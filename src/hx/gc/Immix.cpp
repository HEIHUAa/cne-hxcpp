#include <hxcpp.h>

#include <hx/GC.h>
#include <hx/Memory.h>
#include <hx/Thread.h>
#include "../Hash.h"
#include "GcRegCapture.h"
#include <hx/Unordered.h>
#include <mutex>
#include <condition_variable>
#include <thread>

#ifdef __EMSCRIPTEN__
   #include <emscripten/stack.h>
   #ifdef HXCPP_SINGLE_THREADED_APP
      // Use provided tools to measure stack extent
      #define HXCPP_EXPLICIT_STACK_EXTENT
   #endif
#endif

#include <string>
#include <stdlib.h>
#include <math.h>


#include <stdio.h>
#include <stdarg.h>

static bool sgIsCollecting = false;

// Frame-driven scheduling state.  Only touched from the main thread.
static int    sGcFrameCount = 0;
static int    sGcLastCollectFrame = -1000;
static int    sGcMinCollectFrames = 2;
static size_t sGcLastTickUsage = 0;
static size_t sGcMemAtLastCollect = 0;

// Adaptive pacer.  MMTk's ConcurrentImmix starts concurrent marking once the
// mutator has allocated half of the current heap (total_pages >> 1), and
// MemBalancer sizes the heap from the measured allocation and collection
// rates.  The same feedback loop runs here, so no trigger value has to be
// tuned for a particular scene or content size.
static double sFrameTimeEmaMs = 0;
static double sBestFrameMs = 0;
static double sGcTimeRatioEma = 0;
static double sCycleBeginTime = 0;
static double sLastCycleEndTime = 0;
// Wall time actually spent paused or stepping during the current cycle.  The
// sweep is spread over frames, so the whole cycle duration is not GC time.
static double sStwPauseSeconds = 0;
// Lifetime counters, reported in the low-frequency pacer line so a build
// without per-cycle logging can still tell how often and how long GC ran.
static int    sCycleCount = 0;
static double sCyclePauseTotal = 0;
// Block capacity when the current/most recent incremental cycle started.
// Measuring growth in reserved memory - not in "used since the last GC" -
// keeps the trigger independent of the full collections the application
// requests when it switches states.
static size_t sHeapAtCycleStart = 0;
// Rows handed out by the block allocator since the last cycle began.  This is
// the allocation-path signal MMTk's poll uses ("allocated since last GC").
static size_t sRowsSinceCycle = 0;

// Worst observed duration of each phase of an incremental cycle, reported in
// the low-frequency pacer line.  Maxima matter for perceived hitching; the
// averages hide a single slow phase behind many cheap cycles.
struct GcPhaseTiming
{
   double beginWait, beginSetup, beginRoots, beginAlloc, beginTotal;
   double finishWait, finishDrain, finishRoots, finishMark;
   double finishZombies, finishWeak, finishFinal, finishSweep, finishTotal;
   double cycleMax, cycleSum;
   int    cycles;
   void reset() { memset(this, 0, sizeof(*this)); }
};
static GcPhaseTiming sGcPhases;

static inline void PhaseMax(double &ioMax, double inValue)
{
   if (inValue > ioMax)
      ioMax = inValue;
}

// Per-frame work budget.  5% of the fastest recent frame: a frame that is
// already slow cannot make the collector take even longer, which is the
// feedback loop a current-frame-derived budget would create.
static int GcPacerBudget()
{
   // A zero best-frame means "nothing measured yet"; a measured sub-
   // millisecond frame must not fall back to the 16.7ms default, or
   // high-refresh scenes would get a huge budget.
   double best = sBestFrameMs > 0 ? sBestFrameMs : 16.7;
   int budget = (int)(best * 1000.0 * 0.05);
   if (budget < 100)
      budget = 100;
   if (budget > 1500)
      budget = 1500;
   return budget;
}

// Trigger point for the next cycle, in bytes allocated since the last one.
// Heap-relative, like MMTk's Immix plan.
static size_t GcPacerTrigger(size_t inHeap, size_t inLive)
{
   size_t trigger = inHeap >> 1;
   size_t minTrigger = (inLive >> 2) + (4<<20);
   if (trigger < minTrigger)
      trigger = minTrigger;
   size_t maxTrigger = inLive + (64<<20);
   if (trigger > maxTrigger)
      trigger = maxTrigger;

   return trigger;
}

// Incremental cycle state.  0 = idle, 1 = marking with the mutator running.
static volatile int sgIncrementalActive = 0;

// Usage at the end of the last collection.  MMTk's ConcurrentImmix triggers
// concurrent marking on "used pages since the last GC > half the heap", where
// used pages cover every space.  MemCurrent() is the same signal here: it
// counts the rows the mutator has taken from blocks (one add per block, not
// per object) plus large objects, so the bump path stays free of GC traffic.
static size_t sUsageAtLastCollect = 0;

// Time spent in the per-frame marking steps of the current cycle.
static double sIncrStepTotal = 0;
static int    sIncrStepFrames = 0;

// Start of the incremental sweep, for the sweep timing line.
static double sSweepStartTime = 0;

// Background marking.  Draining the mark stack off the main thread keeps the
// frame time untouched; the main thread only pays the short begin/finish
// pauses.  The worker never allocates haxe objects, so it needs no GC
// registration.
static std::mutex              sgIncrThreadLock;
static std::condition_variable sgIncrThreadCv;
static std::thread            *sgIncrThread = 0;
static bool sgIncrThreadRequest = false;
static bool sgIncrThreadQuit = false;
static bool sgIncrThreadBusy = false;
static bool sgIncrThreadDone = false;

static void IncrMarkThreadProc();

#ifdef HXCPP_GC_AUDIT
static void GCAuditLog(const char *inFormat, ...)
{
   FILE *f = fopen("gc_audit.log","a");
   if (!f)
      return;
   va_list args;
   va_start(args, inFormat);
   vfprintf(f, inFormat, args);
   va_end(args);
   fputc('\n', f);
   fclose(f);
}
#endif

// Timing for the incremental cycle.  GUI builds have no console, so the
// numbers go to a file next to the executable.
static void GCPerfLog(const char *inFormat, ...)
{
   FILE *f = fopen("gc_perf.log","a");
   if (!f)
      return;
   va_list args;
   va_start(args, inFormat);
   vfprintf(f, inFormat, args);
   va_end(args);
   fputc('\n', f);
   fclose(f);
}

// Bisection switches for the concurrent-mutator crash hunt: setting the env
// var to 1 disables one subsystem at a time so the crashing run can be
// narrowed down.  (HXCPP_NO_ASYNC_ZERO / HXCPP_NO_SHRINK / HXCPP_NO_FRAGFINISH)
static bool gcBisectFlag(const char *inName)
{
   const char *v = getenv(inName);
   return v && v[0]=='1';
}

// A single collection can drop thousands of large objects, and free() of the
// big blocks alone cost up to ~25ms in gc_perf.log.  Empty block groups are
// the same story: releasing hundreds of MB through HxFreeGCBlock (VirtualFree)
// took ~37ms inside the pause.  Hand both to a worker so the collection
// itself only pays the queue push.
struct GCDeferredFree { void *ptr; bool isBlock; };
static std::mutex                  sgFreeLock;
static std::condition_variable     sgFreeCv;
static std::vector<GCDeferredFree> sgFreeQueue;
static std::thread                *sgFreeThread = 0;
static bool                        sgFreeQuit = false;

static void GCDeferredFreeThreadProc()
{
   while(true)
   {
      std::vector<GCDeferredFree> batch;
      {
         std::unique_lock<std::mutex> l(sgFreeLock);
         sgFreeCv.wait(l, [](){ return !sgFreeQueue.empty() || sgFreeQuit; });
         if (sgFreeQueue.empty() && sgFreeQuit)
            return;
         batch.swap(sgFreeQueue);
      }
      for(size_t i=0;i<batch.size();i++)
      {
         if (batch[i].isBlock)
            HxFreeGCBlock(batch[i].ptr);
         else
            HxFree(batch[i].ptr);
      }
   }
}

static void QueueGCFree(void *inPtr, bool inIsBlock)
{
   {
      std::lock_guard<std::mutex> l(sgFreeLock);
      GCDeferredFree item;
      item.ptr = inPtr;
      item.isBlock = inIsBlock;
      sgFreeQueue.push_back(item);
   }
   if (!sgFreeThread)
   {
      sgFreeThread = new std::thread(GCDeferredFreeThreadProc);
      sgFreeThread->detach();
   }
   sgFreeCv.notify_one();
}

static void QueueLargeFree(unsigned int *inBlob)
{
   QueueGCFree(inBlob, false);
}

// Block groups are not touched by anything once their GroupInfo.alloc is
// cleared and the block list is rebuilt, so the OS release can happen
// whenever the worker gets to it.
static void QueueBlockGroupFree(void *inGroup)
{
   QueueGCFree(inGroup, true);
}

namespace hx
{
   int gByteMarkID = 0x10;
   int gRememberedByteMarkID = 0x10 | HX_GC_REMEMBERED;
   volatile bool gIncrementalMarking = false;


int gFastPath = 0;
int gSlowPath = 0;


}

using hx::gByteMarkID;
using hx::gRememberedByteMarkID;


namespace hx
{
#ifdef HXCPP_GC_DEBUG_ALWAYS_MOVE

enum { gAlwaysMove = true };
typedef hx::UnorderedSet<void *> PointerMovedSet;
PointerMovedSet sgPointerMoved;

#else
enum { gAlwaysMove = false };
#endif
}

#ifdef ANDROID
#include <android/log.h>
#endif

#ifdef HX_WINDOWS
#include <windows.h>
#endif

#include <vector>
#include <stdio.h>
#ifdef HXCPP_GC_AUDIT
#include <unordered_set>
#include <stdarg.h>
#endif

#include <hx/QuickVec.h>

// #define HXCPP_GC_BIG_BLOCKS


#ifndef __has_builtin
#define __has_builtin(x) 0
#endif
namespace {
void DebuggerTrap()
{
   static bool triggeredOnce = false;

   if (!triggeredOnce)
   {
      triggeredOnce = true;

      #if __has_builtin(__builtin_trap)
      __builtin_trap();
      #else
      *(int *)0=0;
      #endif
   }
}
}




static bool sgAllocInit = 0;
static bool sgInternalEnable = true;
static void *sgObject_root = 0;
// With virtual inheritance, stack pointers can point to the middle of an object
#ifdef _MSC_VER
// MSVC optimizes by taking the address of an initernal data member
static int sgCheckInternalOffset = sizeof(void *)*2;
static int sgCheckInternalOffsetRows = 1;
#else
static int sgCheckInternalOffset = 0;
static int sgCheckInternalOffsetRows = 0;
#endif

int gInAlloc = false;

// This is recalculated from the other parameters
static size_t sWorkingMemorySize = 256*1024;

#ifdef HXCPP_GC_MOVING
// Just not sure what this shold be
static size_t sgMaximumFreeSpace = 1024*1024*1024;
#else
static size_t sgMaximumFreeSpace = 1024 * 1024 * 1024;
#endif


// #define HXCPP_GC_DEBUG_LEVEL 1

#if HXCPP_GC_DEBUG_LEVEL>1
  #define PROFILE_COLLECT
  #if HXCPP_GC_DEBUG_LEVEL>2
     #define SHOW_FRAGMENTATION
     #if HXCPP_GC_DEBUG_LEVEL>3
        #define SHOW_MEM_EVENTS
     #endif
  #endif
#endif

// #define SHOW_FRAGMENTATION_BLOCKS
#if defined SHOW_FRAGMENTATION_BLOCKS
  #define SHOW_FRAGMENTATION
#endif

#define RECYCLE_LARGE

// HXCPP_GC_DYNAMIC_SIZE

//#define HXCPP_GC_SUMMARY
//#define PROFILE_COLLECT
//#define PROFILE_THREAD_USAGE
//#define HXCPP_GC_VERIFY
//#define HX_GC_VERIFY_ALLOC_START
//#define SHOW_MEM_EVENTS
//#define SHOW_MEM_EVENTS_VERBOSE
//#define SHOW_FRAGMENTATION
//
// Setting this can make it easier to reproduce this problem since it takes
//  the timing of the zeroing out of the equation
//#define HX_GC_ZERO_EARLY

// Setting this on windows64 will mean this objects are allocated in the same place,
//  which can make native debugging easier
//#define HX_GC_FIXED_BLOCKS
//
// If the problem happens on the same object, you can print info about the object
//  every collect so you can see where it goes wrong (usually requires HX_GC_FIXED_BLOCKS)
//#define HX_WATCH

#if defined(HXCPP_GC_VERIFY) && defined(HXCPP_GC_GENERATIONAL)
#define HX_GC_VERIFY_GENERATIONAL
#endif


#ifdef HX_WATCH
void *hxWatchList[] = {
  (void *)0x0000000100000200,
  (void *)0
};
bool hxInWatchList(void *watch)
{
   for(void **t = hxWatchList; *t; t++)
      if (*t==watch)
         return true;
   return false;
}
#endif

#ifdef HX_GC_FIXED_BLOCKS
#ifdef HX_WINDOWS
#include <Memoryapi.h>
#endif
#endif

#ifdef PROFILE_COLLECT
   #define HXCPP_GC_SUMMARY
#endif

#ifdef HX_GC_VERIFY_GENERATIONAL
static bool sGcVerifyGenerational = false;
#endif


#if HX_HAS_ATOMIC && (HXCPP_GC_DEBUG_LEVEL==0) && !defined(HXCPP_GC_VERIFY) && !defined(__EMSCRIPTEN__)
  #if defined(HX_MACOS) || defined(HX_WINDOWS) || defined(HX_LINUX)
  enum { MAX_GC_THREADS = 4 };
  #else
  enum { MAX_GC_THREADS = 2 };
  #endif
  
  // You can uncomment this for better call stacks if it crashes while collecting
  #define HX_MULTI_THREAD_MARKING
#else
  enum { MAX_GC_THREADS = 1 };
#endif

#ifdef PROFILE_THREAD_USAGE
static int sThreadMarkCountData[MAX_GC_THREADS+1];
static int sThreadArrayMarkCountData[MAX_GC_THREADS+1];
static int *sThreadMarkCount = sThreadMarkCountData + 1;
static int *sThreadArrayMarkCount = sThreadArrayMarkCountData + 1;
static int sThreadChunkPushCount;
static int sThreadChunkWakes;
static int sSpinCount = 0;
static int sThreadZeroWaits = 0;
static int sThreadZeroPokes = 0;
static int sThreadBlockZeroCount = 0;
static volatile int sThreadZeroMisses = 0;
#endif

enum { MARK_BYTE_MASK = 0x0f };
enum { FULL_MARK_BYTE_MASK = 0x3f };


enum
{
   MEM_INFO_USAGE = 0,
   MEM_INFO_RESERVED = 1,
   MEM_INFO_CURRENT = 2,
   MEM_INFO_LARGE = 3,
};

enum GcMode
{
   gcmFull,
   gcmGenerational,
};

// Start with full gc - since all objects will be new
static GcMode sGcMode = gcmFull;



#ifndef HXCPP_GC_MOVING
  #ifdef HXCPP_GC_DEBUG_ALWAYS_MOVE
  #define HXCPP_GC_MOVING
  #endif
// Enable moving collector...
//#define HXCPP_GC_MOVING
#endif

// Allocate this many blocks at a time - this will increase memory usage % when rounding to block size must be done.
// However, a bigger number makes it harder to release blocks due to pinning
#define IMMIX_BLOCK_GROUP_BITS  5


#ifdef HXCPP_DEBUG
static hx::Object *gCollectTrace = 0;
static bool gCollectTraceDoPrint = false;
static int gCollectTraceCount = 0;
static int sgSpamCollects = 0;
#endif

#if defined(HXCPP_DEBUG) || defined(HXCPP_GC_DEBUG_ALWAYS_MOVE)
volatile int sgAllocsSinceLastSpam = 0;
#endif

#ifdef ANDROID
#define GCLOG(...) __android_log_print(ANDROID_LOG_INFO, "gclog", __VA_ARGS__)
#else
#define GCLOG printf
#endif

// Optional trace for the incremental cycle.  GUI builds have no visible
// stdout, so stage transitions go to a file next to the executable.
#ifdef HXCPP_GC_TRACE
static void GCTrace(const char *inMsg)
{
   static FILE *traceFile = 0;
   if (!traceFile)
   {
      traceFile = fopen("gc_trace.log", "w");
      if (!traceFile)
         return;
   }
   fprintf(traceFile, "%s\n", inMsg);
   fflush(traceFile);
}
#else
#define GCTrace(inMsg)
#endif

#ifdef PROFILE_COLLECT
   #define STAMP(t) double t = __hxcpp_time_stamp();
   #define MEM_STAMP(t) t = __hxcpp_time_stamp();
   static double sLastCollect = __hxcpp_time_stamp();
   static int sObjectMarks =0;
   static int sAllocMarks =0;

#else
   #define STAMP(t)
   #define MEM_STAMP(t)
#endif

#if defined(HXCPP_GC_SUMMARY) || defined(HXCPP_GC_DYNAMIC_SIZE)
struct ProfileCollectSummary
{
   enum { COUNT = 10 };
   double timeWindow[COUNT];
   int    windowIdx;
   double startTime;
   double lastTime;
   double totalCollecting;
   double maxStall;
   double spaceFactor;

   ProfileCollectSummary()
   {
      startTime = __hxcpp_time_stamp();
      lastTime = startTime;
      totalCollecting = 0;
      maxStall = 0;
      windowIdx = 0;
      spaceFactor = 1.0;
      for(int i=0;i<COUNT;i++)
         timeWindow[i] = 0.1;
   }
   ~ProfileCollectSummary()
   {
      #ifdef HXCPP_GC_SUMMARY
      double time = __hxcpp_time_stamp() - startTime;
      GCLOG("Total time     : %.2fms\n", time*1000.0);
      GCLOG("Collecting time: %.2fms\n", totalCollecting*1000.0);
      GCLOG("Max Stall time : %.2fms\n", maxStall*1000.0);
      if (time==0) time = 1;
      GCLOG(" Fraction      : %.2f%%\n",totalCollecting*100.0/time);

      #ifdef HXCPP_GC_DYNAMIC_SIZE
      GCLOG("Space factor   : %.2fx\n",spaceFactor);
      #endif
      #endif
   }

   void addTime(double inCollectStart)
   {
      double now = __hxcpp_time_stamp();
      double dt =  now-inCollectStart;
      if (dt>maxStall)
         maxStall = dt;
      totalCollecting += dt;
      #ifdef HXCPP_GC_DYNAMIC_SIZE
      double wholeTime = now - lastTime;
      if (wholeTime)
      {
         lastTime = now;
         double ratio = dt/wholeTime;
         windowIdx = (windowIdx +1)%COUNT;
         timeWindow[windowIdx] = ratio;
         double sum = 0;
         for(int i=0;i<COUNT;i++)
            sum += timeWindow[i];
         ratio = sum/COUNT;

         if (ratio<0.05)
         {
            if (spaceFactor>1.0)
            {
               spaceFactor -= 0.2;
               if (spaceFactor<1.0)
                  spaceFactor = 1.0;
            }
         }
         else if (ratio>0.12)
         {
            if (ratio>0.2)
               spaceFactor += 0.5;
            else
               spaceFactor += 0.2;

            if (spaceFactor>5.0)
               spaceFactor = 5.0;
         }
      }
      #endif
   }

};

static ProfileCollectSummary profileCollectSummary;
#define PROFILE_COLLECT_SUMMARY_START double collectT0 = __hxcpp_time_stamp();
#define PROFILE_COLLECT_SUMMARY_END profileCollectSummary.addTime(collectT0);

#else
#define PROFILE_COLLECT_SUMMARY_START 
#define PROFILE_COLLECT_SUMMARY_END
#endif



// TODO: Telemetry.h ?
#ifdef HXCPP_TELEMETRY
extern void __hxt_gc_realloc(void* old_obj, void* new_obj, int new_size);
extern void __hxt_gc_start();
extern void __hxt_gc_end();
extern void __hxt_gc_after_mark(int gByteMarkID, int markIdByte);
#endif

static int sgTimeToNextTableUpdate = 1;




std::recursive_mutex *gThreadStateChangeLock=nullptr;
std::mutex *gSpecialObjectLock=nullptr;

class LocalAllocator;
enum LocalAllocState { lasNew, lasRunning, lasStopped, lasWaiting, lasTerminal };


static void MarkLocalAlloc(LocalAllocator *inAlloc,hx::MarkContext *__inCtx);
static void CaptureLocalStack(LocalAllocator *inAlloc, int *inBottom);
#ifdef HXCPP_VISIT_ALLOCS
static void VisitLocalAlloc(LocalAllocator *inAlloc,hx::VisitContext *__inCtx);
#endif
static void WaitForSafe(LocalAllocator *inAlloc);
static void ReleaseFromSafe(LocalAllocator *inAlloc);
static void ClearPooledAlloc(LocalAllocator *inAlloc);
static void CollectFromThisThread(bool inMajor,bool inForceCompact);

namespace hx
{
int gPauseForCollect = 0x00000000;

StackContext *gMainThreadContext = 0;

unsigned int gImmixStartFlag[128];

int gMarkID = 0x10 << 24;
int gMarkIDWithContainer = (0x10 << 24) | IMMIX_ALLOC_IS_CONTAINER;

int gPrevByteMarkID = 0x2f;
unsigned int gPrevMarkIdMask = ((~0x2f000000) & 0x30000000) | HX_GC_CONST_ALLOC_BIT;




void ExitGCFreeZoneLocked();


DECLARE_FAST_TLS_DATA(StackContext, tlsStackContext);

#ifdef HXCPP_SCRIPTABLE
extern void scriptMarkStack(hx::MarkContext *);
#endif
}

//#define DEBUG_ALLOC_PTR ((char *)0xb68354)


#ifdef HX_WINDOWS
#define ZERO_MEM(ptr, n) ZeroMemory(ptr,n)
#else
#define ZERO_MEM(ptr, n) memset(ptr,0,n)
#endif


// ---  Internal GC - IMMIX Implementation ------------------------------



// Some inline implementations ...
// Use macros to allow for mark/move



/*
  IMMIX block size, and various masks for converting addresses

*/

#ifdef HXCPP_GC_BIG_BLOCKS
   #define IMMIX_BLOCK_BITS      16
   typedef unsigned int BlockIdType;
#elif defined(HXCPP_GC_BLOCK_16K)
   #define IMMIX_BLOCK_BITS      14
   typedef unsigned int BlockIdType;
#else
   #define IMMIX_BLOCK_BITS      15
   typedef unsigned short BlockIdType;
#endif

#define IMMIX_BLOCK_SIZE        (1<<IMMIX_BLOCK_BITS)
#define IMMIX_BLOCK_OFFSET_MASK (IMMIX_BLOCK_SIZE-1)
#define IMMIX_BLOCK_BASE_MASK   (~(size_t)(IMMIX_BLOCK_OFFSET_MASK))
#define IMMIX_LINE_COUNT_BITS   (IMMIX_BLOCK_BITS-IMMIX_LINE_BITS)
#define IMMIX_LINES             (1<<IMMIX_LINE_COUNT_BITS)


#if defined(HXCPP_GC_BLOCK_16K)
   #define IMMIX_HEADER_LINES    4
#else
   #define IMMIX_HEADER_LINES    (IMMIX_LINES>>IMMIX_LINE_BITS)
#endif
#define IMMIX_USEFUL_LINES      (IMMIX_LINES - IMMIX_HEADER_LINES)

#define IMMIX_MAX_ALLOC_GROUPS_SIZE  (1<<IMMIX_BLOCK_GROUP_BITS)


// Every second line used
#define MAX_HOLES (IMMIX_USEFUL_LINES>>1)

/*

 IMMIX Alloc Header - 32 bits


 The header is placed in the 4 bytes before the object pointer, and it is placed there using a uint32.
 When addressed as the uint32, you can use the bitmasks below to extract the various data.

 The "mark id" can conveniently be interpreted as a byte, however the offsets well
  be different depending on whether the system is little endian or big endian.


  Little endian - lsb first

 7   0 15 8 23 16 31 24
 -----------------------
 |    |    |     | MID  | obj start here .....
 -----------------------



  Big endian - msb first

 31 24 23 16 15 8 7   0
 -----------------------
 |MID |    |     |      | obj start here .....
 -----------------------

MID = HX_ENDIAN_MARK_ID_BYTE = is measured from the object pointer
      HX_ENDIAN_MARK_ID_BYTE_HEADER = is measured from the header pointer (4 bytes before object)


*/

#define HX_ENDIAN_MARK_ID_BYTE_HEADER (HX_ENDIAN_MARK_ID_BYTE + 4)


// Used by strings
// HX_GC_CONST_ALLOC_BIT  0x80000000

//#define HX_GC_REMEMBERED          0x40000000
#define IMMIX_ALLOC_MARK_ID         0x3f000000
//#define IMMIX_ALLOC_IS_CONTAINER  0x00800000
//#define IMMIX_ALLOC_IS_PINNED     not used at object level
//#define HX_GX_STRING_EXTENDED     0x00200000
//#define HX_GC_STRING_HASH         0x00100000
// size will shift-right IMMIX_ALLOC_SIZE_SHIFT (6).  Low two bits are 0
#define IMMIX_ALLOC_SIZE_MASK       0x000fff00
#define IMMIX_ALLOC_ROW_COUNT       0x000000ff

#define IMMIX_HEADER_PRESERVE       0x00f00000


#define IMMIX_OBJECT_HAS_MOVED 0x000000fe


// Bigger than this, and they go in the large object pool
#define IMMIX_LARGE_OBJ_SIZE 4000

#ifdef allocString
#undef allocString
#endif


void CriticalGCError(const char *inMessage)
{
   // Can't perfrom normal handling because it needs the GC system
   #ifdef ANDROID
   __android_log_print(ANDROID_LOG_ERROR, "HXCPP", "Critical Error: %s", inMessage);
   #elif defined(HX_WINRT)
      WINRT_LOG("HXCPP Critical Error: %s\n", inMessage);
   #else
   printf("Critical Error: %s\n", inMessage);
   #endif

   DebuggerTrap();
}





enum AllocType { allocNone, allocString, allocObject, allocMarked };

struct BlockDataInfo *gBlockStack = 0;
typedef hx::QuickVec<hx::Object *> ObjectStack;

static std::mutex sThreadPoolLock;

// For threaded marking/block reclaiming
static unsigned int sRunningThreads = 0;
static unsigned int sAllThreads = 0;
static bool sLazyThreads = false;
static bool sThreadPoolInit = false;

enum ThreadPoolJob
{
   tpjNone,
   tpjMark,
   tpjReclaim,
   tpjReclaimFull,
   tpjCountRows,
   tpjAsyncZero,
   tpjAsyncZeroJit,
   tpjGetStats,
   tpjVisitBlocks,
   tpjClearRowMarks,
   tpjStackScan,
};

int sgThreadCount = 0;
static ThreadPoolJob sgThreadPoolJob = tpjNone;
static bool sgThreadPoolAbort = false;

// Pthreads enters the sleep state while holding a mutex, so it no cost to update
//  the sleeping state and thereby avoid over-signalling the condition
bool                         sThreadSleeping[MAX_GC_THREADS];
std::condition_variable_any* sThreadWake[MAX_GC_THREADS];
bool                         sThreadJobDoneSleeping = false;
std::condition_variable_any* sThreadJobDone;


static inline void SignalThreadPool(std::condition_variable_any* ioSignal, bool sThreadSleeping)
{
    if (sThreadSleeping)
        ioSignal->notify_one();
}

static void wakeThreadLocked(int inThreadId)
{
   sRunningThreads |= (1<<inThreadId);
   sLazyThreads = sRunningThreads != sAllThreads;
   SignalThreadPool(sThreadWake[inThreadId],sThreadSleeping[inThreadId]);
}

union BlockData
{
   // First 2/4 bytes are not needed for row markers (first 2/4 rows are for flags)
   BlockIdType mId;

   // First 2/4 rows contain a byte-flag-per-row 
   unsigned char  mRowMarked[IMMIX_LINES];
   // Row data as union - don't use first 2/4 rows
   unsigned char  mRow[IMMIX_LINES][IMMIX_LINE_LEN];

};

struct BlockDataStats
{
   void clear() { ZERO_MEM(this, sizeof(BlockDataStats)); }
   void add(const BlockDataStats &inOther)
   {
      rowsInUse += inOther.rowsInUse;
      bytesInUse += inOther.bytesInUse;
      emptyBlocks += inOther.emptyBlocks;
      fraggedBlocks += inOther.fraggedBlocks;
      fragScore += inOther.fragScore;
      fraggedRows += inOther.fraggedRows;
   }

   int rowsInUse;
   size_t bytesInUse;
   int emptyBlocks;
   int fragScore;
   int fraggedBlocks;
   int fraggedRows;
};

static BlockDataStats sThreadBlockDataStats[MAX_GC_THREADS];
#ifdef HXCPP_VISIT_ALLOCS
static hx::VisitContext *sThreadVisitContext = 0;
#endif
   


namespace hx { void MarkerReleaseWorkerLocked(); }




struct GroupInfo
{
   int  blocks;
   char *alloc;

   bool pinned;
   bool isEmpty;
   int  usedBytes;
   int  usedSpace;

   void clear()
   {
      pinned = false;
      usedBytes = 0;
      usedSpace = 0;
      isEmpty = true;
   }
   int getMoveScore()
   {
      return pinned ?  0 : usedSpace-usedBytes;
   }

};
 
hx::QuickVec<GroupInfo> gAllocGroups;



struct HoleRange
{
   unsigned short start;
   unsigned short length;
};


hx::QuickVec<struct BlockDataInfo *> *gBlockInfo = 0;
static int gBlockInfoEmptySlots = 0;

#define FRAG_THRESH 14

#define ZEROED_NOT    0
#define ZEROED_THREAD 1
#define ZEROED_AUTO   2

// Align padding based on block offset
#ifdef HXCPP_ALIGN_ALLOC
    #define ALIGN_PADDING(x) (4-(x&4))
#else
    #define ALIGN_PADDING(x) 0
#endif

struct BlockDataInfo
{
   int             mId;
   int             mGroupId;
   BlockData       *mPtr;

   unsigned int allocStart[IMMIX_LINES];

   HoleRange    mRanges[MAX_HOLES];
   int          mHoles;

   int          mUsedRows;
   int          mMaxHoleSize;
   int          mMoveScore;
   int          mUsedBytes;
   int          mFraggedRows;
   bool         mPinned;
   unsigned char mZeroed;
   bool         mReclaimed;
   bool         mOwned;
   #ifdef HXCPP_GC_GENERATIONAL
   bool         mHasSurvivor;
   #endif
   volatile int mZeroLock;


   BlockDataInfo(int inGid, BlockData *inData)
   {
      if (gBlockInfoEmptySlots)
      {
         for(int i=0;i<gBlockInfo->size();i++)
            if ( !(*gBlockInfo)[i] )
            {
               gBlockInfoEmptySlots--;
               mId = i;
               (*gBlockInfo)[i] = this;
               break;
            }
      }
      else
      {
         if (gBlockInfo==0)
            gBlockInfo = new hx::QuickVec<BlockDataInfo *>;
         mId = gBlockInfo->size();
         gBlockInfo->push( this );
      }


      mZeroLock = 0;
      mOwned = false;
      mGroupId = inGid;
      mPtr     = inData;
      inData->mId = mId;
      #ifdef SHOW_MEM_EVENTS
      //GCLOG("  create block %d : %p -> %p\n",  mId, this, mPtr );
      #endif
      clear();
   }

   void clear()
   {
      mUsedRows = 0;
      mUsedBytes = 0;
      mFraggedRows = 0;
      mPinned = false;
      ZERO_MEM(allocStart,sizeof(int)*IMMIX_LINES);
      ZERO_MEM(mPtr->mRowMarked+IMMIX_HEADER_LINES, IMMIX_USEFUL_LINES); 
      mRanges[0].start = IMMIX_HEADER_LINES << IMMIX_LINE_BITS;
      mRanges[0].length = IMMIX_USEFUL_LINES << IMMIX_LINE_BITS;
      mMaxHoleSize = mRanges[0].length;
      mMoveScore = 0;
      mHoles = 1;
      mZeroed = ZEROED_NOT;
      mReclaimed = true;
      mZeroLock = 0;
      mOwned = false;
   }

   void makeFull()
   {
      mUsedRows = IMMIX_USEFUL_LINES;
      mUsedBytes = mUsedRows<<IMMIX_LINE_BITS;
      mFraggedRows = 0;
      memset(mPtr->mRowMarked+IMMIX_HEADER_LINES, 1,IMMIX_USEFUL_LINES); 
      mRanges[0].start = 0;
      mRanges[0].length = 0;
      mMaxHoleSize = 0;
      mMoveScore = 0;
      mHoles = 0;
      mZeroed = ZEROED_AUTO;
      mReclaimed = true;
      mZeroLock = 0;
      mOwned = false;
   }


   void clearBlockMarks()
   {
      mPinned = false;
      #ifdef HXCPP_GC_GENERATIONAL
      mHasSurvivor = false;
      #endif
   }

   void clearRowMarks()
   {
      clearBlockMarks();
      ZERO_MEM((char *)mPtr+IMMIX_HEADER_LINES, IMMIX_USEFUL_LINES);
   }

   inline int GetFreeRows() const { return (IMMIX_USEFUL_LINES - mUsedRows); }
   inline int GetFreeData() const { return (IMMIX_USEFUL_LINES - mUsedRows)<<IMMIX_LINE_BITS; }


   bool zeroAndUnlock()
   {
      bool doZero = !mZeroed;
      if (doZero)
      {
         if (!mReclaimed)
            reclaim<false>(0);

         for(int i=0;i<mHoles;i++)
             ZERO_MEM( (char *)mPtr+mRanges[i].start, mRanges[i].length );
         mZeroed = ZEROED_THREAD;
      }
      mZeroLock = 0;
      return doZero;
   }

   bool tryZero()
   {
      if (mZeroed)
         return false;

      if (_hx_atomic_compare_exchange(&mZeroLock, 0,1) == 0)
         return zeroAndUnlock();

      return false;
   }

   void destroy()
   {
      #ifdef SHOW_MEM_EVENTS_VERBOSE
      GCLOG("  release block %d : %p\n",  mId, this );
      #endif
      (*gBlockInfo)[mId] = 0;
      gBlockInfoEmptySlots++;
      delete this;
   }

   bool isEmpty() const { return mUsedRows == 0; }
   int getUsedRows() const { return mUsedRows; }

   void getStats(BlockDataStats &outStats)
   {
      outStats.rowsInUse += mUsedRows;
      outStats.bytesInUse += mUsedBytes;
      outStats.fraggedRows += mFraggedRows;
      //outStats.bytesInUse += 0;
      outStats.fragScore += mPinned ? (mMoveScore>0?1:0) : mMoveScore;

      if (mUsedRows==0)
         outStats.emptyBlocks++;
      if (mMoveScore> FRAG_THRESH )
         outStats.fraggedBlocks++;
   }

   #ifdef HX_GC_VERIFY_ALLOC_START
   void verifyAllocStart()
   {
      unsigned char *rowMarked = mPtr->mRowMarked;

      for(int r = IMMIX_HEADER_LINES; r<IMMIX_LINES; r++)
      {
         if (!rowMarked[r] && allocStart[r])
         {
            printf("allocStart set without marking\n");
            DebuggerTrap();
         }
      }
   }
   #endif

   void countRows(BlockDataStats &outStats)
   {
      unsigned char *rowMarked = mPtr->mRowMarked;
      unsigned int *rowTotals = ((unsigned int *)rowMarked) + 1;

      // TODO - sse/neon
      #ifdef HXCPP_GC_BIG_BLOCKS
      unsigned int total = 0;
      #else
      unsigned int total = rowMarked[2] + rowMarked[3];
      #endif

      total +=
       rowTotals[0]  + rowTotals[1]  + rowTotals[2]  + rowTotals[3]  + rowTotals[4] +
       rowTotals[5]  + rowTotals[6]  + rowTotals[7]  + rowTotals[8]  + rowTotals[9] +
       rowTotals[10] + rowTotals[11] + rowTotals[12] + rowTotals[13] + rowTotals[14] +
       rowTotals[15] + rowTotals[16] + rowTotals[17] + rowTotals[18] + rowTotals[19] +
       rowTotals[20] + rowTotals[21] + rowTotals[22] + rowTotals[23] + rowTotals[24] +
       rowTotals[25] + rowTotals[26] + rowTotals[27] + rowTotals[28] + rowTotals[29] +
       rowTotals[30] + rowTotals[31] + rowTotals[32] + rowTotals[33] + rowTotals[34] +
       rowTotals[35] + rowTotals[36] + rowTotals[37] + rowTotals[38] + rowTotals[39] +
       rowTotals[40] + rowTotals[41] + rowTotals[42] + rowTotals[43] + rowTotals[44] +
       rowTotals[45] + rowTotals[46] + rowTotals[47] + rowTotals[48] + rowTotals[49] +
       rowTotals[50] + rowTotals[51] + rowTotals[52] + rowTotals[53] + rowTotals[54] +
       rowTotals[55] + rowTotals[56] + rowTotals[57] + rowTotals[58] + rowTotals[59] +
       rowTotals[60] + rowTotals[61] + rowTotals[62];


      #ifdef HXCPP_GC_BIG_BLOCKS
      rowTotals += 63;
      total +=
       rowTotals[0]  + rowTotals[1]  + rowTotals[2]  + rowTotals[3]  + rowTotals[4] +
       rowTotals[5]  + rowTotals[6]  + rowTotals[7]  + rowTotals[8]  + rowTotals[9] +
       rowTotals[10] + rowTotals[11] + rowTotals[12] + rowTotals[13] + rowTotals[14] +
       rowTotals[15] + rowTotals[16] + rowTotals[17] + rowTotals[18] + rowTotals[19] +
       rowTotals[20] + rowTotals[21] + rowTotals[22] + rowTotals[23] + rowTotals[24] +
       rowTotals[25] + rowTotals[26] + rowTotals[27] + rowTotals[28] + rowTotals[29] +
       rowTotals[30] + rowTotals[31] + rowTotals[32] + rowTotals[33] + rowTotals[34] +
       rowTotals[35] + rowTotals[36] + rowTotals[37] + rowTotals[38] + rowTotals[39] +
       rowTotals[40] + rowTotals[41] + rowTotals[42] + rowTotals[43] + rowTotals[44] +
       rowTotals[45] + rowTotals[46] + rowTotals[47] + rowTotals[48] + rowTotals[49] +
       rowTotals[50] + rowTotals[51] + rowTotals[52] + rowTotals[53] + rowTotals[54] +
       rowTotals[55] + rowTotals[56] + rowTotals[57] + rowTotals[58] + rowTotals[59] +
       rowTotals[60] + rowTotals[61] + rowTotals[62] + rowTotals[63];

      #endif

      mUsedRows = (total & 0xff) + ((total>>8) & 0xff) + ((total>>16)&0xff) + ((total>>24)&0xff);
      mUsedBytes = mUsedRows<<IMMIX_LINE_BITS;

      mZeroLock = 0;
      mOwned = false;
      outStats.rowsInUse += mUsedRows;
      outStats.bytesInUse += mUsedBytes;
      outStats.fraggedRows += mFraggedRows;
      mFraggedRows = 0;
      mHoles = 0;

      if (mUsedRows==IMMIX_USEFUL_LINES)
      {
         // All rows used - write the block off
         mMoveScore = 0;
         mZeroed = ZEROED_AUTO;
         mReclaimed = true;
      }
      else
      {
         mZeroed = ZEROED_NOT;
         mReclaimed = false;
      }

      int left = (IMMIX_USEFUL_LINES - mUsedRows) << IMMIX_LINE_BITS;
      if (left<mMaxHoleSize)
         mMaxHoleSize = left;
   }

   template<bool FULL>
   void reclaim(BlockDataStats *outStats)
   {
      HoleRange *ranges = mRanges;
      ranges[0].length = 0;
      mZeroed = ZEROED_NOT;
      int usedBytes = 0;

      unsigned char *rowMarked = mPtr->mRowMarked;

      int r = IMMIX_HEADER_LINES;
      // Count unused rows ....
     
      // start on 4-byte boundary...
      #ifdef HXCPP_ALIGN_ALLOC
      while(r<4 && rowMarked[r]==0)
         r++;
      if (!rowMarked[r])
      #endif
      {
         while(r<(IMMIX_LINES-4) && *(int *)(rowMarked+r)==0 )
            r += 4;
         while(r<(IMMIX_LINES) && rowMarked[r]==0)
            r++;
      }

      if (r==IMMIX_LINES)
      {
         ranges[0].start  = IMMIX_HEADER_LINES<<IMMIX_LINE_BITS;
         ranges[0].length = (IMMIX_USEFUL_LINES)<<IMMIX_LINE_BITS;
         mMaxHoleSize = (IMMIX_USEFUL_LINES)<<IMMIX_LINE_BITS;
         mUsedRows = 0;
         mHoles = 1;
         mMoveScore = 0;
         ZERO_MEM(allocStart+IMMIX_HEADER_LINES, IMMIX_USEFUL_LINES*sizeof(int));
      }
      else
      {
         int hole = 0;

         if (r>IMMIX_HEADER_LINES)
         {
            ranges[hole].start  = IMMIX_HEADER_LINES;
            ranges[hole].length = r-IMMIX_HEADER_LINES;
            hole++;
         }

         while(r<IMMIX_LINES)
         {
            if (rowMarked[r])
            {
               if (FULL)
               {
                  unsigned int &starts = allocStart[r];
                  if (starts)
                  {
                     unsigned int *headerPtr = ((unsigned int *)mPtr->mRow[r]);
                     #define CHECK_FLAG(i,byteMask) \
                     { \
                        unsigned int mask = 1<<i; \
                        if ( starts & mask ) \
                        { \
                           unsigned int header = headerPtr[i]; \
                           if ( (header & IMMIX_ALLOC_MARK_ID) != hx::gMarkID ) \
                           { \
                              starts ^= mask; \
                              if (!(starts & byteMask)) \
                                 break; \
                           } \
                           else \
                              usedBytes += sizeof(int) + ((header & IMMIX_ALLOC_SIZE_MASK) >> IMMIX_ALLOC_SIZE_SHIFT); \
                        } \
                     }

                     if (starts & 0x000000ff)
                        for(int i=0;i<8;i++)
                           CHECK_FLAG(i,0x000000ff);

                     if (starts & 0x0000ff00)
                        for(int i=8;i<16;i++)
                           CHECK_FLAG(i,0x0000ff00);

                     if (starts & 0x00ff0000)
                        for(int i=16;i<24;i++)
                           CHECK_FLAG(i,0x00ff0000);

                     if (starts & 0xff000000)
                        for(int i=24;i<32;i++)
                           CHECK_FLAG(i,0xff000000);
                  }
               }
               r++;
            }
            else
            {
               int start = r;
               ranges[hole].start = start;

               #ifdef HXCPP_ALIGN_ALLOC
               int alignR = (r+3) & ~3;
               while(r<alignR && rowMarked[r]==0)
                  r++;
               if (!rowMarked[r])
               #endif
               {
                  while(r<(IMMIX_LINES-4) && *(int *)(rowMarked+r)==0 )
                     r += 4;
                  while(r<(IMMIX_LINES) && rowMarked[r]==0)
                     r++;
               }
               ranges[hole].length = r-start;
               hole++;
            }
         }


         int freeLines = 0;
         // Convert hole rows to hole bytes...
         mMaxHoleSize = 0;
         for(int h=0;h<hole;h++)
         {
            int s = ranges->start;
            int l = ranges->length;
            freeLines += l;
            ZERO_MEM(allocStart+s, l*sizeof(int));

            int sBytes = s<<IMMIX_LINE_BITS;
            ranges->start = sBytes;

            int lBytes = l<<IMMIX_LINE_BITS;
            ranges->length = lBytes;

            if (lBytes>mMaxHoleSize)
              mMaxHoleSize = lBytes;

            ranges++;
         }
         mUsedRows = IMMIX_USEFUL_LINES - freeLines;
         mHoles = hole;
      }

      mUsedBytes =  FULL ? usedBytes : (mUsedRows<<IMMIX_LINE_BITS);
      mMoveScore = calcFragScore();
      mReclaimed = true;

      if (outStats)
      {
         outStats->rowsInUse += mUsedRows;
         outStats->bytesInUse += mUsedBytes;
         outStats->fragScore += mMoveScore;
         outStats->fraggedRows += mFraggedRows;

         if (mUsedRows==0)
            outStats->emptyBlocks++;
         if (mMoveScore> FRAG_THRESH )
            outStats->fraggedBlocks++;
      }

      mFraggedRows = 0;
   }

   int calcFragScore()
   {
      return mPinned ? 0 : (mHoles>3 ? mHoles-3 : 0) + 8 * (mUsedRows<<IMMIX_LINE_BITS) / (mUsedBytes+IMMIX_LINE_LEN);
   }


   // When known to be an actual object start...
   AllocType GetAllocTypeChecked(int inOffset, bool allowPrevious)
   {
      char time = mPtr->mRow[0][inOffset+HX_ENDIAN_MARK_ID_BYTE_HEADER];
      if ( ((time+1) & MARK_BYTE_MASK) != (gByteMarkID & MARK_BYTE_MASK)  )
      {
         // Object is either out-of-date, or already marked....
         return time==gByteMarkID ? allocMarked : allocNone;
      }

      if (!allowPrevious)
         return allocNone;

      if (*(unsigned int *)(mPtr->mRow[0] + inOffset) & IMMIX_ALLOC_IS_CONTAINER)
      {
         // See if object::new has been called, but not constructed yet ...
         void **vtable = (void **)(mPtr->mRow[0] + inOffset + sizeof(int));
         if (vtable[0]==0)
         {
            // GCLOG("Partially constructed object.");
            return allocString;
         }
         return allocObject;
      }

      return allocString;
   }

   #ifdef HXCPP_GC_NURSERY
   AllocType GetEnclosingNurseryType(int inOffset, void **outPtr)
   {
      // The block did not get used in the previous cycle, so allocStart is invalid and
      //  no new objects should be in here
      if (!mZeroed)
         return allocNone;
      // For the nursery(generational) case, the allocStart markers are not set
      // So trace tne new object links through the new allocation holes
      for(int h=0;h<mHoles;h++)
      {
         int scan = mRanges[h].start;
         if (inOffset<scan)
            break;

         int size = 0;
         int last = scan + mRanges[h].length;
         if (inOffset<last)
         {
            #ifdef HXCPP_ALIGN_ALLOC
            // Make sure header scan is odd-int aligned so the following object will be even-int
            // aligned
            if (!(scan & 0x4))
               scan += 4;
            #endif

            // Found hole that the object was possibly allocated in
            while(scan<=inOffset)
            {
               // Trace along the hole...
               unsigned int header = *(unsigned int *)(mPtr->mRow[0]+scan);
               if (!(header & 0xff000000))
                  size = header & 0x0000ffff;
               else
                  size = (header & IMMIX_ALLOC_SIZE_MASK) >> IMMIX_ALLOC_SIZE_SHIFT;

               int end = scan+size+sizeof(int);
               if (!size || end > last)
                  return allocNone;

               if (inOffset>=scan && inOffset<end)
               {
                  if (inOffset>scan+sgCheckInternalOffset)
                     return allocNone;

                  *outPtr = mPtr->mRow[0] + scan + sizeof(int);

                  if (header & IMMIX_ALLOC_IS_CONTAINER)
                  {
                     // See if object::new has been called, but not constructed yet ...
                     void **vtable = (void **)(mPtr->mRow[0] + scan + sizeof(int));
                     if (vtable[0]==0)
                     {
                        // GCLOG("Partially constructed object.");
                        return allocString;
                     }
                     return allocObject;
                  }
                  return allocString;
               }
               scan = end;
               #ifdef HXCPP_ALIGN_ALLOC
               // Make sure scan is odd-int aligned so the following object will be even-int
               // aligned
               if (!(scan & 0x4))
                  scan += 4;
               #endif
            }
            break;
         }
      }
      return allocNone;
}
   #endif

   AllocType GetAllocType(int inOffset,bool inAllowPrevious)
   {
      // Row that the header would be on
      int r = inOffset >> IMMIX_LINE_BITS;

      // Out of bounds - can't be a new object start
      if (r < IMMIX_HEADER_LINES || r >= IMMIX_LINES)
      {
         return allocNone;
      }

      // Does a live object start on this row
      if ( !( allocStart[r] & hx::gImmixStartFlag[inOffset &127]) )
      {
         #ifdef HXCPP_GC_NURSERY
         void *ptr;
         return GetEnclosingNurseryType(inOffset,&ptr);
         #endif
         //Not a actual start...
         return allocNone;
      }

      return GetAllocTypeChecked(inOffset,inAllowPrevious);
   }

   AllocType GetEnclosingAllocType(int inOffset,void **outPtr,bool inAllowPrevious)
   {
      for(int dx=0;dx<=sgCheckInternalOffset;dx+=4)
      {
         int blockOffset = inOffset - dx;
         if (blockOffset >= 0)
         {
            int r = blockOffset >> IMMIX_LINE_BITS;
            if (r >= IMMIX_HEADER_LINES && r < IMMIX_LINES)
            {
               // Normal, good alloc
               int rowPos = hx::gImmixStartFlag[blockOffset &127];
               if ( allocStart[r] & rowPos )
               {
                  // Found last valid object - is it big enough?
                  unsigned int header =  *(unsigned int *)((char *)mPtr + blockOffset);
                  int size = (header & IMMIX_ALLOC_SIZE_MASK) >> IMMIX_ALLOC_SIZE_SHIFT;
                  // Valid object not big enough...
                  if (blockOffset + size +sizeof(int) <= inOffset )
                     break;

                  // If the object is old, it could be the tail end of an old row that
                  //  thinks is is covering this row, but it is not because this row is reused.
                  // So we can say there is no other object that could be covering
                  //  this spot, but not that it is not a nursery object.
                  AllocType result = GetAllocTypeChecked(blockOffset,inAllowPrevious);
                  if (result!=allocNone)
                  {
                     *outPtr = (void *)(mPtr->mRow[0] + blockOffset + sizeof(int));
                     return result;
                  }
                  break;
               }
            }
          }
      }

      #ifdef HXCPP_GC_NURSERY
      return GetEnclosingNurseryType(inOffset,outPtr);
      #endif
      // Not a actual start...
      return allocNone;
   }


   void pin() { mPinned = true; }


   #ifdef HXCPP_VISIT_ALLOCS
   void VisitBlock(hx::VisitContext *inCtx)
   {
      if (isEmpty())
         return;

      unsigned char *rowMarked = mPtr->mRowMarked;
      for(int r=IMMIX_HEADER_LINES;r<IMMIX_LINES;r++)
      {
         if (rowMarked[r])
         {
            unsigned int starts = allocStart[r];
            if (!starts)
               continue;
            unsigned char *row = mPtr->mRow[r];
            for(int i=0;i<32;i++)
            {
               int pos = i<<2;
               if ( (starts & (1<<i)) &&
                   (row[pos+HX_ENDIAN_MARK_ID_BYTE_HEADER]&FULL_MARK_BYTE_MASK) == gByteMarkID)
                  {
                     if ( (*(unsigned int *)(row+pos)) & IMMIX_ALLOC_IS_CONTAINER )
                     {
                        hx::Object *obj = (hx::Object *)(row+pos+4);
                        // May be partially constructed
                        if (*(void **)obj)
                           obj->__Visit(inCtx);
                     }
                  }
            }
         }
      }
   }
   #endif

   #ifdef HXCPP_GC_VERIFY
   void verify(const char *inWhere)
   {
      for(int i=IMMIX_HEADER_LINES;i<IMMIX_LINES;i++)
      {
         for(int j=0;j<32;j++)
            if (allocStart[i] & (1<<j))
            {
               unsigned int header = *(unsigned int *)( (char *)mPtr + i*IMMIX_LINE_LEN + j*4 );
               if ((header & IMMIX_ALLOC_MARK_ID) == hx::gMarkID )
               {
                  int rows = header & IMMIX_ALLOC_ROW_COUNT;
                  if (rows==0)
                  {
                     printf("BAD ROW0 %s\n", inWhere);
                     DebuggerTrap();
                  }
                  for(int r=0;r<rows;r++)
                     if (!mPtr->mRowMarked[r+i])
                     {
                        printf("Unmarked row %dx %d/%d %s, t=%d!\n", i, r, rows, inWhere,sgTimeToNextTableUpdate);
                        DebuggerTrap();
                     }
               }
            }
         }

   }
   #endif
};





bool MostUsedFirst(BlockDataInfo *inA, BlockDataInfo *inB)
{
   return inA->getUsedRows() > inB->getUsedRows();
}

bool BiggestFreeFirst(BlockDataInfo *inA, BlockDataInfo *inB)
{
   return inA->mMaxHoleSize > inB->mMaxHoleSize;
}
bool SmallestFreeFirst(BlockDataInfo *inA, BlockDataInfo *inB)
{
   return inA->mMaxHoleSize < inB->mMaxHoleSize;
}


bool LeastUsedFirst(BlockDataInfo *inA, BlockDataInfo *inB)
{
   return inA->getUsedRows() < inB->getUsedRows();
}



bool SortMoveOrder(BlockDataInfo *inA, BlockDataInfo *inB)
{
   return inA->mMoveScore > inB->mMoveScore;
}


namespace hx
{



void BadImmixAlloc()
{

   #ifdef HX_WINRT
   WINRT_LOG("Bad local allocator - requesting memory from unregistered thread!");
   #else
   #ifdef ANDROID
   __android_log_print(ANDROID_LOG_ERROR, "hxcpp",
   #else
   fprintf(stderr,
   #endif

   "Bad local allocator - requesting memory from unregistered thread!"

   #ifdef ANDROID
   );
   #else
   );
   #endif
   #endif

   DebuggerTrap();
}



void GCCheckPointer(void *inPtr)
{
   #ifdef HXCPP_GC_DEBUG_ALWAYS_MOVE
   if (hx::sgPointerMoved.find(inPtr)!=hx::sgPointerMoved.end())
   {
      GCLOG("Accessing moved pointer %p\n", inPtr);
      DebuggerTrap();
   }
   #endif

   unsigned char&mark = ((unsigned char *)inPtr)[HX_ENDIAN_MARK_ID_BYTE];
   #ifdef HXCPP_GC_NURSERY
   if (mark)
   #endif
   if ( !(mark & HX_GC_CONST_ALLOC_MARK_BIT) && (mark&FULL_MARK_BYTE_MASK)!=gByteMarkID  )
   {
      GCLOG("Old object access %p\n", inPtr);
      NullReference("Object", false);
   }
}


void GCOnNewPointer(void *inPtr)
{
   #ifdef HXCPP_ALIGN_ALLOC
   if ( (size_t)inPtr & 0x7 )
   {
      GCLOG("Misaligned pointer %p\n", inPtr);
      NullReference("Object", false);
   }
   #endif

   #ifdef HXCPP_GC_DEBUG_ALWAYS_MOVE
   hx::sgPointerMoved.erase(inPtr);
   _hx_atomic_add(&sgAllocsSinceLastSpam, 1);
   #endif
}

// --- Marking ------------------------------------

struct MarkInfo
{
   const char *mClass;
   const char *mMember;
};

struct GlobalChunks
{
   volatile MarkChunk *processList;
   volatile int       processListPopLock;
   volatile MarkChunk *freeList;
   volatile int       freeListPopLock;

   GlobalChunks()
   {
      processList = 0;
      freeList = 0;
      freeListPopLock = 0;
      processListPopLock = 0;
   }

   // Diagnostics: work that survived a "drain the world" point means a
   // marking thread dropped it (split-job race) - the entries never get
   // marked, the sweep frees them and the owner is left with dangling
   // pointers.  Checked after every STW drain.
   int pendingJobs()
   {
      int n = 0;
      for(MarkChunk *c = (MarkChunk *)processList; c; c = c->next)
         n++;
      return n;
   }

   MarkChunk *pushJobNoWake(MarkChunk *inChunk)
   {
      while(true)
      {
         MarkChunk *head = (MarkChunk *)processList;
         inChunk->next = head;
         if (_hx_atomic_compare_exchange_cast_ptr(&processList, head, inChunk) == head)
            break;
      }

      return alloc();
   }

   MarkChunk *pushJob(MarkChunk *inChunk,bool inAndAlloc)
   {
      while(true)
      {
         MarkChunk *head = (MarkChunk *)processList;
         inChunk->next = head;
         if (_hx_atomic_compare_exchange_cast_ptr(&processList, head, inChunk) == head)
            break;
      }

      #ifdef PROFILE_THREAD_USAGE
      _hx_atomic_add(&sThreadChunkPushCount, 1);
      #endif

      // Wake check runs unconditionally (a stale sLazyThreads here would miss
      // a thread that just completed, orphaning this job - see the final
      // processList re-check in popJobOrFinish).  Waking when nobody sleeps
      // is a cheap no-op: SignalThreadPool only notifies sleepers.
      if (MAX_GC_THREADS>1)
      {
         std::lock_guard<std::mutex> l(sThreadPoolLock);

         #ifdef PROFILE_THREAD_USAGE
           #define CHECK_THREAD_WAKE(tid) \
            if (MAX_GC_THREADS >tid && sgThreadCount>tid && (!(sRunningThreads & (1<<tid)))) { \
            wakeThreadLocked(tid); \
            sThreadChunkWakes++; \
           } 
         #else
           #define CHECK_THREAD_WAKE(tid)  \
            if (MAX_GC_THREADS >tid && sgThreadCount>tid && (!(sRunningThreads & (1<<tid)))) { \
            wakeThreadLocked(tid); \
           }
         #endif


         CHECK_THREAD_WAKE(0)
         else CHECK_THREAD_WAKE(1)
         else CHECK_THREAD_WAKE(2)
         else CHECK_THREAD_WAKE(3)
         else CHECK_THREAD_WAKE(4)
         else CHECK_THREAD_WAKE(5)
         else CHECK_THREAD_WAKE(6)
         else CHECK_THREAD_WAKE(7)
      }

      if (inAndAlloc)
         return alloc();
      return 0;
   }

   void addLocked(MarkChunk *inChunk)
   {
      inChunk->next = (MarkChunk *)processList;
      processList = (volatile MarkChunk *)inChunk;
   }

   void copyPointers( QuickVec<hx::Object *> &outPointers,bool andFree=false)
   {
      int size = 0;
      for(MarkChunk *c =(MarkChunk *)processList; c; c=c->next )
         size += c->count;

      outPointers.setSize(size);
      int idx = 0;
      if (andFree)
      {
         while(processList)
         {
            MarkChunk *c = (MarkChunk *)processList;
            processList = c->next;

            for(int i=0;i<c->count;i++)
               outPointers[idx++] = c->stack[i];
            c->count = 0;
            c->next = (MarkChunk *)freeList;
            freeList = c;
         }
      }
      else
      {
         for(MarkChunk *c = (MarkChunk *)processList; c; c=c->next )
         {
            for(int i=0;i<c->count;i++)
               outPointers[idx++] = c->stack[i];
         }
      }
   }

   int takeArrayJob(hx::Object **inPtr, int inLen)
   {
      if (sLazyThreads)
      {
         int n = (inLen/2) & ~15;

         if (n)
         {
            MarkChunk *chunk = alloc();
            chunk->count = MarkChunk::OBJ_ARRAY_JOB;
            chunk->arrayBase = inPtr;
            chunk->arrayElements = n;

            pushJob(chunk,false);
         }

         // Return how many to skip
         return n;
      }

      return 0;
   }

   inline void release(MarkChunk *inChunk)
   {
      while(true)
      {
         MarkChunk *head = (MarkChunk *)freeList;
         inChunk->next = head;
         if (_hx_atomic_compare_exchange_cast_ptr(&freeList, head, inChunk) == head)
            return;
      }
   }


   MarkChunk *popJobLocked(MarkChunk *inChunk)
   {
      if (inChunk)
         release(inChunk);

      while(_hx_atomic_compare_exchange(&processListPopLock, 0, 1) != 0)
      {
         // Spin
         #ifdef PROFILE_THREAD_USAGE
         _hx_atomic_add(&sSpinCount, 1);
         #endif
      }

      while(true)
      {
         MarkChunk *head = (MarkChunk *)processList;
         if (!head)
         {
            processListPopLock = 0;
            return 0;
         }
         MarkChunk *next = head->next;
         if (_hx_atomic_compare_exchange_cast_ptr(&processList, head, next) == head)
         {
            processListPopLock = 0;

            head->next = 0;
            return head;
         }
      }
      return 0;
   }


   void completeThreadLocked(int inThreadId)
   {
      if (!(sRunningThreads & (1<<inThreadId)))
      {
         printf("Complete non-running thread?\n");
         DebuggerTrap();
      }
      sRunningThreads &= ~(1<<inThreadId);
      sLazyThreads = sRunningThreads != sAllThreads;

      if (!sRunningThreads)
         SignalThreadPool(sThreadJobDone,sThreadJobDoneSleeping);
   }


   // Optionally returns inChunk to empty pool (while we have the lock),
   //  and returns a new job if there is one
   MarkChunk *popJobOrFinish(MarkChunk *inChunk,int inThreadId)
   {
      #ifdef HX_MULTI_THREAD_MARKING
      if (sAllThreads)
      {
         MarkChunk *result =  popJobLocked(inChunk);
         if (!result)
         {
            for(int spinCount = 0; spinCount<10000; spinCount++)
            {
               if ( sgThreadPoolAbort || sAllThreads == (1<<inThreadId) )
                  break;
               if (processList)
               {
                  result =  popJobLocked(0);
                  if (result)
                     return result;
               }
            }
            std::lock_guard<std::mutex> l(sThreadPoolLock);
            // Last chance before completing: a worker may have pushed a split
            // job (takeArrayJob) between the unlocked spin check and this
            // lock.  Taking the job here keeps it from being orphaned - an
            // unprocessed range means unmarked objects, which the next sweep
            // frees while the owning array keeps the dangling pointers.
            if (processList && !sgThreadPoolAbort)
            {
               result = popJobLocked(0);
               if (result)
                  return result;
            }
            completeThreadLocked(inThreadId);
         }
         return result;
      }
      #endif

      return popJobLocked(inChunk);
   }


   void free(MarkChunk *inChunk)
   {
      release(inChunk);
   }

   inline MarkChunk *alloc()
   {
      while(_hx_atomic_compare_exchange(&freeListPopLock, 0, 1) != 0)
      {
         // Spin
         #ifdef PROFILE_THREAD_USAGE
         _hx_atomic_add(&sSpinCount, 1);
         #endif
      }

      while(true)
      {
         MarkChunk *head = (MarkChunk *)freeList;
         if (!head)
         {
            freeListPopLock = 0;
            return new MarkChunk;
         }
         MarkChunk *next = head->next;
         if (_hx_atomic_compare_exchange_cast_ptr(&freeList, head, next) == head)
         {
            freeListPopLock = 0;

            head->next = 0;
            return head;
         }
      }
   }




   MarkChunk *getInitJob()
   {
      MarkChunk *result = popJobLocked(0);
      if (result)
      {
         if (result->count==MarkChunk::OBJ_ARRAY_JOB)
         {
            GCLOG("Popped array job?\n");
            pushJob(result,false);
         }
         else
            return result;
      }
      return alloc();
   }

};

GlobalChunks sGlobalChunks;

class MarkContext
{
    #ifdef HXCPP_DEBUG
    MarkInfo  *mInfo;
    int       mPos;
    #endif

    int       mThreadId;
    MarkChunk *marking;


public:
    enum { StackSize = 8192 };

    bool isGenerational;

    MarkContext(int inThreadId = -1)
    {
       #ifdef HXCPP_DEBUG
       mInfo = new MarkInfo[StackSize];
       mPos = 0;
       #endif
       mThreadId = inThreadId;
       marking = sGlobalChunks.alloc();

       isGenerational = false;
    }
    ~MarkContext()
    {
       if (marking) sGlobalChunks.free(marking);
       #ifdef HXCPP_DEBUG
       delete [] mInfo;
       #endif
       // TODO: Free slabs
    }


    #ifdef HXCPP_DEBUG
    void PushClass(const char *inClass)
    {
       if (mPos<StackSize-1)
       {
          mInfo[mPos].mClass = inClass;
          mInfo[mPos].mMember = 0;
       }
       mPos++;
    }


    void SetMember(const char *inMember)
    {
       // Should not happen...
       if (mPos==0)
          return;
       if (mPos<StackSize)
          mInfo[mPos-1].mMember = inMember ? inMember : "Unknown";
    }
    void PopClass() { mPos--; }

    void Trace()
    {
       int n = mPos < StackSize ? mPos : StackSize;
       #ifdef ANDROID
       __android_log_print(ANDROID_LOG_ERROR, "trace", "Class referenced from");
       #else
       printf("Class referenced from:\n");
       #endif

       for(int i=0;i<n;i++)
          #ifdef ANDROID
          __android_log_print(ANDROID_LOG_INFO, "trace", "%s.%s",  mInfo[i].mClass, mInfo[i].mMember );
          #else
          printf("%s.%s\n",  mInfo[i].mClass, mInfo[i].mMember );
          #endif

       if (mPos>=StackSize)
       {
          #ifdef ANDROID
          __android_log_print(ANDROID_LOG_INFO, "trace", "... + deeper");
          #else
          printf("... + deeper\n");
          #endif
       }
    }
    #endif


    void pushObj(hx::Object *inObject)
    {
       if (marking->count < MarkChunk::SIZE)
       {
          marking->push(inObject);
       }
       else
       {
          marking = sGlobalChunks.pushJob(marking,true);
          marking->push(inObject);
       }
    }

    void init()
    {
       if (!marking)
          marking = sGlobalChunks.getInitJob();
    }

    void releaseJobs()
    {
       if (marking && marking->count)
       {
          sGlobalChunks.pushJob(marking,false);
       }
       else if (marking)
       {
          sGlobalChunks.release(marking);
       }
       marking = 0;
    }

    void processMarkStack()
    {
       while(true)
       {
          if (!marking || !marking->count)
          {
             #ifdef HX_MULTI_THREAD_MARKING
             if (sgThreadPoolAbort)
             {
                releaseJobs();
                // Mirror popJobOrFinish's bookkeeping: without completing the
                // thread here it would go back to waitForThreadWake with its
                // sRunningThreads bit still set, and StopThreadJobs would wait
                // for it forever (the major-abort hang in gc_perf.log).
                if (mThreadId>=0 && sAllThreads)
                {
                   std::lock_guard<std::mutex> l(sThreadPoolLock);
                   sGlobalChunks.completeThreadLocked(mThreadId);
                }
                return;
             }
             #endif

             marking = sGlobalChunks.popJobOrFinish(marking,mThreadId);
             if (!marking)
                break;

             if (marking->count==MarkChunk::OBJ_ARRAY_JOB)
             {
                int n = marking->arrayElements;
                hx::Object **elems = marking->arrayBase;
                marking->count = 0;
                MarkObjectArray(elems, n, this);
                continue;
             }
          }

          while(marking)
          {
             hx::Object *obj = marking->pop();
             if (obj)
             {
                // Re-scanning a remembered referrer clears its remembered bit,
                // otherwise the write barrier would ignore later black->white
                // stores into it until the next cycle.
                unsigned char &objMark = ((unsigned char *)obj)[HX_ENDIAN_MARK_ID_BYTE];
                if (objMark & HX_GC_REMEMBERED)
                   objMark &= ~HX_GC_REMEMBERED;
                obj->__Mark(this);
                #ifdef HX_MULTI_THREAD_MARKING
                // Load balance
                if (sLazyThreads && marking->count>32)
                {
                   MarkChunk *c = sGlobalChunks.alloc();
                   marking->count -= 16;
                   c->count = 16;
                   memcpy( c->stack, marking->stack + marking->count, 16*sizeof(hx::Object *));
                   sGlobalChunks.pushJob(c,false);
                }
                #ifdef PROFILE_THREAD_USAGE
                sThreadMarkCount[mThreadId]++;
                #endif
                #endif
             }
             else
                break;
          }
       }
    }


    // Process at most ioBudget objects, then return.  Returns true when the
    // marker is drained (no more work), false when work remains.
    bool processMarkStackBudget(int &ioBudget)
    {
       while(ioBudget > 0)
       {
          if (!marking || !marking->count)
          {
             #ifdef HX_MULTI_THREAD_MARKING
             if (sgThreadPoolAbort)
             {
                releaseJobs();
                // Same bookkeeping as processMarkStack's abort exit: the pool
                // thread must complete or StopThreadJobs waits forever.
                if (mThreadId>=0 && sAllThreads)
                {
                   std::lock_guard<std::mutex> l(sThreadPoolLock);
                   sGlobalChunks.completeThreadLocked(mThreadId);
                }
                return true;
             }
             #endif

             marking = sGlobalChunks.popJobOrFinish(marking,mThreadId);
             if (!marking)
                return true;

             if (marking->count==MarkChunk::OBJ_ARRAY_JOB)
             {
                int n = marking->arrayElements;
                hx::Object **elems = marking->arrayBase;
                marking->count = 0;
                MarkObjectArray(elems, n, this);
                continue;
             }
          }

          while(marking)
          {
             hx::Object *obj = marking->pop();
             if (obj)
             {
                #ifdef HXCPP_GC_TRACE
                if ((ioBudget & 63)==0)
                {
                   char traceBuf[64];
                   snprintf(traceBuf,sizeof(traceBuf),"mark obj=%p mark=%02x",
                      obj, ((unsigned char *)obj)[HX_ENDIAN_MARK_ID_BYTE]);
                   GCTrace(traceBuf);
                }
                #endif
                // Re-scanning a remembered referrer clears its remembered bit,
                // otherwise the write barrier would ignore later black->white
                // stores into it until the next cycle.
                unsigned char &objMark = ((unsigned char *)obj)[HX_ENDIAN_MARK_ID_BYTE];
                if (objMark & HX_GC_REMEMBERED)
                   objMark &= ~HX_GC_REMEMBERED;
                obj->__Mark(this);
                ioBudget--;
                if (ioBudget <= 0)
                   return false;

                #ifdef HX_MULTI_THREAD_MARKING
                // Load balance
                if (sLazyThreads && marking->count>32)
                {
                   MarkChunk *c = sGlobalChunks.alloc();
                   marking->count -= 16;
                   c->count = 16;
                   memcpy( c->stack, marking->stack + marking->count, 16*sizeof(hx::Object *));
                   sGlobalChunks.pushJob(c,false);
                }
                #ifdef PROFILE_THREAD_USAGE
                sThreadMarkCount[mThreadId]++;
                #endif
                #endif
             }
             else
                break;
          }
       }

       return false;
    }
};


/*
void MarkerReleaseWorkerLocked( )
{
   //printf("Release...\n");
   for(int i=0;i<sAllThreads;i++)
   {
      if ( ! (sRunningThreads & (1<<i) ) )
      {
         //printf("Wake %d\n",i);
         sRunningThreads |= (1<<i);
         sThreadWake[i]->Set();
         return;
      }
   }
}
*/



#ifdef HXCPP_DEBUG
static bool breakOnce = 1;
void MarkSetMember(const char *inName,hx::MarkContext *__inCtx)
{
   if (gCollectTrace)
      __inCtx->SetMember(inName);
}

void MarkPushClass(const char *inName,hx::MarkContext *__inCtx)
{
   if (gCollectTrace)
      __inCtx->PushClass(inName);
}

void MarkPopClass(hx::MarkContext *__inCtx)
{
   if (gCollectTrace)
      __inCtx->PopClass();
}
#endif




struct AutoMarkPush
{
   hx::MarkContext *mCtx;
   AutoMarkPush(hx::MarkContext *ctx, const char *cls, const char *member)
   {
      #ifdef HXCPP_DEBUG
      mCtx = ctx;
      MarkPushClass(cls,mCtx);
      MarkSetMember(member,mCtx);
      #endif
   }
   ~AutoMarkPush()
   {
      #ifdef HXCPP_DEBUG
      MarkPopClass(mCtx);
      #endif
   }
};






void MarkAllocUnchecked(void *inPtr,hx::MarkContext *__inCtx)
{
   #ifdef PROFILE_COLLECT
   sAllocMarks++;
   #endif

   size_t ptr_i = ((size_t)inPtr)-sizeof(int);
   unsigned int flags =  *((unsigned int *)ptr_i);

   #ifdef HXCPP_GC_NURSERY
   if (!(flags & 0xff000000))
   {
      #ifdef HX_GC_VERIFY_GENERATIONAL
      if (sGcVerifyGenerational)
      {
         printf("Nursery alloc escaped generational collection %p\n", inPtr);
         DebuggerTrap();
      }
      #endif

      int size = flags & 0xffff;
      // Size will be 0 for large allocs -> no need to mark block
      if (size)
      {
         int start = (int)(ptr_i & IMMIX_BLOCK_OFFSET_MASK);
         int startRow = start>>IMMIX_LINE_BITS;
         int blockId = *(BlockIdType *)(ptr_i & IMMIX_BLOCK_BASE_MASK);
         BlockDataInfo *info = (*gBlockInfo)[blockId];

         int endRow = (start + size + sizeof(int) + IMMIX_LINE_LEN-1)>>IMMIX_LINE_BITS;
         *(unsigned int *)ptr_i = flags = (flags & IMMIX_HEADER_PRESERVE) |
                                          (endRow -startRow) |
                                          (size<<IMMIX_ALLOC_SIZE_SHIFT) |
                                          gMarkID;

         unsigned int startFlag = gImmixStartFlag[start&127];
         unsigned int *pos = info->allocStart + startRow;
         // Most markings hit a slot that is already recorded; skipping the
         // atomic here removes the cache-line contention between the marker
         // threads, which is what the parallel phase spends its time on.
         if (!(*pos & startFlag))
         {
            unsigned int val = *pos;
            while(_hx_atomic_compare_exchange((volatile int *)pos, val,val|startFlag) != val)
               val = *pos;
         }

         #ifdef HXCPP_GC_GENERATIONAL
         info->mHasSurvivor = true;
         #endif
      }
      else
      {
         // Large nursury object
         ((unsigned char *)inPtr)[HX_ENDIAN_MARK_ID_BYTE] = gByteMarkID;
      }
   }
   else
   #endif
   {
      #ifdef HX_GC_VERIFY_GENERATIONAL
      if (sGcVerifyGenerational && ((unsigned char *)inPtr)[HX_ENDIAN_MARK_ID_BYTE] != gPrevByteMarkID)
      {
         printf("Alloc missed int generational collection %p\n", inPtr);
         DebuggerTrap();
      }
      #endif
      ((unsigned char *)inPtr)[HX_ENDIAN_MARK_ID_BYTE] = gByteMarkID;
   }

   int rows = flags & IMMIX_ALLOC_ROW_COUNT;
   if (rows)
   {
      #if HXCPP_GC_DEBUG_LEVEL>0
      if ( ((ptr_i & IMMIX_BLOCK_OFFSET_MASK)>>IMMIX_LINE_BITS) + rows > IMMIX_LINES) DebuggerTrap();
      #endif

      char *block = (char *)(ptr_i & IMMIX_BLOCK_BASE_MASK);
      char *rowMark = block + ((ptr_i & IMMIX_BLOCK_OFFSET_MASK)>>IMMIX_LINE_BITS);
      *rowMark = 1;
      if (rows>1)
      {
         rowMark[1] = 1;
         if (rows>2)
         {
            rowMark[2] = 1;
            if (rows>3)
            {
               rowMark[3] = 1;
               for(int r=4; r<rows; r++)
                  rowMark[r]=1;
            }
         }
      }

   // MARK_ROWS_UNCHECKED_END
   }
}

void MarkObjectAllocUnchecked(hx::Object *inPtr,hx::MarkContext *__inCtx)
{
   size_t ptr_i = ((size_t)inPtr)-sizeof(int);
   unsigned int flags =  *((unsigned int *)ptr_i);
   #ifdef HXCPP_GC_NURSERY
   if (!(flags & 0xff000000))
   {
      #if defined(HX_GC_VERIFY_GENERATIONAL)
         if (sGcVerifyGenerational)
         {
            printf("Nursery object escaped generational collection %p\n", inPtr);
            DebuggerTrap();
         }
      #endif


      int size = flags & 0xffff;
      int start = (int)(ptr_i & IMMIX_BLOCK_OFFSET_MASK);
      int startRow = start>>IMMIX_LINE_BITS;
      int blockId = *(BlockIdType *)(ptr_i & IMMIX_BLOCK_BASE_MASK);
      BlockDataInfo *info = (*gBlockInfo)[blockId];

      int endRow = (start + size + sizeof(int) + IMMIX_LINE_LEN-1)>>IMMIX_LINE_BITS;
      *(unsigned int *)ptr_i = flags = (flags & IMMIX_HEADER_PRESERVE) |
                                       (endRow -startRow) |
                                       (size<<IMMIX_ALLOC_SIZE_SHIFT) |
                                       gMarkID;

      unsigned int startFlag = gImmixStartFlag[start&127];
      unsigned int *pos = info->allocStart + startRow;
      if (!(*pos & startFlag))
      {
         unsigned int val = *pos;
         while(_hx_atomic_compare_exchange( (volatile int *)pos, val, val|startFlag) != val)
            val = *pos;
      }
      #ifdef HXCPP_GC_GENERATIONAL
      info->mHasSurvivor = true;
      #endif
   }
   else
   #endif
      ((unsigned char *)inPtr)[HX_ENDIAN_MARK_ID_BYTE] = gByteMarkID;

   int rows = flags & IMMIX_ALLOC_ROW_COUNT;
   if (rows)
   {
      char *block = (char *)(ptr_i & IMMIX_BLOCK_BASE_MASK);
      char *rowMark = block + ((ptr_i & IMMIX_BLOCK_OFFSET_MASK)>>IMMIX_LINE_BITS);
      #if HXCPP_GC_DEBUG_LEVEL>0
      if ( ((ptr_i & IMMIX_BLOCK_OFFSET_MASK)>>IMMIX_LINE_BITS) + rows > IMMIX_LINES) DebuggerTrap();
      #endif

      *rowMark = 1;
      if (rows>1)
      {
         rowMark[1] = 1;
         if (rows>2)
         {
            rowMark[2] = 1;
            if (rows>3)
            {
               rowMark[3] = 1;
               for(int r=4; r<rows; r++)
                  rowMark[r]=1;
            }
         }
      }

      if (flags & IMMIX_ALLOC_IS_CONTAINER)
      {
         #ifdef PROFILE_COLLECT
         sObjectMarks++;
         #endif

         #ifdef HXCPP_DEBUG
            if (gCollectTrace && gCollectTrace==inPtr->__GetClass().GetPtr())
            {
               gCollectTraceCount++;
               if (gCollectTraceDoPrint)
                   __inCtx->Trace();
            }

            // Recursive mark so stack stays intact..
            #if (HXCPP_GC_DEBUG_LEVEL>0)
            inPtr->__Mark(__inCtx);
            #else
            if (gCollectTrace)
               inPtr->__Mark(__inCtx);
            else
               __inCtx->pushObj(inPtr);
            #endif
         #else // Not debug

            // There is a slight performance gain by calling recursively, but you
            //   run the risk of stack overflow.  Also, a parallel mark algorithm could be
            //   done when the marking is stack based.
            //inPtr->__Mark(__inCtx);
            #if (HXCPP_GC_DEBUG_LEVEL>0)
            inPtr->__Mark(__inCtx);
            #else
            __inCtx->pushObj(inPtr);
            #endif
        #endif
      }
      else
      {
         #ifdef PROFILE_COLLECT
         sAllocMarks++;
         #endif
      }

   // MARK_ROWS_UNCHECKED_END
   }
}


void MarkObjectArray(hx::Object **inPtr, int inLength, hx::MarkContext *__inCtx)
{
   hx::Object *tmp;

   int extra = inLength & 0x0f;
   for(int i=0;i<extra;i++)
      if (inPtr[i]) MarkObjectAlloc(inPtr[i],__inCtx);
   if (inLength==extra)
      return;

   inLength -= extra;
   hx::Object **ptrI = inPtr + extra;
   hx::Object **end = ptrI + inLength;


   #define MARK_PTR_I \
   tmp = *ptrI++; \
   if (tmp) MarkObjectAlloc(tmp,__inCtx);



   #ifdef HX_MULTI_THREAD_MARKING
   if (sAllThreads && inLength>4096)
   {
      hx::Object **dishOffEnd = end - 4096;
      while(ptrI<end)
      {
         // Are the other threads slacking off?
         if ((sRunningThreads != sAllThreads) && ptrI<dishOffEnd)
         {
            ptrI += sGlobalChunks.takeArrayJob(ptrI, end-ptrI);
         }
         else
         {
            MARK_PTR_I;
            MARK_PTR_I;
            MARK_PTR_I;
            MARK_PTR_I;

            MARK_PTR_I;
            MARK_PTR_I;
            MARK_PTR_I;
            MARK_PTR_I;

            MARK_PTR_I;
            MARK_PTR_I;
            MARK_PTR_I;
            MARK_PTR_I;

            MARK_PTR_I;
            MARK_PTR_I;
            MARK_PTR_I;
            MARK_PTR_I;
         }
      }
   }
   else
   #endif
   {
      while(ptrI<end)
      {
         MARK_PTR_I;
         MARK_PTR_I;
         MARK_PTR_I;
         MARK_PTR_I;

         MARK_PTR_I;
         MARK_PTR_I;
         MARK_PTR_I;
         MARK_PTR_I;

         MARK_PTR_I;
         MARK_PTR_I;
         MARK_PTR_I;
         MARK_PTR_I;

         MARK_PTR_I;
         MARK_PTR_I;
         MARK_PTR_I;
         MARK_PTR_I;
      }
   }
}

void MarkStringArray(String *inPtr, int inLength, hx::MarkContext *__inCtx)
{
   #if 0
   if (MAX_GC_THREADS>1 && sAllThreads && inLength>4096)
   {
      int extra = inLength & 0x0f;
      for(int i=0;i<extra;i++)
         if (inPtr[i]) MarkObjectAlloc(inPtr[i],__inCtx);

      hx::Object **ptrI = inPtr + extra;
      hx::Object **end = ptrI + (inLength& ~0x0f);
      hx::Object **dishOffEnd = end - 4096;
      while(ptrI<end)
      {
         // Are the other threads slacking off?
         if ((sRunningThreads != sAllThreads) && ptrI<dishOffEnd)
         {
            ptrI += sGlobalChunks.takeArrayJob(ptrI, end-ptrI);
         }

         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
         if (*ptrI) MarkObjectAlloc(*ptrI,__inCtx); ptrI++;
      }
   }
   else
   #endif
   {
      for(int i=0;i<inLength;i++)
      {
         const char *str = inPtr[i].raw_ptr();
         HX_MARK_STRING(str);
      }
   }
}

#ifdef HXCPP_DEBUG
#define FILE_SCOPE
#else
#define FILE_SCOPE static
#endif

// --- Roots -------------------------------

FILE_SCOPE std::mutex* sGCRootLock = nullptr;
typedef hx::UnorderedSet<hx::Object **> RootSet;
static RootSet sgRootSet;

typedef hx::UnorderedMap<void *,int> OffsetRootSet;
static OffsetRootSet *sgOffsetRootSet=0;

void GCAddRoot(hx::Object **inRoot)
{
   std::lock_guard<std::mutex> lock(*sGCRootLock);
   sgRootSet.insert(inRoot);
}

void GCRemoveRoot(hx::Object **inRoot)
{
   std::lock_guard<std::mutex> lock(*sGCRootLock);
   sgRootSet.erase(inRoot);
}


void GcAddOffsetRoot(void *inRoot, int inOffset)
{
   std::lock_guard<std::mutex> lock(*sGCRootLock);
   if (!sgOffsetRootSet)
      sgOffsetRootSet = new OffsetRootSet();
   (*sgOffsetRootSet)[inRoot] = inOffset;
}

void GcSetOffsetRoot(void *inRoot, int inOffset)
{
   std::lock_guard<std::mutex> lock(*sGCRootLock);
   (*sgOffsetRootSet)[inRoot] = inOffset;
}

void GcRemoveOffsetRoot(void *inRoot)
{
   std::lock_guard<std::mutex> lock(*sGCRootLock);
   OffsetRootSet::iterator r = sgOffsetRootSet->find(inRoot);
   sgOffsetRootSet->erase(r);
}




// --- Finalizers -------------------------------


class WeakRef;
typedef hx::QuickVec<WeakRef *> WeakRefs;

FILE_SCOPE std::mutex *sFinalizerLock = 0;
FILE_SCOPE WeakRefs sWeakRefs;

class WeakRef : public hx::Object
{
public:
   HX_IS_INSTANCE_OF enum { _hx_ClassId = hx::clsIdWeakRef };

   WeakRef(Dynamic inRef)
   {
      mRef = inRef;
      if (mRef.mPtr)
      {
         std::lock_guard<std::mutex> lock(*sFinalizerLock);
         sWeakRefs.push(this);
      }
   }

   // Don't mark our ref !

   #ifdef HXCPP_VISIT_ALLOCS
   void __Visit(hx::VisitContext *__inCtx) HXCPP_OVERRIDE { HX_VISIT_MEMBER(mRef); }
   #endif

   Dynamic mRef;
};



typedef hx::QuickVec<InternalFinalizer *> FinalizerList;

FILE_SCOPE FinalizerList *sgFinalizers = 0;

typedef hx::UnorderedMap<hx::Object *,hx::finalizer> FinalizerMap;
FILE_SCOPE FinalizerMap sFinalizerMap;

typedef void (*HaxeFinalizer)(Dynamic);
typedef hx::UnorderedMap<hx::Object *,HaxeFinalizer> HaxeFinalizerMap;
FILE_SCOPE HaxeFinalizerMap sHaxeFinalizerMap;

hx::QuickVec<int> sFreeObjectIds;
typedef hx::UnorderedMap<hx::Object *,int> ObjectIdMap;
typedef hx::QuickVec<hx::Object *> IdObjectMap;
FILE_SCOPE ObjectIdMap sObjectIdMap;
FILE_SCOPE IdObjectMap sIdObjectMap;

typedef hx::UnorderedSet<hx::Object *> MakeZombieSet;
FILE_SCOPE MakeZombieSet sMakeZombieSet;

typedef hx::QuickVec<hx::Object *> ZombieList;
FILE_SCOPE ZombieList sZombieList;

typedef hx::QuickVec<hx::HashRoot *> WeakHashList;
FILE_SCOPE WeakHashList sWeakHashList;


InternalFinalizer::InternalFinalizer(hx::Object *inObj, finalizer inFinalizer)
{
   mValid = true;
   mObject = inObj;
   mFinalizer = inFinalizer;

   // Ensure this survives generational collect
   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   sgFinalizers->push(this);
}

#ifdef HXCPP_VISIT_ALLOCS
void InternalFinalizer::Visit(VisitContext *__inCtx)
{
   HX_VISIT_OBJECT(mObject);
}
#endif

void InternalFinalizer::Detach()
{
   mValid = false;
}

void FindZombies(MarkContext &inContext)
{
   bool found = false;
   for(MakeZombieSet::iterator i=sMakeZombieSet.begin(); i!=sMakeZombieSet.end(); )
   {
      hx::Object *obj = *i;
      MakeZombieSet::iterator next = i;
      ++next;

      unsigned char mark = ((unsigned char *)obj)[HX_ENDIAN_MARK_ID_BYTE];
      if ( mark!=gByteMarkID )
      {
         sZombieList.push(obj);
         sMakeZombieSet.erase(i);

         // Mark now to prevent secondary zombies...
         inContext.init();
         hx::MarkObjectAlloc(obj , &inContext );
         found = true;
      }

      i = next;
   }

   // Draining once at the end instead of per zombie: the per-call setup cost
   // showed up as a multi-ms spike whenever many objects were zombified.
   if (found)
      inContext.processMarkStack();
}

bool IsWeakRefValid(const HX_CHAR *inPtr)
{
   unsigned char mark = ((unsigned char *)inPtr)[HX_ENDIAN_MARK_ID_BYTE];

    // Special case of member closure - check if the 'this' pointer is still alive
   return  mark==gByteMarkID;
}

bool IsWeakRefValid(hx::Object *inPtr)
{
   unsigned char mark = ((unsigned char *)inPtr)[HX_ENDIAN_MARK_ID_BYTE];

    // Special case of member closure - check if the 'this' pointer is still alive
    bool isCurrent = mark==gByteMarkID;
    if ( !isCurrent && inPtr->__GetType()==vtFunction)
    {
        hx::Object *thiz = (hx::Object *)inPtr->__GetHandle();
        if (thiz)
        {
            mark = ((unsigned char *)thiz)[HX_ENDIAN_MARK_ID_BYTE];
            if (mark==gByteMarkID)
            {
               // The object is still alive, so mark the closure and continue
               MarkAlloc(inPtr,0);
               return true;
            }
         }
    }
    return isCurrent;
}

static void someHackyFunc(hx::Object *)
{
}

static void (*hackyFunctionCall)(hx::Object *) = someHackyFunc;

struct Finalizable
{
   union
   {
      _hx_member_finalizer member;
      _hx_alloc_finalizer  alloc;
   };
   void *base;
   bool pin;
   bool isMember;

   Finalizable(hx::Object *inBase, _hx_member_finalizer inMember, bool inPin)
   {
      base = inBase;
      member = inMember;
      pin = inPin;
      isMember = true;
   }

   Finalizable(void *inBase, _hx_alloc_finalizer inAlloc, bool inPin)
   {
      base = inBase;
      alloc = inAlloc;
      pin = inPin;
      isMember = false;
   }
   void run()
   {
      if (isMember)
      {
         hx::Object *object = (hx::Object *)base;
         // I can't tell if it is msvc over-optimizing this code, to I am not
         //  quite calling things right, but this seems to fix it...
         hackyFunctionCall(object);
         (object->*member)();
      }
      else
         alloc( base );
   }
};
typedef hx::QuickVec< Finalizable > FinalizableList;
FILE_SCOPE FinalizableList sFinalizableList;


static double tFinalizers;
static int finalizerCount;
static int localCount;
static int localObjects;
static int localAllocs;
static int rootObjects;
static int rootAllocs;

void RunFinalizers()
{
   finalizerCount = 0;

   FinalizerList &list = *sgFinalizers;
   int idx = 0;
   while(idx<list.size())
   {
      InternalFinalizer *f = list[idx];
      if (!f->mValid)
      {
         list.qerase(idx);
         delete f;
      }
      else if (((unsigned char *)(f->mObject))[HX_ENDIAN_MARK_ID_BYTE] != gByteMarkID)
      {
         if (f->mFinalizer)
         {
            f->mFinalizer(f->mObject);
            finalizerCount++;
         }
         list.qerase(idx);
         delete f;
      }
      else
      {
         idx++;
      }
   }

   idx = 0;
   while(idx<sFinalizableList.size())
   {
      Finalizable &f = sFinalizableList[idx];
      unsigned char mark = ((unsigned char *)f.base)[HX_ENDIAN_MARK_ID_BYTE];
      if ( mark!=gByteMarkID )
      {
         finalizerCount++;
         f.run();
         sFinalizableList.qerase(idx);
      }
      else
         idx++;
   }

   for(FinalizerMap::iterator i=sFinalizerMap.begin(); i!=sFinalizerMap.end(); )
   {
      hx::Object *obj = i->first;
      FinalizerMap::iterator next = i;
      ++next;

      unsigned char mark = ((unsigned char *)obj)[HX_ENDIAN_MARK_ID_BYTE];
      if ( mark!=gByteMarkID )
      {
         finalizerCount++;
         (*i->second)(obj);
         sFinalizerMap.erase(i);
      }

      i = next;
   }


   for(HaxeFinalizerMap::iterator i=sHaxeFinalizerMap.begin(); i!=sHaxeFinalizerMap.end(); )
   {
      hx::Object *obj = i->first;
      HaxeFinalizerMap::iterator next = i;
      ++next;

      unsigned char mark = ((unsigned char *)obj)[HX_ENDIAN_MARK_ID_BYTE];
      if ( mark!=gByteMarkID )
      {
         finalizerCount++;
         (*i->second)(obj);
         sHaxeFinalizerMap.erase(i);
      }

      i = next;
   }
   MEM_STAMP(hx::tFinalizers);

   for(ObjectIdMap::iterator i=sObjectIdMap.begin(); i!=sObjectIdMap.end(); )
   {
      ObjectIdMap::iterator next = i;
      next++;

      hx::Object *o = i->first;
      unsigned char mark = ((unsigned char *)o)[HX_ENDIAN_MARK_ID_BYTE];
      if ( mark!=gByteMarkID && !(((unsigned int *)o)[-1] & HX_GC_CONST_ALLOC_BIT))
      {
         sFreeObjectIds.push(i->second);
         sIdObjectMap[i->second] = 0;
         sObjectIdMap.erase(i);
      }

      i = next;
   }

   for(int i=0;i<sWeakHashList.size();    )
   {
      HashRoot *ref = sWeakHashList[i];
      unsigned char mark = ((unsigned char *)ref)[HX_ENDIAN_MARK_ID_BYTE];
      // Object itself is gone - no need to worry about that again
      if ( mark!=gByteMarkID )
      {
         sWeakHashList.qerase(i);
         // no i++ ...
      }
      else
      {
         ref->updateAfterGc();
         i++;
      }
   }



   for(int i=0;i<sWeakRefs.size();    )
   {
      WeakRef *ref = sWeakRefs[i];
      unsigned char mark = ((unsigned char *)ref)[HX_ENDIAN_MARK_ID_BYTE];
      // Object itself is gone ...
      if ( mark!=gByteMarkID )
      {
         sWeakRefs.qerase(i);
         // no i++ ...
      }
      else
      {
         // what about the reference?
         hx::Object *r = ref->mRef.mPtr;
         unsigned char mark = ((unsigned char *)r)[HX_ENDIAN_MARK_ID_BYTE];

         // Special case of member closure - check if the 'this' pointer is still alive
         if ( mark!=gByteMarkID && r->__GetType()==vtFunction)
         {
            hx::Object *thiz = (hx::Object *)r->__GetHandle();
            if (thiz)
            {
               mark = ((unsigned char *)thiz)[HX_ENDIAN_MARK_ID_BYTE];
               if (mark==gByteMarkID)
               {
                  // The object is still alive, so mark the closure and continue
                  MarkAlloc(r,0);
               }
            }
         }

         if ( mark!=gByteMarkID )
         {
            ref->mRef.mPtr = 0;
            sWeakRefs.qerase(i);
         }
         else
            i++;
      }
   }
}

// Callback finalizer on non-abstract type;
void  GCSetFinalizer( hx::Object *obj, hx::finalizer f )
{
   if (!obj)
      throw Dynamic(HX_CSTRING("set_finalizer - invalid null object"));
   if (((unsigned int *)obj)[-1] & HX_GC_CONST_ALLOC_BIT)
      throw Dynamic(HX_CSTRING("set_finalizer - invalid const object"));

   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   if (f==0)
   {
      FinalizerMap::iterator i = sFinalizerMap.find(obj);
      if (i!=sFinalizerMap.end())
         sFinalizerMap.erase(i);
   }
   else
      sFinalizerMap[obj] = f;
}


// Callback finalizer on non-abstract type;
void  GCSetHaxeFinalizer( hx::Object *obj, HaxeFinalizer f )
{
   if (!obj)
      throw Dynamic(HX_CSTRING("set_finalizer - invalid null object"));
   if (((unsigned int *)obj)[-1] & HX_GC_CONST_ALLOC_BIT)
      throw Dynamic(HX_CSTRING("set_finalizer - invalid const object"));

   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   if (f==0)
   {
      HaxeFinalizerMap::iterator i = sHaxeFinalizerMap.find(obj);
      if (i!=sHaxeFinalizerMap.end())
         sHaxeFinalizerMap.erase(i);
   }
   else
      sHaxeFinalizerMap[obj] = f;
}

void GCDoNotKill(hx::Object *inObj)
{
   if (!inObj)
      throw Dynamic(HX_CSTRING("doNotKill - invalid null object"));
   if (((unsigned int *)inObj)[-1] & HX_GC_CONST_ALLOC_BIT)
      throw Dynamic(HX_CSTRING("doNotKill - invalid const object"));

   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   sMakeZombieSet.insert(inObj);
}

hx::Object *GCGetNextZombie()
{
   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   if (sZombieList.empty())
      return 0;
   hx::Object *result = sZombieList.pop();
   return result;
}

void RegisterWeakHash(HashBase<String> *inHash)
{
   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   sWeakHashList.push(inHash);
}

void RegisterWeakHash(HashBase<Dynamic> *inHash)
{
   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   sWeakHashList.push(inHash);
}



void InternalEnableGC(bool inEnable)
{
   //printf("Enable %d\n", sgInternalEnable);
   sgInternalEnable = inEnable;
}

bool IsConstAlloc(const void *inData)
{
   unsigned int *header = (unsigned int *)inData;
   return header[-1] & HX_GC_CONST_ALLOC_BIT;
}

void *InternalCreateConstBuffer(const void *inData,int inSize,bool inAddStringHash)
{
   bool addHash = inAddStringHash && inSize>0;

   int *result = (int *)HxAlloc(inSize + sizeof(int) + (addHash ? sizeof(int):0) );
   if (addHash)
   {
      unsigned int hash = 0;
      if (inData)
         for(int i=0;i<inSize-1;i++)
            hash = hash*223 + ((unsigned char *)inData)[i];

      //*((unsigned int *)((char *)result + inSize + sizeof(int))) = hash;
      *result++ = hash;
      *result++ = HX_GC_CONST_ALLOC_BIT | HX_GC_STRING_HASH;
   }
   else
   {
      *result++ = HX_GC_CONST_ALLOC_BIT;
   }

   if (inData)
   {
      memcpy(result,inData,inSize);
   }
   else if (inSize)
   {
      ZERO_MEM(result,inSize);
   }

   return result;
}

// Used when the allocation size is zero for a non-null pointer
void *emptyAlloc = InternalCreateConstBuffer(0,0,false);


} // namespace hx


hx::Object *__hxcpp_weak_ref_create(Dynamic inObject)
{
   return new hx::WeakRef(inObject);
}

hx::Object *__hxcpp_weak_ref_get(Dynamic inRef)
{
   #ifdef HXCPP_DEBUG
   hx::WeakRef *ref = dynamic_cast<hx::WeakRef *>(inRef.mPtr);
   #else
   hx::WeakRef *ref = static_cast<hx::WeakRef *>(inRef.mPtr);
   #endif
   return ref->mRef.mPtr;
}


// --- GlobalAllocator -------------------------------------------------------

typedef hx::QuickVec<BlockDataInfo *> BlockList;

typedef hx::QuickVec<unsigned int *> LargeList;

enum MemType { memUnmanaged, memBlock, memLarge };




#ifdef HXCPP_VISIT_ALLOCS
class AllocCounter : public hx::VisitContext
{
public:
   int count;

   AllocCounter() { count = 0; }

   void visitObject(hx::Object **ioPtr) HXCPP_OVERRIDE { count ++; }
   void visitAlloc(void **ioPtr) HXCPP_OVERRIDE { count ++; }
};


#endif


class GlobalAllocator *sGlobalAlloc = 0;


inline bool SortByBlockPtr(BlockDataInfo *inA, BlockDataInfo *inB)
{
   return inA->mPtr < inB->mPtr;
}

struct MoveBlockJob
{
   BlockList blocks;
   int from;
   int to;

   MoveBlockJob(BlockList &inAllBlocks)
   {
      blocks.setSize(inAllBlocks.size());
      memcpy(&blocks[0], &inAllBlocks[0], inAllBlocks.size()*sizeof(void*));

      std::sort(&blocks[0], &blocks[0]+blocks.size(), SortMoveOrder );
      from = 0;
      to = blocks.size()-1;
   }

   BlockDataInfo *getFrom()
   {
      while(true)
      {
         if (from>=to)
         {
            //printf("Caught up!\n");
            return 0;
         }
         #ifndef HXCPP_GC_DEBUG_ALWAYS_MOVE
         // Pinned / full
         if (blocks[from]->mMoveScore<2)
         {
            //printf("All other blocks good!\n");
            while(from<to)
            {
               //printf("Ignore DEFRAG %p ... %p\n", blocks[from]->mPtr, blocks[from]->mPtr+1);
               from++;
            }
            return 0;
         }
         #endif
         if (blocks[from]->mPinned)
         {
            //printf("PINNED DEFRAG %p ... %p\n", blocks[from]->mPtr, blocks[from]->mPtr+1);
            from++;
         }
         else // Found one...
            break;
      }
      //printf("From block %d (id=%d)\n", from, blocks[from]->mId);
      BlockDataInfo *result = blocks[from++];
      ////printf("FROM DEFRAG %p ... %p\n", result->mPtr, result->mPtr + 1 );
      return result;
   }
   BlockDataInfo *getTo()
   {
      if (from>=to)
      {
         //printf("No more room!\n");
         return 0;
      }
      //printf("To block %d (id=%d)\n", to, blocks[to]->mId);
      BlockDataInfo *result = blocks[to--];
      //printf("TO DEFRAG %p ... %p\n", result->mPtr, result->mPtr + 1 );
      return result;
   }
};


#ifndef HX_MEMORY_H_OVERRIDE

#if 0
static hx::QuickVec<void *> sBlockPool;
static int gcBlockAllocs = 0;

void *HxAllocGCBlock(size_t size)
{
   if (sBlockPool.size())
      return sBlockPool.pop();
   gcBlockAllocs++;
   GCLOG("===========================================> New Chunk (%d)\n", gcBlockAllocs);
   return HxAlloc(size);
}

void HxFreeGCBlock(void *p)
{
   sBlockPool.push(p);
}

#else

#ifdef HX_GC_FIXED_BLOCKS
unsigned char *chunkData = 0;
void *HxAllocGCBlock(size_t inSize)
{
   if (!chunkData)
   {
      size_t size = 65536;
      size *= IMMIX_BLOCK_SIZE;
      #if defined(HX_WINDOWS) && defined(HXCPP_M64)
      chunkData = (unsigned char *)0x100000000;
      VirtualAlloc(chunkData,size,MEM_COMMIT|MEM_RESERVE,PAGE_READWRITE);
      #else
      chunkData = (unsigned char *)HxAlloc(size);
      size_t ptr_i = (size_t)(chunkData+0xffff) & ~((size_t)0xffff);
      chunkData = (unsigned char *)ptr_i;
      #endif
      //printf("Using fixed blocks %p...%p\n", chunkData, chunkData+size);
   }
   void *result = chunkData;
   //printf(" %p\n", result);
   chunkData += inSize;
   return result;
}
void HxFreeGCBlock(void *p)
{
   printf("todo - HX_GC_FIXED_BLOCKS %p\n",p);
}
#else
void *HxAllocGCBlock(size_t size) { return HxAlloc(size); }
void HxFreeGCBlock(void *p) { HxFree(p); }
#endif

#endif

#endif // HX_MEMORY_H_OVERRIDE


//#define VERIFY_STACK_READ

#ifdef VERIFY_STACK_READ
// Just have something to do...
int gVerifyVoidCount = 0;
void VerifyStackRead(int *inBottom, int *inTop)
{
   #ifdef HXCPP_STACK_UP
   int *start = inTop-1;
   inTop = inBottom+1;
   inBottom = start;
   #endif

   int n = inTop - inBottom;
   int check = std::min(n,5);
   for(int c=0;c<check;c++)
   {
      if (inBottom[c]==0)
         gVerifyVoidCount++;
      if (inTop[-1-c]==0)
         gVerifyVoidCount++;
   }
}
#endif

// TODO - work out best size based on cache size?
#ifdef HXCPP_GC_BIG_BLOCKS
static int sMinZeroQueueSize = 4*2;
static int sMaxZeroQueueSize = 16*2;
#else
static int sMinZeroQueueSize = 8*2;
static int sMaxZeroQueueSize = 32*2;
#endif

#define BLOCK_OFSIZE_COUNT 12


class GlobalAllocator
{
   enum { LOCAL_POOL_SIZE = 2 };

public:
   // Serialises lazy sweeping between mutator threads.  One block takes a
   // couple of microseconds to reclaim, so contention stays low, and the
   // allocator can hand the reclaimed rows out immediately instead of paying
   // a stop-the-world sweep at the end of every cycle.
   std::mutex mSweepLock;

   GlobalAllocator()
   {
      memset((void *)mNextFreeBlockOfSize,0,sizeof(mNextFreeBlockOfSize));
      mRowsInUse = 0;
      mLargeAllocated = 0;
      mLargeAllocSpace = 40 << 20;
      mLargeAllocForceRefresh = mLargeAllocSpace;
      // Start at 1 Meg...
      mTotalAfterLastCollect = 1<<20;
      mCurrentRowsInUse = 0;
      mAllBlocksCount = 0;
      mGenerationalRetainEstimate = 0.5;
      mSweepCursor = 0;
      mSweepActive = false;
      mSweepOwnedRows = 0;
      for(int p=0;p<LOCAL_POOL_SIZE;p++)
         mLocalPool[p] = 0;

      createFreeList();
   }
   void AddLocal(LocalAllocator *inAlloc)
   {
      if (!gThreadStateChangeLock)
      {
         gThreadStateChangeLock = new std::recursive_mutex();
         gSpecialObjectLock = new std::mutex();
      }
      // Until we add ourselves, the collector will not wait
      //  on us - ie, we are assumed ot be in a GC free zone.
      std::lock_guard<std::recursive_mutex> lock(*gThreadStateChangeLock);
      mLocalAllocs.push(inAlloc);
      // TODO Attach debugger
   }

   bool ReturnToPoolLocked(LocalAllocator *inAlloc)
   {
      // Until we add ourselves, the colled will not wait
      //  on us - ie, we are assumed ot be in a GC free zone.
      for(int p=0;p<LOCAL_POOL_SIZE;p++)
      {
         if (!mLocalPool[p])
         {
            mLocalPool[p] = inAlloc;
            return true;
         }
      }
      // I told him we already got one
      return false;
   }

   LocalAllocator *GetPooledAllocator()
   {
      std::lock_guard<std::recursive_mutex> lock(*gThreadStateChangeLock);
      for(int p=0;p<LOCAL_POOL_SIZE;p++)
      {
         if (mLocalPool[p])
         {
            LocalAllocator *result = mLocalPool[p];
            mLocalPool[p] = 0;
            return result;
         }
      }
      return 0;
   }

   void RemoveLocalLocked(LocalAllocator *inAlloc)
   {
      // You should be in the GC free zone before you call this...
      if (!mLocalAllocs.qerase_val(inAlloc))
      {
         CriticalGCError("LocalAllocator removed without being added");
      }
   }

   void FreeLarge(void *inLarge)
   {
#ifdef HXCPP_TELEMETRY
       __hxt_gc_free_large(inLarge);
#endif

      ((unsigned char *)inLarge)[HX_ENDIAN_MARK_ID_BYTE] = 0;
      // AllocLarge will not lock this list unless it decides there is a suitable
      //  value, so we can't doa realloc without potentially crashing it.
      if (largeObjectRecycle.hasExtraCapacity(1))
      {
         unsigned int *blob = ((unsigned int *)inLarge) - 2;
         unsigned int size = *blob;
         mLargeListLock.lock();
         mLargeAllocated -= size;
         // Could somehow keep it in the list, but mark as recycled?
         mLargeList.qerase_val(blob);
         // We could maybe free anyhow?
         if (!largeObjectRecycle.hasExtraCapacity(1))
         {
            mLargeListLock.unlock();
            HxFree(blob);
            return;
         }
         largeObjectRecycle.push(blob);
         mLargeListLock.unlock();
      }
   }

   void *AllocLarge(int inSize, bool inClear)
   {
      if (hx::gPauseForCollect)
         __hxcpp_gc_safe_point();

      //Should we force a collect ? - the 'large' data are not considered when allocating objects
      // from the blocks, and can 'pile up' between smalll object allocations
      size_t newThreshold = mLargeAllocForceRefresh * 1.5f;
      if ((inSize+mLargeAllocated > newThreshold) && sgInternalEnable)
      {
         #ifdef SHOW_MEM_EVENTS
         //GCLOG("Large alloc causing collection");
         #endif
         CollectFromThisThread(false,false);
      }

      inSize = (inSize +3) & ~3;

      if (inSize<<1 > mLargeAllocSpace)
         mLargeAllocSpace = inSize<<1;

      unsigned int *result = 0;
      #ifndef HXCPP_SINGLE_THREADED_APP
      bool do_lock = true;
      #else
      bool do_lock = false;
      #endif
      bool isLocked = false;


      if (largeObjectRecycle.size())
      {
         for(int i=0;i<largeObjectRecycle.size();i++)
         {
            if ( largeObjectRecycle[i][0] == inSize )
            {
               if (do_lock && !isLocked)
               {
                  mLargeListLock.lock();
                  isLocked = true;
                  if (  i>=largeObjectRecycle.size() || largeObjectRecycle[i][0] != inSize )
                     continue;
               }

               result = largeObjectRecycle[i];
               largeObjectRecycle.qerase(i);
               // You can use this to test race condition
               //Sleep(1);
               break;
            }
         }
      }

      if (!result)
         result = (unsigned int *)HxAlloc(inSize + sizeof(int)*2);

      if (!result)
      {
         #ifdef SHOW_MEM_EVENTS
         GCLOG("Large alloc failed - forcing collect\n");
         #endif

         if (isLocked)
         {
            mLargeListLock.unlock();
            isLocked = false;
         }

         CollectFromThisThread(true,true);
         result = (unsigned int *)HxAlloc(inSize + sizeof(int)*2);
      }

      if (!result)
      {
         GCLOG("Memory Exhausted!\n");
         DebuggerTrap();
      }

      if (inClear)
         ZERO_MEM(result, inSize + sizeof(int)*2);

      result[0] = inSize;
      #ifdef HXCPP_GC_NURSERY
      result[1] = 0;
      #else
      result[1] = hx::gMarkID;
      #endif

      if (do_lock && !isLocked)
         mLargeListLock.lock();

      mLargeList.push(result);
      mLargeAllocated += inSize;

      if (do_lock)
         mLargeListLock.unlock();

#ifdef HXCPP_TELEMETRY
      __hxt_gc_alloc(result + 2, inSize);
#endif

      return result+2;
   }

   void onMemoryChange(int inDelta, const char *inWhy)
   {
      if (hx::gPauseForCollect)
         __hxcpp_gc_safe_point();

      if (inDelta>0)
      {
         //Should we force a collect ? - the 'large' data are not considered when allocating objects
         // from the blocks, and can 'pile up' between smalll object allocations
         if (inDelta>0 && (inDelta+mLargeAllocated > mLargeAllocForceRefresh) && sgInternalEnable)
         {
            //GCLOG("onMemoryChange alloc causing collection");
            CollectFromThisThread(false,false);
         }

         int rounded = (inDelta +3) & ~3;
   
         if (rounded<<1 > mLargeAllocSpace)
            mLargeAllocSpace = rounded<<1;
      }

      #ifndef HXCPP_SINGLE_THREADED_APP
      bool do_lock = true;
      #else
      bool do_lock = false;
      #endif

      if (do_lock)
         mLargeListLock.lock();

      mLargeAllocated += inDelta;

      if (do_lock)
         mLargeListLock.unlock();
   }

   // Gets a block with the 'zeroLock' acquired, which means the zeroing thread
   //  will leave it alone from now on
   //
   // This contains some "lock free" code that triggers the thread sanitizer.
   //  * mOwned can only be changed with the mZeroLock
   //  * mFreeBlocks may increase size, but it is not critical whether the mNextFreeBlockOfSize
   //     is increased since skipping only leads to a bit of extra searhing for the
   //     next allocation
   #if defined(__has_feature)
     #if __has_feature(thread_sanitizer)
      __attribute__((no_sanitize("thread")))
     #endif
   #endif
   BlockDataInfo *GetNextFree(int inRequiredBytes)
   {
      bool failedLock = true;
      int sizeSlot = inRequiredBytes>>IMMIX_LINE_BITS;
      if (sizeSlot>=BLOCK_OFSIZE_COUNT)
         sizeSlot = BLOCK_OFSIZE_COUNT-1;
      //volatile int &nextFreeBlock = mNextFreeBlockOfSize[sizeSlot];
      int nextFreeBlock = mNextFreeBlockOfSize[sizeSlot];
      while(failedLock && nextFreeBlock<mFreeBlocks.size())
      {
         failedLock = false;

         for(int i=nextFreeBlock; i<mFreeBlocks.size(); i++)
         {
             BlockDataInfo *info = mFreeBlocks[i];
             if (!info->mOwned && info->mMaxHoleSize>=inRequiredBytes)
             {
                // Acquire the zero-lock
                if (_hx_atomic_compare_exchange(&info->mZeroLock, 0, 1) == 0)
                {
                   // Acquire ownership...
                   if (info->mOwned)
                   {
                      // Someone else got it...
                      info->mZeroLock = 0;
                   }
                   else
                   {
                      info->mOwned = true;

                      // Increase the mNextFreeBlockOfSize
                      int idx = nextFreeBlock;
                      while(idx<mFreeBlocks.size() && mFreeBlocks[idx]->mOwned)
                      {
                         _hx_atomic_compare_exchange(mNextFreeBlockOfSize+sizeSlot, idx, idx+1);
                         idx++;
                      }

                      if (sgThreadPoolJob==tpjAsyncZeroJit)
                      {
                         if (info->mZeroed==ZEROED_THREAD)
                            onZeroedBlockDequeued();
                         #ifdef PROFILE_THREAD_USAGE
                         else
                         {
                            if (!info->mZeroed)
                               _hx_atomic_add(&sThreadZeroMisses, 1);
                         }
                         #endif
                       }

                      return info;
                   }
                 }
                 else if (!info->mOwned)
                 {
                    // Zeroing thread is currently working on this block
                    // Go to next one or spin around again
                    failedLock = true;
                 }
             }
         }
      }

      return 0;
   }

   inline size_t GetWorkingMemory()
   {
       return ((size_t)mAllBlocks.size()) << IMMIX_BLOCK_BITS;
   }

   // Bytes handed out by the row allocator since the last collection.  MMTk's
   // Immix space triggers GC on exactly this ("allocation since last GC"),
   // which - unlike total heap usage - is not skewed by large objects.
   size_t RowsAllocatedSinceGC()
   {
      return (mCurrentRowsInUse > mRowsAtLastCollect ? mCurrentRowsInUse - mRowsAtLastCollect : 0)
             << IMMIX_LINE_BITS;
   }

   size_t LiveBytes()
   {
      return mRowsInUse << IMMIX_LINE_BITS;
   }

   // Making this function "virtual" is actually a (big) performance enhancement!
   // On the iphone, sjlj (set-jump-long-jump) exceptions are used, which incur a
   //  performance overhead.  It seems that the overhead in only in routines that call
   //  malloc/new.  This is not called very often, so the overhead should be minimal.
   //  However, gcc inlines this function!  requiring every alloc the have sjlj overhead.
   //  Making it virtual prevents the overhead.
   virtual bool AllocMoreBlocks(bool &outForceCompact, bool inJustBorrowing)
   {
      enum { newBlockCount = 1<<(IMMIX_BLOCK_GROUP_BITS) };

      #ifdef HXCPP_GC_MOVING
      if (!inJustBorrowing)
      {
         // Do compact next collect sooner
         if (sgTimeToNextTableUpdate>1)
         {
            #ifdef SHOW_FRAGMENTATION
              #ifdef SHOW_MEM_EVENTS_VERBOSE
                GCLOG("  alloc -> enable full collect\n");
              #endif
            #endif
            //sgTimeToNextTableUpdate = 1;
         }
      }
      #endif

      #if !defined(HXCPP_GC_BIG_BLOCKS) && !defined(HXCPP_GC_BLOCK_16K)
      // Currently, we only have 2 bytes for a block header
      if (mAllBlocks.size()+newBlockCount >= 0xfffe )
      {
         #if defined(SHOW_MEM_EVENTS) || defined(SHOW_FRAGMENTATION)
         GCLOG("Block id count used - collect");
         #endif
         // The problem is we are out of blocks, not out of memory
         outForceCompact = false;
         return false;
      }
      #endif

      // Find spare group...
      int gid = -1;
      for(int i=0;i<gAllocGroups.size();i++)
         if (!gAllocGroups[i].alloc)
         {
            gid = i;
            break;
         }
      if (gid<0)
      {
         if (!gAllocGroups.safeReserveExtra(1))
         {
            outForceCompact = true;
            return false;
         }
         gid = gAllocGroups.next();
         gAllocGroups[gid].alloc = 0;
      }

      int n = 1<<IMMIX_BLOCK_GROUP_BITS;


      if (!mAllBlocks.safeReserveExtra(n) || !mFreeBlocks.hasExtraCapacity(n))
      {
         outForceCompact = true;
         return false;
      }

      char *chunk = (char *)HxAllocGCBlock( 1<<(IMMIX_BLOCK_GROUP_BITS + IMMIX_BLOCK_BITS) );
      if (!chunk)
      {
         //DebuggerTrap();
         #ifdef SHOW_MEM_EVENTS
         GCLOG("Alloc failed - try collect\n");
         #endif
         outForceCompact = true;
         return false;
      }

      char *aligned = (char *)( (((size_t)chunk) + IMMIX_BLOCK_SIZE-1) & IMMIX_BLOCK_BASE_MASK);
      if (aligned!=chunk)
         n--;
      gAllocGroups[gid].alloc = chunk;
      gAllocGroups[gid].blocks = n;
      gAllocGroups[gid].clear();

      int newSize = mFreeBlocks.size();
      {
         // The lazy sweep publishes blocks into the same list from other
         // threads; both sides must serialise their pushes.
         std::lock_guard<std::mutex> freeLock(mSweepLock);
         for(int i=0;i<n;i++)
         {
            BlockData *block = (BlockData *)(aligned + i*IMMIX_BLOCK_SIZE);
            BlockDataInfo *info = new BlockDataInfo(gid,block);

            mAllBlocks.push(info);
            mFreeBlocks.push(info);
         }
         std::stable_sort(&mAllBlocks[0], &mAllBlocks[0] + mAllBlocks.size(), SortByBlockPtr );
         mAllBlocksCount = mAllBlocks.size();
         for(int i=0;i<BLOCK_OFSIZE_COUNT;i++)
            mNextFreeBlockOfSize[i] = newSize;
      }

      #ifdef HXCPP_GC_VERIFY
      VerifyBlockOrder();
      #endif

      #if defined(SHOW_MEM_EVENTS_VERBOSE) || defined(SHOW_FRAGMENTATION_BLOCKS)
      if (inJustBorrowing)
      {
         GCLOG("Borrow Blocks %d = %d k\n", mAllBlocks.size(), (int)(GetWorkingMemory() >> 10));
      }
      else
      {
         GCLOG("Blocks %d = %d k\n", mAllBlocks.size(), (int)(GetWorkingMemory() >> 10));
      }
      #endif


      return true;
   }

   bool allowMoreBlocks()
   {
      #ifdef HXCPP_GC_GENERATIONAL
      return sGcMode==gcmFull;
      #else
      return true;
      #endif
   }

   void repoolReclaimedBlock(BlockDataInfo *block)
   {
      // The mMaxHoleSize has changed - possibly return to one of the pools
   }


   // Allocation-path poll, the same place MMTk checks for the next GC.  It
   // runs when a block is claimed, so the cycle starts before the free list
   // is empty and the background marker gets the remaining capacity to work
   // with.  Starting from the frame timer instead made every cycle an
   // emergency pause that paid for the whole mark.
   void PollIncremental()
   {
      // Do not start a cycle while the process is still booting: the class
      // tables and the thread set are not stable yet, and the first full
      // collection has not established the working-memory target.
      if (sGcFrameCount < 30)
         return;
      if (sgIncrementalActive || sgIsCollecting || hx::gPauseForCollect)
         return;
      if (sWorkingMemorySize < (size_t)hx::sgMinimumWorkingMemory)
         return;

      size_t liveRows = LiveBytes() >> IMMIX_LINE_BITS;
      size_t capRows = GetWorkingMemory() >> IMMIX_LINE_BITS;
      // Trigger when the allocation SINCE THE LAST GC COMPLETED has consumed
      // 75% of the free capacity that existed at that point, leaving 25% as
      // proportional headroom for the concurrent marker.  sRowsSinceCycle is
      // reset at cycle completion (MMTk's used_pages_after_last_gc
      // semantics), so it counts only fresh allocation and the live set must
      // NOT be added to the threshold - unlike the old start-reset formula,
      // where the counter re-counted the live rows every cycle.
      // Compared with MMTk ConcurrentImmix's total_pages >> 1, this fires a
      // little later while the heap has room (fewer cycle pauses) and
      // behaves proportionally when live approaches the capacity, instead of
      // MMTk's immediate back-to-back re-triggering.  A 25% variant (fires
      // 3x earlier) was A/B tested and was strictly worse: the per-cycle
      // fixed costs (begin setup + root re-scan + finish) do not shrink
      // with headroom, so tripling their frequency tripled the outliers,
      // including a 28.5ms finish drain when a burst collided with a cycle
      // closing during a marker budget slice.
      size_t thresholdRows = ((capRows - liveRows) * 3) >> 2;
      size_t minRows = (size_t)(8<<20) >> IMMIX_LINE_BITS;
      if (thresholdRows < minRows)
         thresholdRows = minRows;
      if (sRowsSinceCycle < thresholdRows)
         return;

      sHeapAtCycleStart = GetWorkingMemory();
      if (BeginIncremental())
         GCPerfLog("pacer-poll threshold=%d live=%d heap=%d target=%d",
            (int)thresholdRows, (int)LiveBytes(), (int)sHeapAtCycleStart, (int)sWorkingMemorySize);
   }

   BlockDataInfo *GetFreeBlock(int inRequiredBytes, hx::ImmixAllocator *inAlloc)
   {
      while(true)
      {
         BlockDataInfo *result = GetNextFree(inRequiredBytes);
         if (result)
         {
            result->zeroAndUnlock();

            // After zero/reclaim, it might be that the hole size is smaller than we thought.
            if (result->mMaxHoleSize>=inRequiredBytes)
            {
               mCurrentRowsInUse += result->GetFreeRows();
               sRowsSinceCycle += result->GetFreeRows();
               PollIncremental();
               return result;
            }

            repoolReclaimedBlock(result);
            continue;
         }

         if (hx::gPauseForCollect)
         {
            hx::PauseForCollect();
            continue;
         }

         #ifndef HXCPP_SINGLE_THREADED_APP
         hx::EnterGCFreeZone();
         gThreadStateChangeLock->lock();
         hx::ExitGCFreeZoneLocked();

         result = GetNextFree(inRequiredBytes);
         #endif

         bool forceCompact = false;
         // Lazy sweep first: the cycle may have ended but its rows have not
         // been reclaimed yet.  Reclaiming a block here costs microseconds
         // and keeps the allocator running instead of pausing the world.
         while (!result && SweepOneBlock())
            result = GetNextFree(inRequiredBytes);

         // An incremental cycle has no reclaimed rows yet, so let the heap
         // grow a little past its target - but only a little.  Growing
         // without a bound turns every long cycle into a larger heap, and
         // the next stop-the-world collection then has to scan it all.
         size_t growLimit = sWorkingMemorySize + (sWorkingMemorySize >> 1);
         size_t growCap = sWorkingMemorySize + (64<<20);
         if (growLimit > growCap)
            growLimit = growCap;
         bool incrementalGrow = hx::gIncrementalMarking && GetWorkingMemory()<growLimit;
         // GC-disabled loads used to grow without any bound here (a 3GB song
         // pushed the block heap to 2GB), and every later full collect then
         // had to scan all of it.  Keep the "no collects while disabled"
         // contract but bound the growth; past the bound a collect runs and
         // the shrink hands the memory back.
         bool disabledGrow = !sgInternalEnable &&
            GetWorkingMemory() < sWorkingMemorySize*2 + (256<<20);
         if (!result && allowMoreBlocks() && (disabledGrow || incrementalGrow || GetWorkingMemory()<sWorkingMemorySize))
         {
            if (AllocMoreBlocks(forceCompact,false))
               result = GetNextFree(inRequiredBytes);
         }

         if (!result)
         {
            inAlloc->SetupStackAndCollect(false,forceCompact,true,true);
            result = GetNextFree(inRequiredBytes);
         }

         if (!result && !forceCompact)
         {
            // Try with compact this time...
            forceCompact = true;
            inAlloc->SetupStackAndCollect(false,forceCompact,true,true);
            result = GetNextFree(inRequiredBytes);
         }

         if (!result)
         {
            if (AllocMoreBlocks(forceCompact,false))
               result = GetNextFree(inRequiredBytes);
         }

         if (!result && sgIncrementalActive && !gcBisectFlag("HXCPP_NO_FRAGFINISH"))
         {
            // Fragmented: every block has a hole smaller than the request, so
            // no amount of growing helps.  If the concurrent mark is already
            // done, closing the cycle now (a ~2ms finish pause) starts the
            // lazy sweep and reclaims the garbage WITHOUT the full
            // stop-the-world collect the old abort paid for (28-43ms in the
            // big-song log).  Only an unfinished mark falls back to the
            // abort, because waiting for it would stall the allocator.
            if (BackgroundMarkFinished())
            {
               GCPerfLog("incr-frag-finish size=%d blocks=%d free=%d wm=%d target=%d",
                  inRequiredBytes, (int)mAllBlocks.size(), (int)mFreeBlocks.size(),
                  (int)GetWorkingMemory(), (int)sWorkingMemorySize);
               FinishIncremental();
               while (!result && SweepOneBlock())
                  result = GetNextFree(inRequiredBytes);
            }
            if (!result)
            {
               GCPerfLog("incr-abort-frag size=%d blocks=%d free=%d wm=%d target=%d",
                  inRequiredBytes, (int)mAllBlocks.size(), (int)mFreeBlocks.size(),
                  (int)GetWorkingMemory(), (int)sWorkingMemorySize);
               AbortIncremental();
               inAlloc->SetupStackAndCollect(false,true,true,true);
               result = GetNextFree(inRequiredBytes);
            }
         }

         if (!result)
         {
            GCPerfLog("exhausted size=%d blocks=%d free=%d wm=%d target=%d incr=%d marking=%d",
               inRequiredBytes, (int)mAllBlocks.size(), (int)mFreeBlocks.size(),
               (int)GetWorkingMemory(), (int)sWorkingMemorySize,
               (int)sgIncrementalActive, (int)hx::gIncrementalMarking);
            GCLOG("Memory exhausted.\n");
            #ifndef HXCPP_M64
            GCLOG(" try 64 bit build.\n");
            #endif
            #ifndef HXCPP_GC_BIG_BLOCKS
            GCLOG(" try HXCPP_GC_BIG_BLOCKS.\n");
            #endif
            DebuggerTrap();
         }

         // Assume all wil be used
         mCurrentRowsInUse += result->GetFreeRows();
         sRowsSinceCycle += result->GetFreeRows();
         PollIncremental();

         #ifndef HXCPP_SINGLE_THREADED_APP
         gThreadStateChangeLock->unlock();
         #endif


         result->zeroAndUnlock();

         // After zero/reclaim, it might be that the hole size is smaller than we thought.
         if (result->mMaxHoleSize>=inRequiredBytes)
            return result;

         repoolReclaimedBlock(result);
      }
  }

   #if  defined(HXCPP_VISIT_ALLOCS) // {

  void MoveSpecial(hx::Object *inTo, hx::Object *inFrom, int size)
   {
      #ifdef HX_WATCH
      if (hxInWatchList(inFrom))
         GCLOG("****** watch MOVE from %p\n",inFrom);
      if (hxInWatchList(inTo))
         GCLOG("****** watch MOVE to %p\n",inTo);
      #endif
       // FinalizerList will get visited...

       hx::FinalizerMap::iterator i = hx::sFinalizerMap.find(inFrom);
       if (i!=hx::sFinalizerMap.end())
       {
          hx::finalizer f = i->second;
          hx::sFinalizerMap.erase(i);
          hx::sFinalizerMap[inTo] = f;
       }

       hx::HaxeFinalizerMap::iterator h = hx::sHaxeFinalizerMap.find(inFrom);
       if (h!=hx::sHaxeFinalizerMap.end())
       {
          hx::HaxeFinalizer f = h->second;
          hx::sHaxeFinalizerMap.erase(h);
          hx::sHaxeFinalizerMap[inTo] = f;
       }

       hx::MakeZombieSet::iterator mz = hx::sMakeZombieSet.find(inFrom);
       if (mz!=hx::sMakeZombieSet.end())
       {
          hx::sMakeZombieSet.erase(mz);
          hx::sMakeZombieSet.insert(inTo);
       }

       hx::ObjectIdMap::iterator id = hx::sObjectIdMap.find(inFrom);
       if (id!=hx::sObjectIdMap.end())
       {
          hx::sIdObjectMap[id->second] = inTo;
          hx::sObjectIdMap[inTo] = id->second;
          hx::sObjectIdMap.erase(id);
       }

       // Maybe do something faster with weakmaps

#ifdef HXCPP_TELEMETRY
       //printf(" -- moving %018x to %018x, size %d\n", inFrom, inTo, size);
       __hxt_gc_realloc(inFrom, inTo, size);
#endif

   }



   bool MoveBlocks(MoveBlockJob &inJob,BlockDataStats &ioStats)
   {
      BlockData *dest = 0;
      BlockDataInfo *destInfo = 0;
      unsigned int *destStarts = 0;
      int hole = -1;
      int holes = 0;
      int destPos = 0;
      int destLen = 0;

      int moveObjs = 0;
      int clearedBlocks = 0;

      while(true)
      {
         BlockDataInfo *from = inJob.getFrom();
         if (!from)
            break;
         if (from->calcFragScore()>FRAG_THRESH)
            ioStats.fraggedBlocks--;
         ioStats.rowsInUse -= from->mUsedRows;
         if (!from->isEmpty())
            ioStats.emptyBlocks ++;

         unsigned int *allocStart = from->allocStart;
         #ifdef SHOW_MEM_EVENTS
         //GCLOG("Move from %p (%d x %d)\n", from, from->mUsedRows, from->mHoles );
         #endif

         const unsigned char *rowMarked = from->mPtr->mRowMarked;
         for(int r=IMMIX_HEADER_LINES;r<IMMIX_LINES;r++)
         {
            if (rowMarked[r])
            {
               unsigned int starts = allocStart[r];
               if (!starts)
                  continue;
               for(int i=0;i<32;i++)
               {
                  if ( starts & (1<<i))
                  {
                     unsigned int *row = (unsigned int *)from->mPtr->mRow[r];
                     unsigned int &header = row[i];

                     if ((header&IMMIX_ALLOC_MARK_ID) == hx::gMarkID)
                     {
                        int size = ((header & IMMIX_ALLOC_SIZE_MASK) >> IMMIX_ALLOC_SIZE_SHIFT);
                        int allocSize = size + sizeof(int);

                        while(allocSize + ALIGN_PADDING(destPos)>destLen)
                        {
                           hole++;
                           if (hole<holes)
                           {
                              destPos = destInfo->mRanges[hole].start;
                              destLen = destInfo->mRanges[hole].length;
                           }
                           else
                           {
                              if (destInfo)
                                 destInfo->makeFull();
                              do
                              {
                                 destInfo = inJob.getTo();
                                 if (!destInfo)
                                    goto all_done;
                              } while(destInfo->mHoles==0);


                              ioStats.rowsInUse += IMMIX_USEFUL_LINES - destInfo->mUsedRows;
                              //destInfo->zero();
                              dest = destInfo->mPtr;
                              destStarts = destInfo->allocStart;

                              hole = 0;
                              holes = destInfo->mHoles;
                              destPos = destInfo->mRanges[hole].start;
                              destLen = destInfo->mRanges[hole].length;
                           }
                        }

                        #ifdef HXCPP_ALIGN_ALLOC
                        destPos += ALIGN_PADDING(destPos);
                        #endif

                        int startRow = destPos>>IMMIX_LINE_BITS;

                        destStarts[ startRow ] |= hx::gImmixStartFlag[destPos&127];

                        unsigned int *buffer = (unsigned int *)((char *)dest + destPos);

                        unsigned int headerPreserve = header & IMMIX_HEADER_PRESERVE;

                        int end = destPos + allocSize;

                        *buffer++ =  (( (end+(IMMIX_LINE_LEN-1))>>IMMIX_LINE_BITS) -startRow) |
                                        (size<<IMMIX_ALLOC_SIZE_SHIFT) |
                                        headerPreserve |
                                        hx::gMarkID;
                        destPos = end;
                        destLen -= allocSize;

                        unsigned int *src = row + i + 1;

                        MoveSpecial((hx::Object *)buffer,(hx::Object *)src, size);

                        // Result has moved - store movement in original position...
                        memcpy(buffer, src, size);
                        //GCLOG("   move %p -> %p %d (%08x %08x )\n", src, buffer, size, buffer[-1], buffer[1] );

                        *(unsigned int **)src = buffer;
                        header = IMMIX_OBJECT_HAS_MOVED;
                        moveObjs++;

                        starts &= ~(1<<i);
                        if (!starts)
                           break;
                     }
                  }
               }
            }
         }

         all_done:
         if (destInfo)
         {
            // Still have space, which means from finished.
            destInfo->makeFull();
            from->clear();
            clearedBlocks++;
            // Could remove some used rows from stats
         }
         else
         {
            // Partialy cleared, then ran out of to blocks - remove from allocation this round
            if (from)
            {
               // Could maybe be a bit smarter here
               ioStats.rowsInUse += from->mUsedRows;
               from->makeFull();
            }
         }
      }

      #ifdef SHOW_FRAGMENTATION
      GCLOG("Moved %d objects (%d/%d blocks)\n", moveObjs, clearedBlocks, mAllBlocks.size());
      #endif

      if (moveObjs)
      {
         AdjustPointers(0);
      }


      return moveObjs;
   }

   void AdjustPointers(hx::QuickVec<hx::Object *> *inRemembered)
   {
      class AdjustPointer : public hx::VisitContext
      {
         GlobalAllocator *mAlloc;
      public:
         AdjustPointer(GlobalAllocator *inAlloc) : mAlloc(inAlloc) {  }

         void visitObject(hx::Object **ioPtr) HXCPP_OVERRIDE
         {
            if ( ((*(unsigned int **)ioPtr)[-1]) == IMMIX_OBJECT_HAS_MOVED )
            {
               //GCLOG("  patch object to  %p -> %p\n", *ioPtr,  (*(hx::Object ***)ioPtr)[0]);
               *ioPtr = (*(hx::Object ***)ioPtr)[0];
               //GCLOG("    %08x %08x ...\n", ((int *)(*ioPtr))[0], ((int *)(*ioPtr))[1] );
            }
         }

         void visitAlloc(void **ioPtr) HXCPP_OVERRIDE
         {
            if ( ((*(unsigned int **)ioPtr)[-1]) == IMMIX_OBJECT_HAS_MOVED )
            {
               //GCLOG("  patch reference to  %p -> %p\n", *ioPtr,  (*(void ***)ioPtr)[0]);
               *ioPtr = (*(void ***)ioPtr)[0];
               //GCLOG("    %08x %08x ...\n", ((int *)(*ioPtr))[0], ((int *)(*ioPtr))[1] );
            }
         }
      };


      AdjustPointer adjust(this);
      VisitAll(&adjust,true, inRemembered);
   }


   #ifdef HXCPP_GC_GENERATIONAL
   BlockDataInfo *getNextBlockWithoutSurvivors(int &ioPosition)
   {
      while(ioPosition<mAllBlocks.size())
      {
         BlockDataInfo *b = mAllBlocks[ioPosition++];
         if (b->mHoles>0 && !b->mHasSurvivor)
            return b;
      }
      return 0;
   }

 

   int MoveSurvivors(hx::QuickVec<hx::Object *> *inRemembered)
   {
      int sourceScan = 0;
      int destScan = 0;
      int moveObjs = 0;
      int clearedBlocks = 0;

      BlockDataInfo *destInfo = 0;
      BlockData *dest = 0;
      int destHole = 0;
      int destPos = 0;
      int destLen = 0;
      unsigned int *destStarts = 0;

      BlockDataInfo *from = 0;

      int tested = 0;

      int all = mAllBlocks.size();
      for(int srcBlock=0; srcBlock<all; srcBlock++)
      {
         from = mAllBlocks[srcBlock];
         if (from->mPinned || !from->mHasSurvivor)
         {
            from = 0;
            continue;
         }
         tested++;
         unsigned int *srcStart = from->allocStart;

         // Scan nursery for survivors
         for(int hole = 0; hole<from->mHoles; hole++)
         {
            int start = from->mRanges[hole].start;
            int len = from->mRanges[hole].length;
            int startRow = start >> IMMIX_LINE_BITS;
            int end = startRow + (len >> IMMIX_LINE_BITS);
            for(int r = startRow; r<end;r++)
            {
               unsigned int &startFlags = srcStart[r];
               if (startFlags)
               {
                  for(int loc=0;loc<32;loc++)
                     if (startFlags & (1<<loc))
                     {
                        unsigned int *row = (unsigned int *)from->mPtr->mRow[r];
                        unsigned int &header = row[loc];

                        if ((header&IMMIX_ALLOC_MARK_ID) == hx::gMarkID)
                        {
                           int size = ((header & IMMIX_ALLOC_SIZE_MASK) >> IMMIX_ALLOC_SIZE_SHIFT);
                           int allocSize = size + sizeof(int);

                           // Find dest reqion ...
                           while(destHole==0 || destLen < ALIGN_PADDING(destPos) + allocSize)
                           {
                              if (destHole==0)
                              {
                                 if (destInfo)
                                    destInfo->makeFull();
                                 destInfo = getNextBlockWithoutSurvivors(destScan);
                                 if (!destInfo)
                                    goto no_more_moves;

                                 destHole = -1;
                                 destLen = 0;
                              }
                              if (destLen + ALIGN_PADDING(0)<allocSize)
                              {
                                 destHole++;
                                 if (destHole>=destInfo->mHoles)
                                    destHole = 0;
                                 else
                                 {
                                    dest = destInfo->mPtr;
                                    destPos = destInfo->mRanges[destHole].start;
                                    destLen = destInfo->mRanges[destHole].length;
                                    destStarts = destInfo->allocStart;
                                 }
                              }
                           }

                           // TODO - not copy + paste

                        printf("Move!\n");
                           #ifdef HXCPP_ALIGN_ALLOC
                           destPos += ALIGN_PADDING(destPos);
                           #endif

                           int startRow = destPos>>IMMIX_LINE_BITS;

                           destStarts[ startRow ] |= hx::gImmixStartFlag[destPos&127];

                           unsigned int *buffer = (unsigned int *)((char *)dest + destPos);

                           unsigned int headerPreserve = header & IMMIX_HEADER_PRESERVE;

                           int end = destPos + allocSize;

                           *buffer++ =  (( (end+(IMMIX_LINE_LEN-1))>>IMMIX_LINE_BITS) -startRow) |
                                           (size<<IMMIX_ALLOC_SIZE_SHIFT) |
                                           headerPreserve |
                                           hx::gMarkID;
                           destPos = end;
                           destLen -= allocSize;

                           unsigned int *src = row + loc + 1;

                           MoveSpecial((hx::Object *)buffer,(hx::Object *)src, size);

                           // Result has moved - store movement in original position...
                           memcpy(buffer, src, size);
                           //GCLOG("   move %p -> %p %d (%08x %08x )\n", src, buffer, size, buffer[-1], buffer[1] );

                           *(unsigned int **)src = buffer;
                           header = IMMIX_OBJECT_HAS_MOVED;
                           moveObjs++;

                           startFlags &= ~(1<<loc);
                           if (!startFlags)
                              break;
                        }
                     }
               }
            }
         }

         no_more_moves:
            if (destInfo)
            {
               destInfo->makeFull();
               clearedBlocks++;
            }
            else
            {
               // Partialy cleared, then ran out of to blocks - remove from allocation this round
               if (from && moveObjs)
               {
                  // Could maybe be a bit smarter here
                  //ioStats.rowsInUse += from->mUsedRows;
                  from->makeFull();
               }
            }
      }

      #ifdef SHOW_FRAGMENTATION
      //GCLOG("Compacted nursery %d objects (%d/%d blocks)\n", moveObjs, clearedBlocks, mAllBlocks.size());
      #endif

      if (moveObjs)
      {
         AdjustPointers(inRemembered);
      }

      return moveObjs;
   }
   #endif

   // MMTk's shrink, implemented without per-block erase: release whole empty
   // block groups and rebuild the block list in one pass.  releaseEmptyGroups
   // erases one block at a time, which is O(n^2) on a heap with tens of
   // thousands of blocks.
   size_t ShrinkBlocks(BlockDataStats &outStats, size_t releaseSize)
   {
      for(int i=0;i<gAllocGroups.size();i++)
         gAllocGroups[i].isEmpty = true;
      // Owned blocks hold live mutator data even when their row counters are
      // stale (the sweep skips owned blocks without updating mUsedRows), so
      // their groups must never be marked empty - releasing such a group
      // frees live data (the Hash::query crash).
      for(int i=0;i<mAllBlocks.size();i++)
      {
         BlockDataInfo *info = mAllBlocks[i];
         if (!info->isEmpty() || info->mOwned)
            gAllocGroups[info->mGroupId].isEmpty = false;
      }

      size_t released = 0;
      for(int i=0;i<gAllocGroups.size() && released<releaseSize;i++)
      {
         GroupInfo &g = gAllocGroups[i];
         if (g.alloc && g.isEmpty && !g.pinned)
         {
            size_t bytes = g.blocks << IMMIX_BLOCK_BITS;
            // Async OS release: VirtualFree of hundreds of MB measured tens of
            // ms inside this pause (gc_perf.log "stats" time).  Nothing below
            // references the group memory any more.
            QueueBlockGroupFree(g.alloc);
            g.alloc = 0;
            released += bytes;
         }
      }

      if (!released)
         return 0;


      // The compaction pass below deletes the BlockDataInfo of every
      // released group (destroy() is "delete this").  createFreeList pushes
      // fully-empty blocks into mFreeBlocks and backgroundProcessFreeList
      // copies that list into mZeroList, so without filtering, both hold
      // dangling pointers and the next GetNextFree dereferences freed
      // metadata (upstream releaseEmptyGroups has the same hole - it just
      // never fires with upstream heap sizes).  Filter the free list FIRST,
      // while every info is still alive, and rebuild the per-size-class
      // index array exactly like createFreeList does.  The relative order of
      // surviving entries is still the sorted one, so the removal preserves
      // SmallestFreeFirst.
      int fWrite = 0;
      for(int i=0;i<mFreeBlocks.size();i++)
      {
         BlockDataInfo *info = mFreeBlocks[i];
         if (gAllocGroups[info->mGroupId].alloc)
            mFreeBlocks[fWrite++] = info;
      }
      mFreeBlocks.setSize(fWrite);
      for(int i=0;i<BLOCK_OFSIZE_COUNT;i++)
         mNextFreeBlockOfSize[i] = fWrite;
      for(int i=fWrite-1;i>=0;i--)
      {
         int slot = mFreeBlocks[i]->mMaxHoleSize >> IMMIX_LINE_BITS;
         if (slot>=BLOCK_OFSIZE_COUNT)
            slot = BLOCK_OFSIZE_COUNT-1;
         mNextFreeBlockOfSize[slot] = i;
      }
      for(int i=BLOCK_OFSIZE_COUNT-2;i>=0;i--)
         if (mNextFreeBlockOfSize[i]>mNextFreeBlockOfSize[i+1])
            mNextFreeBlockOfSize[i] = mNextFreeBlockOfSize[i+1];
      // The zero list holds copies of the old free list; async zero jobs are
      // stopped during this pause.  Clear both sides of the handshake - the
      // next backgroundProcessFreeList rebuilds it from the filtered list.
      mZeroList.clear();
      mZeroListQueue = 0;

      int write = 0;
      for(int i=0;i<mAllBlocks.size();i++)
      {
         BlockDataInfo *info = mAllBlocks[i];
         if (!gAllocGroups[info->mGroupId].alloc)
         {
            if (outStats.emptyBlocks > 0)
               outStats.emptyBlocks--;
            info->destroy();
         }
         else
            mAllBlocks[write++] = info;
      }
      mAllBlocks.setSize(write);
      return released;
   }

   int releaseEmptyGroups(BlockDataStats &outStats, size_t releaseSize)
   {
      int released=0;
      int groups=0;
      for(int i=0; i<mAllBlocks.size(); i++ )
      {
         // Owned blocks hold live mutator data even when the row counters
         // are stale - never mark their group empty (same hole as
         // ShrinkBlocks, same defensive guard).
         if (!mAllBlocks[i]->isEmpty() || mAllBlocks[i]->mOwned)
             gAllocGroups[mAllBlocks[i]->mGroupId].isEmpty=false;
      }

      #ifdef HXCPP_GC_VERIFY
      typedef std::pair< void *, void * > ReleasedRange;
      std::vector<ReleasedRange> releasedRange;
      std::vector<int> releasedGids;
      #endif

      for(int i=0;i<gAllocGroups.size();i++)
      {
         GroupInfo &g = gAllocGroups[i];
         if (g.alloc && g.isEmpty && !g.pinned)
         {
            size_t groupBytes = g.blocks << (IMMIX_BLOCK_BITS);

            #ifdef SHOW_MEM_EVENTS_VERBOSE
            GCLOG("Release group %d: %p -> %p\n", i, g.alloc, g.alloc+groupBytes);
            #endif
            #ifdef HXCPP_GC_VERIFY
            releasedRange.push_back( ReleasedRange(g.alloc, g.alloc+groupBytes) );
            releasedGids.push_back(i);
            #endif

            HxFreeGCBlock(g.alloc);
            g.alloc = 0;

            groups++;

            if (groupBytes > releaseSize)
               break;

            releaseSize -= groupBytes;
         }
      }

      // The erase loop below deletes the BlockDataInfo of released groups;
      // filter the free list first (see ShrinkBlocks - same dangling
      // pointer, upstream hole).
      {
         int fWrite = 0;
         for(int i=0;i<mFreeBlocks.size();i++)
         {
            BlockDataInfo *info = mFreeBlocks[i];
            if (gAllocGroups[info->mGroupId].alloc)
               mFreeBlocks[fWrite++] = info;
         }
         mFreeBlocks.setSize(fWrite);
         for(int i=0;i<BLOCK_OFSIZE_COUNT;i++)
            mNextFreeBlockOfSize[i] = fWrite;
         for(int i=fWrite-1;i>=0;i--)
         {
            int slot = mFreeBlocks[i]->mMaxHoleSize >> IMMIX_LINE_BITS;
            if (slot>=BLOCK_OFSIZE_COUNT)
               slot = BLOCK_OFSIZE_COUNT-1;
            mNextFreeBlockOfSize[slot] = i;
         }
         for(int i=BLOCK_OFSIZE_COUNT-2;i>=0;i--)
            if (mNextFreeBlockOfSize[i]>mNextFreeBlockOfSize[i+1])
               mNextFreeBlockOfSize[i] = mNextFreeBlockOfSize[i+1];
         mZeroList.clear();
         mZeroListQueue = 0;
      }

      // Release blocks
      for(int i=0; i<mAllBlocks.size();  )
      {
         if (!gAllocGroups[mAllBlocks[i]->mGroupId].alloc)
         {
            outStats.emptyBlocks--;
            released++;
            mAllBlocks[i]->destroy();
            mAllBlocks.erase(i);
         }
         else
         {
            #ifdef HXCPP_GC_VERIFY
            for(int g=0;g<releasedGids.size();g++)
               if (mAllBlocks[i]->mGroupId == releasedGids[g])
               {
                  printf("Group %d should be released.\n", mAllBlocks[i]->mGroupId);
                  DebuggerTrap();
               }
            #endif
            i++;
         }
      }

      #ifdef HXCPP_GC_VERIFY
      for(int i=0;i<mAllBlocks.size();i++)
      {
         BlockDataInfo *info = mAllBlocks[i];
         void *ptr = info->mPtr;
         for(int r=0;r<releasedRange.size();r++)
         if ( ptr>=releasedRange[r].first && ptr<releasedRange[r].second )
         {
            printf("Released block %p(%d:%p) still in list\n", info, info->mId, info->mPtr );
            DebuggerTrap();
         }
      }

      VerifyBlockOrder();
      #endif


      #if defined(SHOW_MEM_EVENTS) || defined(SHOW_FRAGMENTATION)
      GCLOG("Release %d blocks, %d groups,  %s\n", released, groups, formatBytes((size_t)released<<(IMMIX_BLOCK_BITS)).c_str());
      #endif
      return released;
   }


   void calcMoveOrder()
   {
      for(int i=0;i<gAllocGroups.size();i++)
         gAllocGroups[i].clear();

      for(int i=0; i<mAllBlocks.size(); i++ )
      {
         BlockDataInfo &block = *mAllBlocks[i];
         GroupInfo &g = gAllocGroups[block.mGroupId];
         if (block.mPinned)
            g.pinned = true;
         g.usedBytes += block.mUsedBytes;
         g.usedSpace += block.mUsedRows<<IMMIX_LINE_BITS;
      }

      for(int i=0; i<mAllBlocks.size(); i++ )
      {
         BlockDataInfo &block = *mAllBlocks[i];
         GroupInfo &g = gAllocGroups[block.mGroupId];
         // Base on group wasted space (when not pinned)
         block.mMoveScore = g.getMoveScore();
      }
   }

   #endif // } defined(HXCPP_VISIT_ALLOCS)
 
   void *GetIDObject(int inIndex)
   {
      std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
      if (inIndex<0 || inIndex>hx::sIdObjectMap.size())
         return 0;
      return hx::sIdObjectMap[inIndex];
   }

   int GetObjectID(void * inPtr)
   {
      std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
      hx::ObjectIdMap::iterator i = hx::sObjectIdMap.find( (hx::Object *)inPtr );
      if (i!=hx::sObjectIdMap.end())
         return i->second;

      int id = 0;
      if (hx::sFreeObjectIds.size()>0)
      {
         id = hx::sFreeObjectIds.pop();
      }
      else
      {
         id = hx::sObjectIdMap.size();
         hx::sIdObjectMap.push(0);
      }
      hx::sObjectIdMap[(hx::Object *)inPtr] = id;
      hx::sIdObjectMap[id] = (hx::Object *)inPtr;
      return id;
   }


   void ClearRowMarks()
   {
      for(int i=0;i<mAllBlocks.size();i++)
         mAllBlocks[i]->clearRowMarks();
   }


   void ClearBlockMarks()
   {
      for(int i=0;i<mAllBlocks.size();i++)
         mAllBlocks[i]->clearBlockMarks();
   }

   #ifdef HXCPP_VISIT_ALLOCS
   void VisitAll(hx::VisitContext *inCtx,bool inMultithread = false,hx::QuickVec<hx::Object *> *inRemembered = 0)
   {
      if (inRemembered)
      {
         int n = inRemembered->size();
         for(int i=0;i<n;i++)
            (*inRemembered)[i]->__Visit(inCtx);
      }
      else if (MAX_GC_THREADS>1 && inMultithread && mAllBlocks.size())
      {
         sThreadVisitContext = inCtx;
         StartThreadJobs(tpjVisitBlocks, mAllBlocks.size(), true);
         sThreadVisitContext = 0;
      }
      else
         for(int i=0;i<mAllBlocks.size();i++)
            mAllBlocks[i]->VisitBlock(inCtx);

      for(int i=0;i<mLocalAllocs.size();i++)
         VisitLocalAlloc(mLocalAllocs[i], inCtx);

      hx::VisitClassStatics(inCtx);

      for(hx::RootSet::iterator i = hx::sgRootSet.begin(); i!=hx::sgRootSet.end(); ++i)
      {
         hx::Object **obj = *i;
         if (*obj)
            inCtx->visitObject(obj);
      }


      if (hx::sgOffsetRootSet)
         for(hx::OffsetRootSet::iterator i = hx::sgOffsetRootSet->begin(); i!=hx::sgOffsetRootSet->end(); ++i)
         {
            char *ptr = *(char **)(i->first);
            int offset = i->second;
            hx::Object *obj = (hx::Object *)(ptr - offset);

            if (obj)
            {
               hx::Object *obj0 = obj;
               inCtx->visitObject(&obj);
               if (obj!=obj0)
                  *(char **)(i->first) = (char *)(obj) + offset;
            }
         }

      if (hx::sgFinalizers)
         for(int i=0;i<hx::sgFinalizers->size();i++)
            (*hx::sgFinalizers)[i]->Visit(inCtx);

      for(int i=0;i<hx::sFinalizableList.size();i++)
         inCtx->visitAlloc( &hx::sFinalizableList[i].base );

      for(int i=0;i<hx::sZombieList.size();i++)
         inCtx->visitObject( &hx::sZombieList[i] );

      for(int i=0;i<hx::sWeakRefs.size(); i++)
         inCtx->visitObject( (hx::Object **) &hx::sWeakRefs[i] );

      for(int i=0;i<hx::sWeakHashList.size();i++)
         inCtx->visitObject( (hx::Object **) &hx::sWeakHashList[i] );

   }

   #endif

   void ReclaimAsync(BlockDataStats &outStats)
   {
      while(!sgThreadPoolAbort)
      {
         int blockId = _hx_atomic_add(&mThreadJobId, 1);
         if (blockId>=mAllBlocks.size())
            break;

         if ( sgThreadPoolJob==tpjReclaimFull)
            mAllBlocks[blockId]->reclaim<true>(&outStats);
         else
            mAllBlocks[blockId]->reclaim<false>(&outStats);
      }
   }

   void CountAsync(BlockDataStats &outStats)
   {
      while(!sgThreadPoolAbort)
      {
         int blockId = _hx_atomic_add(&mThreadJobId, 1);
         if (blockId>=mAllBlocks.size())
            break;

         mAllBlocks[blockId]->countRows(outStats);
      }
   }


   void GetStatsAsync(BlockDataStats &outStats)
   {
      while(!sgThreadPoolAbort)
      {
         int blockId = _hx_atomic_add(&mThreadJobId, 1);
         if (blockId>=mAllBlocks.size())
            break;

         mAllBlocks[blockId]->getStats( outStats );
      }
   }

   void ClearRowMarksAsync()
   {
      while(!sgThreadPoolAbort)
      {
         int blockId = _hx_atomic_add(&mThreadJobId, 1);
         if (blockId>=mAllBlocks.size())
            break;

         mAllBlocks[blockId]->clearRowMarks();
      }
   }

   // Finish-phase root scan: each worker conservative-scans the captured
   // stacks/registers of the paused mutator threads.  The captured state is
   // frozen (all mutators are parked at a safepoint) and each worker's
   // MarkContext keeps its pushes thread-local until releaseJobs publishes
   // them for the mark drain.
   void StackScanAsync(hx::MarkContext &inCtx)
   {
      // The previous drain released this context's chunk (marking==0) - the
      // main thread's mMarker always re-arms via init() before marking, and
      // so must a pool context before any direct pushObj.
      inCtx.init();
      while(!sgThreadPoolAbort)
      {
         int allocId = _hx_atomic_add(&mThreadJobId, 1);
         if (allocId>=mLocalAllocs.size())
            break;

         MarkLocalAlloc(mLocalAllocs[allocId], &inCtx);
      }

      inCtx.releaseJobs();
   }



   #ifdef HXCPP_VISIT_ALLOCS
   void VisitBlockAsync(hx::VisitContext *inCtx)
   {
      while(!sgThreadPoolAbort)
      {
         int blockId = _hx_atomic_add(&mThreadJobId, 1);
         if (blockId>=mAllBlocks.size())
            break;

         mAllBlocks[blockId]->VisitBlock(inCtx);
      }
   }
   #endif


   void ZeroAsync()
   {
      while(!sgThreadPoolAbort)
      {
         int zeroListId = _hx_atomic_add(&mThreadJobId, 1);
         if (zeroListId>=mZeroList.size())
            break;

         BlockDataInfo *info = mZeroList[zeroListId];
         info->tryZero();
      }
   }

   bool ZeroAsyncJit()
   {
      int spinCount = 0;
      while(!sgThreadPoolAbort)
      {
         if (mZeroListQueue>=sMaxZeroQueueSize)
         {
            spinCount++;
            if (spinCount<10000)
               // Spin
               continue;
            // Full for now, so sleep...
            return true;
         }
         spinCount = 0;

         // Look at next block...
         int zeroListId = _hx_atomic_add(&mThreadJobId, 1);
         if (zeroListId>=mZeroList.size())
         {
            // Done, so sleep...
            return true;
         }

         BlockDataInfo *info = mZeroList[zeroListId];
         if (info->tryZero())
         {
            // We zeroed it, so increase queue count
            _hx_atomic_add(&mZeroListQueue, 1);
            #ifdef PROFILE_THREAD_USAGE
            sThreadBlockZeroCount++;
            #endif
         }
      }

      return true;
   }

   // Try to maintain between sMinZeroQueueSize and sMaxZeroQueueSize pre-zeroed blocks
   void onZeroedBlockDequeued()
   {
      // Wake the thread?
      if (_hx_atomic_sub(&mZeroListQueue, 1)<sMinZeroQueueSize && !sRunningThreads)
      {
         if (mZeroListQueue + mThreadJobId < mZeroList.size())
         {
            // Wake zeroing thread
            std::lock_guard<std::mutex> l(sThreadPoolLock);
            if (!(sRunningThreads & 0x01))
            {
               #ifdef PROFILE_THREAD_USAGE
               sThreadZeroPokes++;
               #endif
               wakeThreadLocked(0);
            }
         }
      }
   }


   void finishThreadJob(int inId)
   {
      std::lock_guard<std::mutex> l(sThreadPoolLock);
      if (sRunningThreads & (1<<inId))
      {
         sRunningThreads &= ~(1<<inId);
         sLazyThreads = sRunningThreads != sAllThreads;

         if (!sRunningThreads)
            SignalThreadPool(sThreadJobDone,sThreadJobDoneSleeping);
      }
      else
      {
         printf("Finishe non-runnning thread?\n");
         DebuggerTrap();
      }
   }

   void waitForThreadWake(int inId)
   {
        std::lock_guard<std::mutex> l(sThreadPoolLock);
        int count = 0;

        // May be woken multiple times if sRunningThreads is set to 0 then 1 before we sleep
        sThreadSleeping[inId] = true;
        // Spurious wake?
        sThreadWake[inId]->wait(sThreadPoolLock, [&inId]() { return sRunningThreads & (1 << inId); });
        
        sThreadSleeping[inId] = false;
   }


   void ThreadLoop(int inId)
   {
      hx::MarkContext context(inId);

      while(true)
      {
         waitForThreadWake(inId);

         #ifdef HXCPP_GC_VERIFY
         if (! (sRunningThreads & (1<<inId)) )
            printf("Bad running threads!\n");
         #endif

         if (sgThreadPoolJob==tpjMark)
         {
            context.processMarkStack();
         }
         else if (sgThreadPoolJob==tpjAsyncZeroJit)
         {
            #ifdef PROFILE_THREAD_USAGE
            sThreadZeroWaits++;
            #endif
            if (ZeroAsyncJit())
               finishThreadJob(inId);
         }
         else
         {
            if (sgThreadPoolJob==tpjReclaimFull || sgThreadPoolJob==tpjReclaim)
               ReclaimAsync(sThreadBlockDataStats[inId]);

            else if (sgThreadPoolJob==tpjCountRows)
               CountAsync(sThreadBlockDataStats[inId]);

            else if (sgThreadPoolJob==tpjGetStats)
               GetStatsAsync(sThreadBlockDataStats[inId]);

            #ifdef HXCPP_VISIT_ALLOCS
            else if (sgThreadPoolJob==tpjVisitBlocks)
               VisitBlockAsync(sThreadVisitContext);
            #endif

            else if (sgThreadPoolJob==tpjAsyncZero)
               ZeroAsync();

            else if (sgThreadPoolJob==tpjClearRowMarks)
               ClearRowMarksAsync();

            else if (sgThreadPoolJob==tpjStackScan)
               StackScanAsync(context);

            finishThreadJob(inId);
         }
      }
   }

   static THREAD_FUNC_TYPE SThreadLoop( void *inInfo )
   {
      sGlobalAlloc->ThreadLoop((int)(size_t)inInfo);
      THREAD_FUNC_RET;
   }

   void CreateWorker(int inId)
   {
      void *info = (void *)(size_t)inId;

      #if defined(__EMSCRIPTEN__)
         // Only one thread
      #else
         sThreadWake[inId] = new std::condition_variable_any();
         if (0 == inId)
         {
             sThreadJobDone = new std::condition_variable_any();
         }

         sThreadSleeping[inId] = false;

         HxCreateDetachedThread(SThreadLoop, info);
      #endif
   }

   void StopThreadJobs(bool inKill)
   {
      bool maybeExtraWake = false;

      if (sAllThreads)
      {
         if (inKill)
         {
            sgThreadPoolAbort = true;
            if (sgThreadPoolJob==tpjAsyncZeroJit)
            {
               std::lock_guard<std::mutex> l(sThreadPoolLock);
               // Thread will be waiting, but not finished
               if (sRunningThreads & 0x1)
               {
                  sgThreadPoolJob = tpjNone;
                  maybeExtraWake = true;
                  wakeThreadLocked(0);
               }
            }
         }


         std::lock_guard<std::mutex> l(sThreadPoolLock);
         sThreadJobDoneSleeping = true;
         sThreadJobDone->wait(sThreadPoolLock, []() { return sRunningThreads == false; });
         sThreadJobDoneSleeping = false;
         sgThreadPoolAbort = false;
         sAllThreads = 0;
         sgThreadPoolJob = tpjNone;
         sLazyThreads = 0;
      }
   }


   void StartThreadJobs(ThreadPoolJob inJob, int inWorkers, bool inWait, int inThreadLimit = -1)
   {
      mThreadJobId = 0;

      if (!inWorkers)
         return;

      if (!sThreadPoolInit)
      {
         sThreadPoolInit = true;
         for(int i=0;i<MAX_GC_THREADS;i++)
            CreateWorker(i);
      }

      std::lock_guard<std::mutex> l(sThreadPoolLock);

      sgThreadPoolJob = inJob;

      sgThreadCount = inThreadLimit<0 ? MAX_GC_THREADS : std::min((int)MAX_GC_THREADS, inThreadLimit) ;

      int start = std::min(inWorkers, sgThreadCount );

      sAllThreads = (1<<sgThreadCount) - 1;

      sRunningThreads = (1<<start) - 1;

      sLazyThreads = sRunningThreads != sAllThreads;

      for(int i=0;i<start;i++)
         SignalThreadPool(sThreadWake[i],sThreadSleeping[i]);

      if (inWait)
      {
         // Join the workers...
         sThreadJobDoneSleeping = true;
         sThreadJobDone->wait(sThreadPoolLock, []() { return sRunningThreads == false; });
         sThreadJobDoneSleeping = false;

         sAllThreads = 0;
         sgThreadPoolJob = tpjNone;
         sLazyThreads = 0;

         if (sRunningThreads)
         {
            printf("Bad thread stop %d\n", sRunningThreads);
            DebuggerTrap();
         }
      }
   }


   #if defined(SHOW_FRAGMENTATION) || defined(SHOW_MEM_EVENTS)
   std::string formatBytes(size_t bytes)
   {
      size_t k = 1<<10;
      size_t meg = 1<<20;

      char strBuf[100];
      if (bytes<k)
         snprintf(strBuf,sizeof(strBuf),"%d", (int)bytes);
      else if (bytes<meg)
         snprintf(strBuf,sizeof(strBuf),"%.2fk", (double)bytes/k);
      else
         snprintf(strBuf,sizeof(strBuf),"%.2fmb", (double)bytes/meg);
      return strBuf;
   }
   #endif


   double tMarkInit;
   double tMarkLocal;
   double tMarkLocalEnd;
   double tMarked;
   void MarkAll(bool inGenerational)
   {
      double tM0 = __hxcpp_time_stamp();
      if (!inGenerational)
      {
         hx::gPrevByteMarkID = hx::gByteMarkID;

         // The most-significant header byte looks like:
         // C nH Odd Even  c c c c
         //  C = "is const alloc bit" - in this case Odd and Even will be false
         // nH = non-hashed const string bit
         // Odd = true if cycle is odd
         // Even = true if cycle is even
         // c c c c = 4 bit cycle code
         //
         hx::gPrevMarkIdMask = ((~hx::gMarkID) & 0x30000000) | HX_GC_CONST_ALLOC_BIT;

         // 4 bits of cycle
         gByteMarkID = (gByteMarkID + 1) & 0x0f;
         if (gByteMarkID & 0x1)
            gByteMarkID |= 0x20;
         else
            gByteMarkID |= 0x10;

         hx::gMarkID = gByteMarkID << 24;
         hx::gMarkIDWithContainer = (gByteMarkID << 24) | IMMIX_ALLOC_IS_CONTAINER;
         gRememberedByteMarkID = gByteMarkID | HX_GC_REMEMBERED;

         #ifdef HX_WATCH
         GCLOG(" non-gen mark byte -> %02x\n", hx::gByteMarkID);
         #endif
         gBlockStack = 0;

         // Parallel over the worker pool: a single-threaded pass over every
         // block cost 0.3-0.6ms of every begin/major pause.
         StartThreadJobs(tpjClearRowMarks, mAllBlocks.size(), true);
      }
      else
      {
         #ifdef HX_WATCH
         GCLOG(" generational mark byte -> %02x\n", hx::gByteMarkID);
         #endif
         ClearBlockMarks();
      }

      MEM_STAMP(tMarkInit);

      #ifdef PROFILE_THREAD_USAGE
      for(int i=-1;i<MAX_GC_THREADS;i++)
         sThreadChunkPushCount = sThreadChunkWakes = sThreadMarkCount[i] = sThreadArrayMarkCount[i] = 0;
      #endif



      mMarker.init();

      hx::MarkClassStatics(&mMarker);

      {
      hx::AutoMarkPush info(&mMarker,"Roots","root");

      for(hx::RootSet::iterator i = hx::sgRootSet.begin(); i!=hx::sgRootSet.end(); ++i)
      {
         hx::Object *&obj = **i;
         if (obj)
            hx::MarkObjectAlloc(obj , &mMarker );
      }

      if (hx::sgOffsetRootSet)
         for(hx::OffsetRootSet::iterator i = hx::sgOffsetRootSet->begin(); i!=hx::sgOffsetRootSet->end(); ++i)
         {
            char *ptr = *(char **)(i->first);
            int offset = i->second;
            hx::Object *obj = (hx::Object *)(ptr - offset);

            if (obj)
               hx::MarkObjectAlloc(obj , &mMarker );
         }
      } // automark

      #ifdef PROFILE_COLLECT
      hx::rootObjects = sObjectMarks;
      hx::rootAllocs = sAllocMarks;
      #endif


      {
      hx::AutoMarkPush info(&mMarker,"Zombies","zombie");
      // Mark zombies too....
      for(int i=0;i<hx::sZombieList.size();i++)
         hx::MarkObjectAlloc(hx::sZombieList[i] , &mMarker );
      } // automark

      MEM_STAMP(tMarkLocal);
      double tM1 = __hxcpp_time_stamp();
      hx::localCount = 0;

      mMarker.isGenerational = inGenerational;

      // Mark local stacks
      for(int i=0;i<mLocalAllocs.size();i++)
         MarkLocalAlloc(mLocalAllocs[i] , &mMarker);

      #ifdef PROFILE_COLLECT
      hx::localObjects = sObjectMarks;
      hx::localAllocs = sAllocMarks;
      #endif

      MEM_STAMP(tMarkLocalEnd);
      double tM2 = __hxcpp_time_stamp();

      #ifdef HX_MULTI_THREAD_MARKING
         mMarker.releaseJobs();

         // Unleash the workers...
         StartThreadJobs(tpjMark, MAX_GC_THREADS, true);
      #else
         mMarker.processMarkStack();
      #endif



      MEM_STAMP(tMarked);
      double tM3 = __hxcpp_time_stamp();

      hx::FindZombies(mMarker);

      // Weak-key hashes are ephemerons: a value is reachable only when both
      // the hash and its key are reachable. Values marked here may in turn
      // make keys in other weak hashes reachable, so iterate to a fixed point.
      bool markedWeakValue;
      do
      {
         markedWeakValue = false;
         mMarker.init();
         for(int i=0;i<hx::sWeakHashList.size();i++)
         {
            hx::HashRoot *hash = hx::sWeakHashList[i];
            if (hx::IsWeakRefValid(hash))
               markedWeakValue = hash->markWeakValues(&mMarker) || markedWeakValue;
         }
         if (markedWeakValue)
         {
            #ifdef HX_MULTI_THREAD_MARKING
            mMarker.releaseJobs();
            StartThreadJobs(tpjMark, MAX_GC_THREADS, true);
            #else
            mMarker.processMarkStack();
            #endif
         }
      }
      while(markedWeakValue);

      hx::RunFinalizers();
      double tM4 = __hxcpp_time_stamp();
      {
         int orphaned = hx::sGlobalChunks.pendingJobs();
         if (orphaned)
            GCPerfLog("GC-ORPHAN markall: %d mark chunks left undrained!", orphaned);
      }
      GCPerfLog("markall roots=%.3f locals=%.3f parallel=%.3f weakfin=%.3f stacks=%d",
         (tM1-tM0)*1000, (tM2-tM1)*1000, (tM3-tM2)*1000, (tM4-tM3)*1000,
         (int)mLocalAllocs.size());

      #ifdef HXCPP_GC_VERIFY
      for(int i=0;i<mAllBlocks.size();i++)
         mAllBlocks[i]->verify("After mark");
      #endif

      #ifdef HX_WATCH
      for(void **watch = hxWatchList; *watch; watch++)
      {
         GCLOG("********* Watch mark : %p %08x\n",*watch, ((unsigned int *)*watch)[-1]);
         GCLOG(" ******** is marked  : %d\n", (((unsigned char *)(*watch))[HX_ENDIAN_MARK_ID_BYTE]== gByteMarkID));
      }
      #endif
   }


   
   #ifdef HX_GC_VERIFY_ALLOC_START
   void verifyAllocStart()
   {
      for(int i=1;i<mAllBlocks.size();i++)
         mAllBlocks[i]->verifyAllocStart();
   }
   #endif

   #ifdef HXCPP_GC_VERIFY
   void VerifyBlockOrder()
   {
      for(int i=1;i<mAllBlocks.size();i++)
      {
         if ( mAllBlocks[i-1]->mPtr >= mAllBlocks[i]->mPtr)
         {
            printf("Bad block order block[%d]=%p >= block[%d]=%p / %d\n", i-1, mAllBlocks[i-1]->mPtr,
                    i, mAllBlocks[i]->mPtr, mAllBlocks.size() );
            DebuggerTrap();
         }
      }
   }
   #endif

   void Collect(bool inMajor, bool inForceCompact, bool inLocked,bool inFreeIsFragged)
   {
      // An incremental cycle owns the heap until it ends.  A collection
      // request arriving now means the allocator is out of rows (or external
      // memory grew), so close the cycle instead of returning without doing
      // anything: the sweep makes the reclaimed rows available right away.
      if (sgIncrementalActive)
      {
         if (inMajor)
         {
            // Close the cycle COMPLETELY - drain the mark and run the row
            // sweep to the end inside the finish pause (FinishIncremental
            // with inDrainSweep) - so the full collect below starts from a
            // quiescent heap.  The old abort path left stale remembered
            // chunks and half-swept state behind; combined with a sweep
            // running between the close and this collect it produced
            // dangling references (the clearMajor crash).
            GCPerfLog("collect-major-close-cycle major=%d compact=%d", (int)inMajor, (int)inForceCompact);
            // Close the cycle without aborting it: run ONE finish pause,
            // then help the lazy sweep along (the same locked SweepOneBlock
            // the allocation path uses) until the cycle has fully ended.
            // A mid-cycle abort would leave the remembered chunks and mark
            // chunks behind; draining them at the top of this STW section
            // makes that survivable, but a clean close keeps the heap
            // quiescent for the full collect below.
            int spins = 0;
            while (sgIncrementalActive)
            {
               if (SweepActive())
               {
                  // Help the lazy sweep (same locked call the allocation
                  // path makes).  A false return means the cursor is at the
                  // end - finalize the cycle now.
                  if (!SweepOneBlock())
                     FinishIncrementalSweepList();
               }
               else if (BackgroundMarkFinished() && !hx::gPauseForCollect)
                  FinishIncremental();
               else if (hx::gPauseForCollect)
                  hx::PauseForCollect();
               if (++spins > 4000000)
                  break;
               std::this_thread::yield();
            }
            if (sgIncrementalActive)
            {
               GCPerfLog("collect-major-abort-cycle major=%d compact=%d", (int)inMajor, (int)inForceCompact);
               AbortIncremental();
            }
         }
         else
         {
            // Do not wait for the cycle here: the finishing thread waits for
            // every mutator to reach a safepoint, so spinning on the cycle
            // flag would deadlock.  The caller reclaims rows lazily and the
            // frame tick closes the cycle once the marker is done.
            return;
         }
      }

      // Requests coming from the allocator (a block ran out) or from external
      // memory growth only need a collection, not a pause.  Start the
      // incremental cycle and let the frame tick finish it; major or
      // compacting requests still take the stop-the-world path below.
      // The very first collection still has to run to completion: it is the
      // one that computes the initial working-memory target, and the
      // allocator cannot grow past the 256k bootstrap value on its own.
      if (!inMajor && !inForceCompact && sgInternalEnable)
      {
         if (sWorkingMemorySize >= (size_t)hx::sgMinimumWorkingMemory && BeginIncremental())
         {
            #ifdef HXCPP_DEBUG
            GCPerfLog("collect-request redirected to incremental major=%d compact=%d locked=%d fragged=%d",
               (int)inMajor, (int)inForceCompact, (int)inLocked, (int)inFreeIsFragged);
            #endif
            return;
         }
         #ifdef HXCPP_DEBUG
         GCPerfLog("collect-request not-redirected major=%d compact=%d wm=%d min=%d incr=%d pause=%d",
            (int)inMajor, (int)inForceCompact, (int)sWorkingMemorySize,
            (int)hx::sgMinimumWorkingMemory, (int)sgIncrementalActive, (int)hx::gPauseForCollect);
         #endif
      }
      #ifdef HXCPP_DEBUG
      GCPerfLog("collect-slow-path major=%d compact=%d locked=%d fragged=%d wm=%d incr=%d pause=%d",
         (int)inMajor, (int)inForceCompact, (int)inLocked, (int)inFreeIsFragged,
         (int)sWorkingMemorySize, (int)sgIncrementalActive, (int)hx::gPauseForCollect);
      #endif

      PROFILE_COLLECT_SUMMARY_START;
      double tCollectEnter = __hxcpp_time_stamp();

      #ifndef HXCPP_SINGLE_THREADED_APP
      // If we set the flag from 0 -> 0xffffffff then we are the collector
      //  otherwise, someone else is collecting at the moment - so wait...
      if (_hx_atomic_compare_exchange((volatile int *)&hx::gPauseForCollect, 0, 0xffffffff) != 0)
      {
         if (inLocked)
         {
            gThreadStateChangeLock->unlock();

            hx::PauseForCollect();

            hx::EnterGCFreeZone();
            gThreadStateChangeLock->lock();
            hx::ExitGCFreeZoneLocked();
         }
         else
         {
            hx::PauseForCollect();
         }
         return;
      }
      #endif

      STAMP(t0)

      // We are the collector - all must wait for us
      LocalAllocator *this_local = 0;
      #ifndef HXCPP_SINGLE_THREADED_APP
      this_local = (LocalAllocator *)(hx::ImmixAllocator *)hx::tlsStackContext;

      if (!inLocked)
         gThreadStateChangeLock->lock();

      for(int i=0;i<mLocalAllocs.size();i++)
         if (mLocalAllocs[i]!=this_local)
            WaitForSafe(mLocalAllocs[i]);
      #endif

      sgIsCollecting = true;

      StopThreadJobs(true);
      #ifdef HXCPP_DEBUG
      sgAllocsSinceLastSpam = 0;
      #endif

      HX_STACK_FRAME("GC", "collect", 0, "GC::collect", __FILE__, __LINE__,0)
      #ifdef SHOW_MEM_EVENTS
      int here = 0;
      GCLOG("=== Collect === %p\n",&here);
      #endif


      #ifdef PROFILE_THREAD_USAGE
      GCLOG("Thread zero waits %d/%d/%d, misses=%d, hits=%d\n", sThreadZeroPokes, sThreadZeroWaits, mFreeBlocks.size(), sThreadZeroMisses, sThreadBlockZeroCount);
      sThreadZeroWaits = 0;
      sThreadZeroPokes = 0;
      sThreadZeroMisses = 0;
      sThreadBlockZeroCount = 0;
      #endif



      #ifdef HXCPP_TELEMETRY
      __hxt_gc_start();
      #endif

      size_t freeFraggedRows = 0;
      if (inFreeIsFragged)
      {
         for(int i=mNextFreeBlockOfSize[0]; i<mFreeBlocks.size(); i++)
            freeFraggedRows += mFreeBlocks[i]->GetFreeRows();
      }

      // Flush remembered-referrer chunks left behind by an aborted incremental
      // cycle into the mark list NOW, while the world is stopped and nothing
      // referenced inside has been freed.  The full mark below consumes them
      // like any other work.  Leaving them on the contexts was a use-after-free:
      // a thread stop / GC-free-zone entry pushed the stale chunk into the
      // global list, the objects inside died in this collect's sweep, and the
      // next mark dereferenced the freed memory (crash via clearMajor).
      #if defined(HXCPP_GC_GENERATIONAL) || defined(HXCPP_GC_INCREMENTAL)
      {
         for(int i=0;i<mLocalAllocs.size();i++)
         {
            hx::StackContext *ctx = (hx::StackContext *)mLocalAllocs[i];
            if (ctx->mOldReferrers)
            {
               if (ctx->mOldReferrers->count)
                  hx::sGlobalChunks.addLocked(ctx->mOldReferrers);
               else
                  hx::sGlobalChunks.free(ctx->mOldReferrers);
               ctx->mOldReferrers = 0;
            }
         }
         for(int i=0;i<LOCAL_POOL_SIZE;i++)
         {
            hx::StackContext *ctx = (hx::StackContext *)mLocalPool[i];
            if (ctx && ctx->mOldReferrers)
            {
               if (ctx->mOldReferrers->count)
                  hx::sGlobalChunks.addLocked(ctx->mOldReferrers);
               else
                  hx::sGlobalChunks.free(ctx->mOldReferrers);
               ctx->mOldReferrers = 0;
            }
         }
      }
      #endif

      // Now all threads have mTopOfStack & mBottomOfStack set.
      bool generational = false;

      #ifdef HXCPP_GC_GENERATIONAL
      bool compactSurviors = false;

      if (sGcMode==gcmGenerational)
      {
         for(int i=0;i<mLocalAllocs.size();i++)
         {
            hx::StackContext *ctx = (hx::StackContext *)mLocalAllocs[i];
            if( ctx->mOldReferrers->count )
                hx::sGlobalChunks.addLocked( ctx->mOldReferrers );
            else
                hx::sGlobalChunks.free( ctx->mOldReferrers );
            ctx->mOldReferrers = 0;
         }
      }

      hx::QuickVec<hx::Object *> rememberedSet;
      generational = !inMajor && !inForceCompact && sGcMode == gcmGenerational;
      if (sGcMode==gcmGenerational)
      {
         hx::sGlobalChunks.copyPointers(rememberedSet,!generational);
         #ifdef SHOW_MEM_EVENTS
         GCLOG("Patch remembered set marks %d\n", rememberedSet.size());
         #endif
         for(int i=0;i<rememberedSet.size();i++)
            ((unsigned char *)rememberedSet[i])[HX_ENDIAN_MARK_ID_BYTE] = gByteMarkID;
      }
      #endif

      STAMP(t1)

      MarkAll(generational);

      #ifdef HX_GC_VERIFY_GENERATIONAL
      {
         #ifdef SHOW_MEM_EVENTS
         GCLOG("verify generational [\n");
         #endif
         sGcVerifyGenerational = true;
         sgTimeToNextTableUpdate--;
         MarkAll(false);
         sGcVerifyGenerational = false;
         #ifdef SHOW_MEM_EVENTS
         GCLOG("] verify generational\n");
         #endif
      }
      #endif

      double tCollectMarked = __hxcpp_time_stamp();

      STAMP(t2)


      // Sweep blocks

      // Update table entries?  This needs to be done before the gMarkID count clocks
      //  back to the same number
      if (!generational)
         sgTimeToNextTableUpdate--;

      bool full = inMajor || (sgTimeToNextTableUpdate<=0) || inForceCompact;

      // Setup memory target ...
      // Count free rows, and prep blocks for sorting
      BlockDataStats stats;

      /*
       This reduces the stall time, but adds a bit of background cpu usage
       Might be good to just countRows for non-generational too
      */
      if (!full && generational)
      {
         countRows(stats);
         size_t currentRows = stats.rowsInUse + stats.fraggedRows + freeFraggedRows;
         double filled = (double)(currentRows) / (double)(mAllBlocks.size()*IMMIX_USEFUL_LINES);
         if (filled>0.85)
         {
            // Failure of generational estimation
            int retained = currentRows - mRowsInUse;
            int space = mAllBlocks.size()*IMMIX_USEFUL_LINES - mRowsInUse;
            if (space<retained)
               space = retained;
            if (space<1)
               space = 1;
            mGenerationalRetainEstimate = (double)retained/(double)space;
            #ifdef SHOW_MEM_EVENTS
            GCLOG("Generational retention/fragmentation too high %f, do normal collect\n", mGenerationalRetainEstimate);
            #endif

            #ifdef HX_GC_VERIFY_ALLOC_START
            verifyAllocStart();
            #endif

            generational = false;
            MarkAll(generational);

            sgTimeToNextTableUpdate--;
            full = sgTimeToNextTableUpdate<=0;

            stats.clear();
            reclaimBlocks(full,stats);
         }
      }
      else
      {
         reclaimBlocks(full,stats);
      }

      double tCollectReclaimed = __hxcpp_time_stamp();


      #ifdef HXCPP_GC_GENERATIONAL
      if (compactSurviors)
      {
         MoveSurvivors(&rememberedSet);
      }
      #endif


      #ifdef HXCPP_GC_MOVING
      if (!full)
      {
         double useRatio = (double)(mRowsInUse<<IMMIX_LINE_BITS) / (sWorkingMemorySize);
         #if defined(SHOW_FRAGMENTATION) || defined(SHOW_MEM_EVENTS)
            GCLOG("Row use ratio:%f\n", useRatio);
         #endif
         // Could be either expanding, or fragmented...
         if (useRatio>0.75)
         {
            #if defined(SHOW_FRAGMENTATION) || defined(SHOW_MEM_EVENTS)
               GCLOG("Do full stats\n", useRatio);
            #endif
            full = true;
            stats.clear();
            reclaimBlocks(full,stats);
         }
      }
      #endif

      if (full)
      {
         #ifdef HXCPP_GC_MOVING
         sgTimeToNextTableUpdate = 7;
         #else
         sgTimeToNextTableUpdate = 15;
         #endif
      }

      size_t oldRowsInUse = mRowsInUse;
      mRowsInUse = stats.rowsInUse + stats.fraggedRows + freeFraggedRows;

      bool moved = false;

      #if defined(SHOW_FRAGMENTATION) || defined(SHOW_MEM_EVENTS)
      GCLOG("Total memory : %s\n", formatBytes(GetWorkingMemory()).c_str());
      GCLOG("  reserved bytes : %s\n", formatBytes(mRowsInUse*IMMIX_LINE_LEN).c_str());
      if (full)
      {
         GCLOG("  active bytes   : %s\n", formatBytes(stats.bytesInUse).c_str());
         GCLOG("  active ratio   : %f\n", (double)stats.bytesInUse/( mRowsInUse*IMMIX_LINE_LEN));
         GCLOG("  fragged blocks : %d (%.1f%%)\n", stats.fraggedBlocks, stats.fraggedBlocks*100.0/mAllBlocks.size() );
         GCLOG("  fragged score  : %f\n", (double)stats.fragScore/mAllBlocks.size() );
      }
      GCLOG("  large size   : %s\n", formatBytes(mLargeAllocated).c_str());
      GCLOG("  empty blocks : %d (%.1f%%)\n", stats.emptyBlocks, stats.emptyBlocks*100.0/mAllBlocks.size());
      #endif

      size_t bytesInUse = mRowsInUse<<IMMIX_LINE_BITS;

      STAMP(t3)


      #ifdef HXCPP_TELEMETRY
      // Detect deallocations - TODO: add STAMP() ?
      __hxt_gc_after_mark(gByteMarkID, HX_ENDIAN_MARK_ID_BYTE);
      #endif

      // Sweep large

      // Manage recycle size ?
      //  clear old frames recycle objects
      int l2 = largeObjectRecycle.size();
      for(int i=0;i<largeObjectRecycle.size();i++)
         QueueLargeFree(largeObjectRecycle[i]);
      largeObjectRecycle.setSize(0);

      size_t recycleRemaining = 0;
      #ifdef RECYCLE_LARGE
      if (!inForceCompact)
         recycleRemaining = mLargeAllocForceRefresh;
      #endif

      int l0 = mLargeList.size();
      // Compact the live entries in place.  qerase() shifts the whole tail on
      // every removal, which made this sweep O(n^2) with thousands of large
      // objects - the largest single stall seen in gc_perf.log.
      int live = 0;
      for(int i=0;i<l0;i++)
      {
         unsigned int *blob = mLargeList[i];
         if ( (blob[1] & IMMIX_ALLOC_MARK_ID) != hx::gMarkID )
         {
            unsigned int size = *blob;
            mLargeAllocated -= size;
            if (size < recycleRemaining)
            {
               recycleRemaining -= size;
               largeObjectRecycle.push(blob);
            }
            else
            {
               QueueLargeFree(blob);
            }
         }
         else
            mLargeList[live++] = blob;
      }
      mLargeList.setSize(live);

      int l1 = mLargeList.size();
      double tCollectLarge = __hxcpp_time_stamp();


      STAMP(t4)

      bool defragged = false;

      // Compact/Defrag?
      #if defined(HXCPP_GC_MOVING) && defined(HXCPP_VISIT_ALLOCS)
      if (full)
      {
         bool doRelease = false;

         if (inForceCompact)
            doRelease = true;
         else
         {
            size_t mem = mRowsInUse<<IMMIX_LINE_BITS;
            size_t targetFree = std::max((size_t)hx::sgMinimumFreeSpace, mem/100 * (size_t)hx::sgTargetFreeSpacePercentage );
            targetFree = std::min(targetFree, (size_t)sgMaximumFreeSpace );
            sWorkingMemorySize = std::max( mem + targetFree, (size_t)hx::sgMinimumWorkingMemory);

            size_t allMem = GetWorkingMemory();
            // 8 Meg too much?
            size_t allowExtra = std::max( (size_t)8*1024*1024, sWorkingMemorySize*5/4 );

            if ( allMem > sWorkingMemorySize + allowExtra )
            {
               #if defined(SHOW_FRAGMENTATION) || defined(SHOW_MEM_EVENTS)
               int releaseGroups = (int)((allMem - sWorkingMemorySize) / (IMMIX_BLOCK_SIZE<<IMMIX_BLOCK_GROUP_BITS));
               if (releaseGroups)
                  GCLOG("Try to release %d groups\n", releaseGroups );
               #endif
               doRelease = true;
            }
         }


         bool isFragged = stats.fragScore > mAllBlocks.size()*FRAG_THRESH;
         if (doRelease || isFragged || hx::gAlwaysMove)
         {
            if (isFragged && sgTimeToNextTableUpdate>1)
               sgTimeToNextTableUpdate = 1;
            calcMoveOrder( );

            // Borrow some blocks to ensuure space to defrag into
            int workingBlocks = mAllBlocks.size()*3/2 - stats.emptyBlocks;
            int borrowed = 0;
            while( mAllBlocks.size()<workingBlocks )
            {
               bool dummy = false;
               if (!AllocMoreBlocks(dummy, true))
                  break;
               doRelease = true;
               borrowed++;
            }
            stats.emptyBlocks += borrowed;
            #if defined(SHOW_FRAGMENTATION)
               GCLOG("Borrowed %d groups for %d target blocks\n", borrowed, workingBlocks);
            #endif

            MoveBlockJob job(mAllBlocks);

            if (MoveBlocks(job,stats) || doRelease)
            {
               if (doRelease)
               {
                  size_t mem = mRowsInUse<<IMMIX_LINE_BITS;
                  size_t targetFree = std::max((size_t)hx::sgMinimumFreeSpace, bytesInUse/100 *hx::sgTargetFreeSpacePercentage );
                  targetFree = std::min(targetFree, (size_t)sgMaximumFreeSpace );
                  size_t targetMem = std::max( mem + targetFree, (size_t)hx::sgMinimumWorkingMemory) +
                                        (2<<(IMMIX_BLOCK_GROUP_BITS+IMMIX_BLOCK_BITS));

                  if (inForceCompact)
                     targetMem = 0;
                  size_t have = GetWorkingMemory();
                  if (targetMem<have)
                  {
                     size_t releaseSize = have - targetMem;
                     #ifdef SHOW_FRAGMENTATION
                     GCLOG(" Release %s bytes to leave %s\n", formatBytes(releaseSize).c_str(), formatBytes(targetMem).c_str() );
                     #endif

                     int releasedBlocks = releaseEmptyGroups(stats, releaseSize);
                     #ifdef SHOW_FRAGMENTATION
                     int releasedGroups = releasedBlocks >> IMMIX_BLOCK_GROUP_BITS;
                     GCLOG(" Released %s, %d groups\n", formatBytes((size_t)releasedBlocks<<IMMIX_BLOCK_BITS).c_str(), releasedGroups );
                     #endif
                  }
               }

               // Reduce sWorkingMemorySize now we have defragged
               #if defined(SHOW_FRAGMENTATION) || defined(SHOW_MEM_EVENTS)
               GCLOG("After compacting---\n");
               GCLOG("  total memory : %s\n", formatBytes(GetWorkingMemory()).c_str() );
               GCLOG("  total needed : %s\n", formatBytes((size_t)mRowsInUse*IMMIX_LINE_LEN).c_str() );
               GCLOG("  for bytes    : %s\n", formatBytes(bytesInUse).c_str() );
               GCLOG("  empty blocks : %d (%.1f%%)\n", stats.emptyBlocks, stats.emptyBlocks*100.0/mAllBlocks.size());
               GCLOG("  fragged blocks : %d (%.1f%%)\n", stats.fraggedBlocks, stats.fraggedBlocks*100.0/mAllBlocks.size() );
               #endif
            }

            std::stable_sort(&mAllBlocks[0], &mAllBlocks[0] + mAllBlocks.size(), SortByBlockPtr );

            #ifdef HXCPP_GC_VERIFY
            VerifyBlockOrder();
            #endif
         }
      }
      #endif


      STAMP(t5)

      size_t mem = mRowsInUse<<IMMIX_LINE_BITS;
      size_t baseMem = full ? bytesInUse : mem;
      #ifdef HXCPP_GC_DYNAMIC_SIZE
      size_t targetFree = std::max((size_t)hx::sgMinimumFreeSpace, (size_t)(baseMem * profileCollectSummary.spaceFactor ) );
      #else
      size_t targetFree = std::max((size_t)hx::sgMinimumFreeSpace, baseMem/100 *hx::sgTargetFreeSpacePercentage );
      #endif
      targetFree = std::min(targetFree, (size_t)sgMaximumFreeSpace );
      // Only adjust if non-generational
      if (!generational)
         sWorkingMemorySize = std::max( mem + targetFree, (size_t)hx::sgMinimumWorkingMemory);

      // MMTk's shrink: hand empty block groups back to the OS.  The allocator
      // never frees blocks, so without this a temporary peak (a large song
      // loading) stays reserved and every later full collection has to scan
      // it.  Allocators are reset first so no block is freed under a bump
      // pointer.
      {
         size_t currentCap = GetWorkingMemory();
         if (currentCap > sWorkingMemorySize + (64<<20) && !gcBisectFlag("HXCPP_NO_SHRINK"))
         {
            for(int i=0;i<mLocalAllocs.size();i++)
               ClearPooledAlloc(mLocalAllocs[i]);
            for(int i=0;i<LOCAL_POOL_SIZE;i++)
               if (mLocalPool[i])
                  ClearPooledAlloc(mLocalPool[i]);
            size_t released = ShrinkBlocks(stats, currentCap - sWorkingMemorySize);
            if (released)
               GCPerfLog("shrink released=%dMB cap=%dMB target=%dMB",
                  (int)(released>>20), (int)(GetWorkingMemory()>>20), (int)(sWorkingMemorySize>>20));
         }
      }

      #if defined(SHOW_FRAGMENTATION) || defined(SHOW_MEM_EVENTS)
      GCLOG("Target memory %s, using %s\n",  formatBytes(sWorkingMemorySize).c_str(), formatBytes(mem).c_str() );
      #endif

      // Large alloc target
      size_t blockSize =  GetWorkingMemory();
      if (blockSize > mLargeAllocSpace)
         mLargeAllocSpace = blockSize;
      mLargeAllocForceRefresh = mLargeAllocated + mLargeAllocSpace;

      mTotalAfterLastCollect = MemUsage();

      #ifdef HXCPP_GC_GENERATIONAL
      if (generational)
      {
         // TODO - include large too?
         int retained = mRowsInUse - oldRowsInUse;
         int space = mAllBlocks.size()*IMMIX_USEFUL_LINES - oldRowsInUse;
         if (space<retained)
            space = retained;

         mGenerationalRetainEstimate = (double)retained/(double)space;
      }
      else
      {
         // move towards 0.2
         mGenerationalRetainEstimate += (0.2-mGenerationalRetainEstimate)*0.25;
      }

      double filled_ratio = (double)mRowsInUse/(double)(mAllBlocksCount*IMMIX_USEFUL_LINES);
      double after_gen = filled_ratio + (1.0-filled_ratio)*mGenerationalRetainEstimate;

      if (after_gen<0.85)
      {
         sGcMode = gcmGenerational;
      }
      else
      {
         sGcMode = gcmFull;
         // What was I thinking here?  This breaks #851
         //gByteMarkID |= 0x30;
         sgTimeToNextTableUpdate = 10;
      }

      #ifdef SHOW_MEM_EVENTS
      GCLOG("filled=%.2f%% + estimate = %.2f%% = %.2f%% -> %s\n",
            filled_ratio*100, mGenerationalRetainEstimate*100, after_gen*100, sGcMode==gcmFull?"Full":"Generational");
      #endif

      #endif

      double tCollectBeforeFree = __hxcpp_time_stamp();

      createFreeList();

      // This saves some running/stall time, but increases the total CPU usage
      // Delaying it until just before the block is used to improve the cache locality
      backgroundProcessFreeList(true);

      double tCollectFree = __hxcpp_time_stamp();
      GCPerfLog("collect total=%.3f mark=%.3f reclaim=%.3f large=%.3f stats=%.3f freelist=%.3f used=%d blocks=%d",
         (tCollectFree-tCollectEnter)*1000, (tCollectMarked-tCollectEnter)*1000,
         (tCollectReclaimed-tCollectMarked)*1000, (tCollectLarge-tCollectReclaimed)*1000,
         (tCollectBeforeFree-tCollectLarge)*1000, (tCollectFree-tCollectBeforeFree)*1000,
         (int)MemUsage(), (int)mAllBlocks.size());

      mAllBlocksCount   = mAllBlocks.size();
      mCurrentRowsInUse = mRowsInUse;
      mRowsAtLastCollect = mCurrentRowsInUse;

      #ifdef SHOW_MEM_EVENTS
      GCLOG("Collect Done\n");
      #endif

      #ifdef PROFILE_COLLECT
      STAMP(t6)
      double period = t6-sLastCollect;
      sLastCollect=t6;
      GCLOG("Collect time %s total=%.2fms =%.1f%%\n  setup=%.2f\n  %s=%.2f(init=%.2f/roots=%.2f %d+%d/loc=%.2f*%d %d+%d/mark=%.2f %d+%d/fin=%.2f*%d/ids=%.2f)\n  reclaim=%.2f\n  large(%d->%d, recyc %d)=%.2f\n  defrag=%.2f\n",
               generational ? "gen" : "std",
              (t6-t0)*1000, (t6-t0)*100.0/period, // total %
              (t1-t0)*1000, // sync/setup
              generational ? "mark gen" : "mark", (t2-t1)*1000,
                      (tMarkInit-t1)*1000,
                      (tMarkLocal-tMarkInit)*1000,  hx::rootObjects, hx::rootAllocs,
                      (tMarkLocalEnd-tMarkLocal)*1000, hx::localCount, hx::localObjects-hx::rootObjects, hx::localAllocs-hx::rootAllocs,
                      (tMarked-tMarkLocalEnd)*1000, sObjectMarks-hx::localObjects, sAllocMarks-hx::localAllocs,
                      (hx::tFinalizers-tMarked)*1000, hx::finalizerCount,
                      (t2-hx::tFinalizers)*1000,
              (t3-t2)*1000, // reclaim
              l0, l1, l2, (t4-t3)*1000, // large
              (t5-t4)*1000 // defrag
              );
      sObjectMarks = sAllocMarks = 0;

      #endif

      #ifdef PROFILE_THREAD_USAGE
      GCLOG("Thread chunks:%d, wakes=%d\n", sThreadChunkPushCount, sThreadChunkWakes);
      for(int i=-1;i<MAX_GC_THREADS;i++)
        GCLOG(" thread %d] %d + %d\n", i, sThreadMarkCount[i], sThreadArrayMarkCount[i]);
      GCLOG("Locking spins  : %d\n", sSpinCount);
      sSpinCount = 0;
      #endif

      #ifdef HXCPP_GC_GENERATIONAL
      if (sGcMode==gcmGenerational)
         for(int i=0;i<mLocalAllocs.size();i++)
         {
            hx::StackContext *ctx = (hx::StackContext *)mLocalAllocs[i];
            ctx->mOldReferrers = hx::sGlobalChunks.alloc();
         }
      #endif


      #ifdef HXCPP_GC_VERIFY
      VerifyBlockOrder();
      #endif

      for(int i=0;i<LOCAL_POOL_SIZE;i++)
      {
         LocalAllocator *l = mLocalPool[i];
         if (l)
            ClearPooledAlloc(l);
      }

      #ifdef HXCPP_TELEMETRY
      __hxt_gc_end();
      #endif

      sgIsCollecting = false;
      sGcLastCollectFrame = sGcFrameCount;
      sGcLastTickUsage = MemUsage();
      sGcMemAtLastCollect = sGcLastTickUsage;
      sUsageAtLastCollect = MemUsage();

      hx::gPauseForCollect = 0x00000000;
      #ifndef HXCPP_SINGLE_THREADED_APP
         for(int i=0;i<mLocalAllocs.size();i++)
         {
            #ifdef HXCPP_SCRIPTABLE
            ((hx::StackContext *)mLocalAllocs[i])->byteMarkId = hx::gByteMarkID;
            #endif
            if (mLocalAllocs[i]!=this_local)
               ReleaseFromSafe(mLocalAllocs[i]);
         }

         if (!inLocked)
            gThreadStateChangeLock->unlock();
      #else
        #ifdef HXCPP_SCRIPTABLE
        hx::gMainThreadContext->byteMarkId = hx::gByteMarkID;
        #endif
      #endif


      PROFILE_COLLECT_SUMMARY_END;
   }


   // --- Incremental collection ---------------------------------------------
   //
   // BeginIncremental stops the world briefly, snapshots the roots and starts
   // a mark cycle.  StepIncremental runs on the main thread with a budget while
   // the mutator keeps running (the write barrier records black->white stores).
   // FinishIncremental stops the world again, re-scans the roots and the
   // remembered set, drains the marker and sweeps.

   #ifdef HXCPP_GC_AUDIT
   static bool AuditLooksMapped(void *inPtr)
   {
      #ifdef HX_WINDOWS
      MEMORY_BASIC_INFORMATION info;
      if (!VirtualQuery(inPtr, &info, sizeof(info)))
         return false;
      return info.State == MEM_COMMIT && info.Protect != PAGE_NOACCESS;
      #else
      return true;
      #endif
   }

   // Collect the addresses of every object currently carrying the live mark,
   // so an incremental mark can be compared against a full mark.
   void AuditCollectMarked(std::unordered_set<void*> &out)
   {
      for(int i=0;i<mAllBlocks.size();i++)
      {
         BlockDataInfo *block = mAllBlocks[i];
         char *base = (char *)block->mPtr;
         unsigned char *rowMarks = (unsigned char *)block->mPtr;
         for(int r=IMMIX_HEADER_LINES; r<IMMIX_LINES; r++)
         {
            if (!rowMarks[r])
               continue;
            unsigned int flags = block->allocStart[r];
            if (!flags)
               continue;
            for(int bit=0; bit<32; bit++)
            {
               if (!(flags & (1u<<bit)))
                  continue;
               unsigned int *header = (unsigned int *)(base + (r<<IMMIX_LINE_BITS) + (bit*4));
               if ((*header & IMMIX_ALLOC_ROW_COUNT)==0)
                  continue;
               hx::Object *obj = (hx::Object *)(header + 1);
               // Remembered objects carry HX_GC_REMEMBERED on top of the cycle
               // byte; they are just as marked as plain black objects.
               unsigned char mark = ((unsigned char *)obj)[HX_ENDIAN_MARK_ID_BYTE];
               if ((mark & FULL_MARK_BYTE_MASK) == (hx::gByteMarkID & FULL_MARK_BYTE_MASK))
                  out.insert(obj);
            }
         }
      }
      for(int i=0;i<mLargeList.size();i++)
      {
         unsigned int *blob = mLargeList[i];
         if ((blob[1] & IMMIX_ALLOC_MARK_ID) == hx::gMarkID)
            out.insert((hx::Object *)(blob+2));
      }
   }
   #endif

   void MarkIncrementalRoots(bool inIncludeStacks)
   {
      hx::MarkClassStatics(&mMarker);

      {
         hx::AutoMarkPush info(&mMarker,"Roots","root");

         for(hx::RootSet::iterator i = hx::sgRootSet.begin(); i!=hx::sgRootSet.end(); ++i)
         {
            hx::Object *&obj = **i;
            if (obj)
               hx::MarkObjectAlloc(obj, &mMarker);
         }

         if (hx::sgOffsetRootSet)
            for(hx::OffsetRootSet::iterator i = hx::sgOffsetRootSet->begin(); i!=hx::sgOffsetRootSet->end(); ++i)
            {
               char *ptr = *(char **)(i->first);
               int offset = i->second;
               hx::Object *obj = (hx::Object *)(ptr - offset);
               if (obj)
                  hx::MarkObjectAlloc(obj, &mMarker);
            }
      }

      {
         hx::AutoMarkPush info(&mMarker,"Zombies","zombie");
         for(int i=0;i<hx::sZombieList.size();i++)
            hx::MarkObjectAlloc(hx::sZombieList[i], &mMarker);
      }

      if (inIncludeStacks)
         for(int i=0;i<mLocalAllocs.size();i++)
            MarkLocalAlloc(mLocalAllocs[i], &mMarker);
   }


   // Off-main-thread marking for the incremental cycle.  A marked object can
   // be a huge array, so a per-frame time budget cannot bound a step; a worker
   // thread has no such constraint and the frame time stays untouched.
   //
   // MMTk runs its Concurrent bucket on every GC worker; the single dedicated
   // thread here left three of the four pool threads idle during a cycle and
   // cycles lost the race against mutator allocation on 3GB scenes.  With
   // HX_MULTI_THREAD_MARKING the STW pool is reused instead: StartThreadJobs
   // with inWait=false hands tpjMark to all MAX_GC_THREADS workers and returns
   // immediately, and completion is just "sRunningThreads == 0".
   #ifdef HX_MULTI_THREAD_MARKING
   void StartBackgroundMark()
   {
      StartThreadJobs(tpjMark, MAX_GC_THREADS, false);
   }

   bool BackgroundMarkFinished()
   {
      {
         std::lock_guard<std::mutex> l(sThreadPoolLock);
         return sRunningThreads == 0;
      }
   }
   #else
   void StartBackgroundMark()
   {
      if (!sgIncrThread)
      {
         sgIncrThread = new std::thread(IncrMarkThreadProc);
         sgIncrThread->detach();
      }
      {
         std::lock_guard<std::mutex> l(sgIncrThreadLock);
         sgIncrThreadDone = false;
         sgIncrThreadRequest = true;
      }
      sgIncrThreadCv.notify_one();
   }

   bool BackgroundMarkFinished()
   {
      std::lock_guard<std::mutex> l(sgIncrThreadLock);
      return sgIncrThreadDone && !sgIncrThreadBusy;
   }
   #endif

   #ifndef HX_MULTI_THREAD_MARKING
   void DrainMarkStackInBackground()
   {
      mMarker.init();
      bool done = false;
      while(!done)
      {
         int budget = 4096;
         done = mMarker.processMarkStackBudget(budget);
      }
   }
   #endif


   bool BeginIncremental()
   {
      if (sgIncrementalActive)
         return false;

      // Never start during boot: the class tables and thread stacks are not
      // stable yet, and scanning them here crashes.  The first frame-driven
      // collections have to be plain stop-the-world ones.
      if (sGcFrameCount < 30)
         return false;

      double tBegin = __hxcpp_time_stamp();
      // The pacer measures a cycle from this pause to the end of the sweep.
      sCycleBeginTime = tBegin;
      sHeapAtCycleStart = GetWorkingMemory();
      sRowsSinceCycle = 0;
      GCTrace("begin-enter");
      #ifdef HXCPP_GC_AUDIT
      GCAuditLog("begin-enter frame=%d", sGcFrameCount);
      #endif
      volatile int stackBottom = 1;

      #ifdef HXCPP_SINGLE_THREADED_APP
      LocalAllocator *this_local = (LocalAllocator *)hx::gMainThreadContext;
      #else
      LocalAllocator *this_local = (LocalAllocator *)(hx::ImmixAllocator *)hx::tlsStackContext;
      #endif

      #ifndef HXCPP_SINGLE_THREADED_APP
      if (_hx_atomic_compare_exchange((volatile int *)&hx::gPauseForCollect, 0, 0xffffffff) != 0)
         return false;

      gThreadStateChangeLock->lock();
      for(int i=0;i<mLocalAllocs.size();i++)
         if (mLocalAllocs[i]!=this_local)
            WaitForSafe(mLocalAllocs[i]);
      #endif

      sgIsCollecting = true;
      CaptureLocalStack(this_local, (int *)&stackBottom);
      StopThreadJobs(true);
      double tPaused = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.beginWait, tPaused - tBegin);
      GCTrace("begin-paused");

      // Start a fresh mark cycle.
      hx::gPrevByteMarkID = hx::gByteMarkID;
      hx::gPrevMarkIdMask = ((~hx::gMarkID) & 0x30000000) | HX_GC_CONST_ALLOC_BIT;
      hx::gByteMarkID = (hx::gByteMarkID + 1) & 0x0f;
      if (hx::gByteMarkID & 0x1)
         hx::gByteMarkID |= 0x20;
      else
         hx::gByteMarkID |= 0x10;

      hx::gMarkID = hx::gByteMarkID << 24;
      hx::gMarkIDWithContainer = (hx::gByteMarkID << 24) | IMMIX_ALLOC_IS_CONTAINER;
      hx::gRememberedByteMarkID = hx::gByteMarkID | HX_GC_REMEMBERED;
      gBlockStack = 0;
      // Parallel over the worker pool (pool is idle here: StopThreadJobs ran
      // above) - the single-threaded pass cost 0.3-0.6ms of every begin pause.
      StartThreadJobs(tpjClearRowMarks, mAllBlocks.size(), true);

      mMarker.init();
      mMarker.isGenerational = false;

      for(int i=0;i<mLocalAllocs.size();i++)
      {
         hx::StackContext *ctx = (hx::StackContext *)mLocalAllocs[i];
         if (!ctx->mOldReferrers)
            ctx->mOldReferrers = hx::sGlobalChunks.alloc();
      }

      GCTrace("begin-roots");
      double tRoots = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.beginSetup, tRoots - tPaused);
      MarkIncrementalRoots(false);
      double tAlloc = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.beginRoots, tAlloc - tRoots);

      // ClearRowMarks dropped every allocStart bit, including the objects in
      // the current nursery holes.  Reset each allocator so the mutator takes
      // fresh blocks instead of letting the sweep hand those rows out twice.
      for(int i=0;i<mLocalAllocs.size();i++)
         ClearPooledAlloc(mLocalAllocs[i]);
      double tAllocEnd = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.beginAlloc, tAllocEnd - tAlloc);
      PhaseMax(sGcPhases.beginTotal, tAllocEnd - tBegin);
      GCTrace("begin-roots-done");

      // An incremental cycle does not compute a new heap target by itself,
      // so the allocator must not be held at the tiny bootstrap value while
      // it runs.
      if (sWorkingMemorySize < (size_t)hx::sgMinimumWorkingMemory)
         sWorkingMemorySize = (size_t)hx::sgMinimumWorkingMemory;

      sgIncrementalActive = 1;
      hx::gIncrementalMarking = true;
      sgIsCollecting = false;

      // The roots marked above sit in mMarker's local chunk; publish it so the
      // background workers can drain everything, then hand tpjMark to the
      // pool.  Threads wake with the world still paused and are already
      // draining when the mutators resume.
      mMarker.releaseJobs();
      StartBackgroundMark();

      hx::gPauseForCollect = 0x00000000;
      #ifndef HXCPP_SINGLE_THREADED_APP
      for(int i=0;i<mLocalAllocs.size();i++)
         if (mLocalAllocs[i]!=this_local)
            ReleaseFromSafe(mLocalAllocs[i]);
      gThreadStateChangeLock->unlock();
      #endif

      GCTrace("begin-released");
      #ifdef HXCPP_GC_AUDIT
      GCAuditLog("begin-done frame=%d", sGcFrameCount);
      #endif
      sIncrStepTotal = 0;
      sIncrStepFrames = 0;
      sStwPauseSeconds = __hxcpp_time_stamp() - tBegin;
      sCycleCount++;
      #ifdef HXCPP_DEBUG
      GCPerfLog("begin %.3fms used=%d wm=%d blocks=%d threads=%d", (__hxcpp_time_stamp()-tBegin)*1000,
         (int)MemUsage(), (int)sWorkingMemorySize, (int)mAllBlocks.size(), (int)MAX_GC_THREADS);
      #endif
      return true;
   }


   void StepIncremental(int inBudgetMicros)
   {
      if (!sgIncrementalActive)
         return;

      double tStep = __hxcpp_time_stamp();

      GCTrace("step");
      #ifdef HXCPP_GC_AUDIT
      static int sStepLog = 0;
      if ((sStepLog++ & 15)==0)
         GCAuditLog("step %d frame=%d", sStepLog, sGcFrameCount);
      #endif

      // Object counts do not translate to time (arrays are marked in bulk),
      // so bound the work by the clock and check it between small batches.
      if (inBudgetMicros < 1)
         inBudgetMicros = 1;
      double deadline = __hxcpp_time_stamp() + inBudgetMicros * 1.0e-6;

      mMarker.init();
      bool done = false;
      do
      {
         int batch = 128;
         done = mMarker.processMarkStackBudget(batch);
         if (done)
            break;
      }
      while(__hxcpp_time_stamp() < deadline);

      sIncrStepTotal += __hxcpp_time_stamp() - tStep;
      sIncrStepFrames++;

      if (done)
         FinishIncremental();
   }


   void FinishIncremental()
   {
      if (!sgIncrementalActive)
         return;

      // The worker must be idle before the mark state is touched again.
      if (!BackgroundMarkFinished())
         return;

      GCTrace("finish-enter");
      #ifdef HXCPP_GC_AUDIT
      GCAuditLog("finish-enter frame=%d", sGcFrameCount);
      #endif
      double tFinish = __hxcpp_time_stamp();
      double tPaused = 0;
      double tMarked = 0;
      double tFinal = 0;
      volatile int stackBottom = 1;

      #ifdef HXCPP_SINGLE_THREADED_APP
      LocalAllocator *this_local = (LocalAllocator *)hx::gMainThreadContext;
      #else
      LocalAllocator *this_local = (LocalAllocator *)(hx::ImmixAllocator *)hx::tlsStackContext;
      #endif

      #ifndef HXCPP_SINGLE_THREADED_APP
      if (_hx_atomic_compare_exchange((volatile int *)&hx::gPauseForCollect, 0, 0xffffffff) != 0)
         return;

      gThreadStateChangeLock->lock();
      for(int i=0;i<mLocalAllocs.size();i++)
         if (mLocalAllocs[i]!=this_local)
            WaitForSafe(mLocalAllocs[i]);
      #endif

      sgIsCollecting = true;
      CaptureLocalStack(this_local, (int *)&stackBottom);
      StopThreadJobs(true);
      GCTrace("finish-paused");
      tPaused = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.finishWait, tPaused - tFinish);

      // Re-scan roots and remembered referrers on a stopped heap.
      mMarker.init();
      mMarker.isGenerational = false;

      // Must still drain the barrier chunks, otherwise they overflow.
      for(int i=0;i<mLocalAllocs.size();i++)
      {
         hx::StackContext *ctx = (hx::StackContext *)mLocalAllocs[i];
         if (ctx->mOldReferrers)
         {
            if (ctx->mOldReferrers->count)
               hx::sGlobalChunks.addLocked(ctx->mOldReferrers);
            else
               hx::sGlobalChunks.free(ctx->mOldReferrers);
            ctx->mOldReferrers = 0;
         }
      }

      GCTrace("finish-roots");
      double tRoots = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.finishDrain, tRoots - tPaused);
      // NOTE: the stack scan stays on the main thread.  A parallel version
      // (tpjStackScan) measured 10-78ms here at real frame rates vs 0.5-0.9ms
      // sequential - the conservative scan of garbage-dense mutator stacks
      // does not parallelize well (cache/lock effects), so it was reverted.
      MarkIncrementalRoots(true);
      double tRootsDone = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.finishRoots, tRootsDone - tRoots);

      #ifdef HX_MULTI_THREAD_MARKING
      mMarker.releaseJobs();
      StartThreadJobs(tpjMark, MAX_GC_THREADS, true);
      #else
      mMarker.processMarkStack();
      #endif
      GCTrace("finish-marked");
      {
         int orphaned = hx::sGlobalChunks.pendingJobs();
         if (orphaned)
            GCPerfLog("GC-ORPHAN finish-mark: %d mark chunks left undrained!", orphaned);
      }
      tMarked = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.finishMark, tMarked - tRootsDone);

      #ifdef HXCPP_GC_AUDIT
      // Limit > 0 replaces the finish mark with a full mark and compares the
      // two sets.  Zero runs the plain incremental finish.
      static int sAuditCycleLimit = 3;
      static int sAuditCycles = 0;
      if (sAuditCycles < sAuditCycleLimit)
      {
         sAuditCycles++;
         std::unordered_set<void*> before;
         AuditCollectMarked(before);
         MarkAll(false);
         std::unordered_set<void*> after;
         AuditCollectMarked(after);

         FILE *audit = fopen("gc_audit.log","a");
         if (audit)
         {
            int missing = 0;
            for(std::unordered_set<void*>::iterator it = after.begin(); it!=after.end(); ++it)
            {
               if (before.count(*it))
                  continue;
               if (++missing > 40)
                  break;
               const char *name = "?";
               hx::Object *obj = (hx::Object *)(*it);
               // Only dereference the class pointer if the memory is committed;
               // stale allocStart entries can otherwise point at garbage.
               if (AuditLooksMapped(obj))
               {
                  void **vtable = *(void ***)obj;
                  if (AuditLooksMapped(vtable))
                  {
                     hx::Class cls = obj->__GetClass();
                     if (cls.GetPtr() && AuditLooksMapped(cls.GetPtr()))
                        name = cls->mName.raw_ptr();
                  }
               }
               fprintf(audit, "missed %p %s\n", *it, name);
            }
            fprintf(audit, "cycle %d: before=%d after=%d missed=%d\n",
               sAuditCycles, (int)before.size(), (int)after.size(), missing);
            fclose(audit);
         }
      }
      #endif

      hx::FindZombies(mMarker);
      double tZombies = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.finishZombies, tZombies - tMarked);

      bool markedWeakValue;
      do
      {
         markedWeakValue = false;
         mMarker.init();
         for(int i=0;i<hx::sWeakHashList.size();i++)
         {
            hx::HashRoot *hash = hx::sWeakHashList[i];
            if (hx::IsWeakRefValid(hash))
               markedWeakValue = hash->markWeakValues(&mMarker) || markedWeakValue;
         }
         if (markedWeakValue)
         {
            #ifdef HX_MULTI_THREAD_MARKING
            mMarker.releaseJobs();
            StartThreadJobs(tpjMark, MAX_GC_THREADS, true);
            #else
            mMarker.processMarkStack();
            #endif
         }
      }
      while(markedWeakValue);
      double tWeak = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.finishWeak, tWeak - tZombies);

      hx::RunFinalizers();
      GCTrace("finish-finalized");
      tFinal = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.finishFinal, tFinal - tWeak);

      FinishIncrementalSweep();
      GCTrace("finish-swept");

      double tDone = __hxcpp_time_stamp();
      PhaseMax(sGcPhases.finishSweep, tDone - tFinal);
      PhaseMax(sGcPhases.finishTotal, tDone - tFinish);
      sStwPauseSeconds += tDone - tFinish;
      sGcPhases.cycleSum += sStwPauseSeconds;
      if (sStwPauseSeconds > sGcPhases.cycleMax)
         sGcPhases.cycleMax = sStwPauseSeconds;
      sGcPhases.cycles++;
      // When the sync sweep finished the cycle inside this pause, the sweep
      // bookkeeping already counted the begin pause; add this finish pause
      // so the reported total covers the whole cycle.
      if (!sgIncrementalActive)
         sCyclePauseTotal += tDone - tFinish;
      #ifdef HXCPP_DEBUG
      GCPerfLog("finish total=%.3f pause=%.3f mark=%.3f weak=%.3f sweep=%.3f steps=%d stepAvg=%.1fus used=%d blocks=%d",
         (tDone-tFinish)*1000, (tPaused-tFinish)*1000, (tMarked-tPaused)*1000,
         (tFinal-tMarked)*1000, (tDone-tFinal)*1000,
         sIncrStepFrames, sIncrStepFrames ? sIncrStepTotal*1.0e6/sIncrStepFrames : 0.0,
         (int)MemUsage(), (int)mAllBlocks.size());
      #endif

      // Keep the cycle open: the row sweep continues in the frame tick, and
      // until it finishes the allocator must grow the heap instead of
      // collecting (see FinishIncrementalSweepList).
      sgIsCollecting = false;

      hx::gPauseForCollect = 0x00000000;
      #ifndef HXCPP_SINGLE_THREADED_APP
      for(int i=0;i<mLocalAllocs.size();i++)
         if (mLocalAllocs[i]!=this_local)
            ReleaseFromSafe(mLocalAllocs[i]);
      gThreadStateChangeLock->unlock();
      #endif

      GCTrace("finish-released");
   }


   // Drop a running cycle without sweeping: used when a major collection is
   // about to run and would re-mark everything anyway.  The background marker
   // has to be idle first because the full mark reuses the shared context.
   void AbortIncremental()
   {
      if (!sgIncrementalActive)
         return;

      // With pool marking, StopThreadJobs both waits for the workers to drain
      // (sgThreadPoolAbort makes them exit early) and resets the pool state
      // (sAllThreads/job/sLazyThreads).  The dedicated-thread fallback keeps
      // the old cv handshake.
      #ifdef HX_MULTI_THREAD_MARKING
      StopThreadJobs(true);
      #else
      {
         std::lock_guard<std::mutex> l(sgIncrThreadLock);
         sgIncrThreadRequest = false;
      }
      while (!BackgroundMarkFinished())
         std::this_thread::yield();
      {
         std::lock_guard<std::mutex> l(sgIncrThreadLock);
         sgIncrThreadDone = false;
      }
      #endif

      sgIncrementalActive = 0;
      hx::gIncrementalMarking = false;
      mSweepActive = false;
      sgIsCollecting = false;
      sIncrStepTotal = 0;
      sIncrStepFrames = 0;
      // MMTk counts pages allocated since the last GC COMPLETED, so the
      // next trigger measures allocation from here, not from the cycle
      // start.  (sRowsSinceCycle is also reset in BeginIncremental for the
      // pacing logs; this completion reset is what the trigger compares.)
      sRowsSinceCycle = 0;
   }


   void FinishIncrementalSweep()
   {
      GCTrace("sweep-enter");

      // Sweep large objects.  They live outside the blocks and the walk is
      // cheap, so it stays in the stop-the-world part.
      for(int i=0;i<largeObjectRecycle.size();i++)
         QueueLargeFree(largeObjectRecycle[i]);
      largeObjectRecycle.setSize(0);

      size_t recycleRemaining = 0;
      #ifdef RECYCLE_LARGE
      recycleRemaining = mLargeAllocForceRefresh;
      #endif

      int live = 0;
      int total = mLargeList.size();
      for(int i=0;i<total;i++)
      {
         unsigned int *blob = mLargeList[i];
         if ( (blob[1] & IMMIX_ALLOC_MARK_ID) != hx::gMarkID )
         {
            unsigned int size = *blob;
            mLargeAllocated -= size;
            if (size < recycleRemaining)
            {
               recycleRemaining -= size;
               largeObjectRecycle.push(blob);
            }
            else
            {
               QueueLargeFree(blob);
            }
         }
         else
            mLargeList[live++] = blob;
      }
      mLargeList.setSize(live);

      // No allocator may keep a block across the sweep: reclaiming rebuilds a
      // block's hole list, so anything the mutator still points into would be
      // corrupted.  Reset them all; they re-acquire holes from the free list
      // as the sweep publishes blocks.
      for(int i=0;i<mLocalAllocs.size();i++)
         ClearPooledAlloc(mLocalAllocs[i]);
      for(int i=0;i<LOCAL_POOL_SIZE;i++)
      {
         LocalAllocator *l = mLocalPool[i];
         if (l)
            ClearPooledAlloc(l);
      }

      BeginIncrementalSweep();
      GCTrace("sweep-begun");
   }

   bool SweepActive() const { return mSweepActive; }

   // True once every block has been handed to a sweeping thread.  The caller
   // must hold mSweepLock before treating the statistics as final, because
   // threads may still be reclaiming the blocks they claimed.
   bool SweepDone()
   {
      return !mSweepActive || mSweepCursor >= mAllBlocks.size();
   }

   // Lazy sweep, the way MMTk's Immix plan reclaims rows: the allocator that
   // needs a block reclaims one itself.  This spreads the sweep cost over
   // allocations instead of stopping the world at the end of a cycle.
   // Returns false when there is nothing left to sweep.
   bool SweepOneBlock()
   {
      if (!mSweepActive)
         return false;

      std::lock_guard<std::mutex> lock(mSweepLock);
      if (mSweepCursor >= mAllBlocks.size())
         return false;

      BlockDataInfo *info = mAllBlocks[mSweepCursor++];

      if (info->mOwned)
      {
         // An allocator picked this block up while the sweep was running;
         // the mutator owns its holes now, leave them alone.
         mSweepOwnedRows += info->mUsedRows;
         return true;
      }

      BlockDataStats stats;
      stats.clear();
      info->reclaim<true>(&stats);
      mSweepStats.add(stats);

      if (info->GetFreeRows()>0 && info->mMaxHoleSize>256)
      {
         int idx = mFreeBlocks.size();
         mFreeBlocks.push(info);
         for(int s=0;s<BLOCK_OFSIZE_COUNT;s++)
            if (mNextFreeBlockOfSize[s] > idx)
               mNextFreeBlockOfSize[s] = idx;
      }
      return true;
   }

   void BeginIncrementalSweep()
   {
      // Sweep directly over mAllBlocks instead of rebuilding a snapshot
      // list: pushing thousands of entries here cost ~0.4ms of the finish
      // pause for nothing.  mAllBlocks only ever grows, and newly added
      // blocks are empty, so reclaiming them is cheap and safe.
      {
         int orphaned = hx::sGlobalChunks.pendingJobs();
         if (orphaned)
            GCPerfLog("GC-ORPHAN sweep-start: %d mark chunks never drained!", orphaned);
      }
      for(int i=0;i<mAllBlocks.size();i++)
      {
         // Every allocator was just reset, so no block is really owned now.
         mAllBlocks[i]->mOwned = false;
      }

      mSweepStats.clear();
      mSweepOwnedRows = 0;
      mSweepCursor = 0;
      mSweepActive = true;
      sSweepStartTime = __hxcpp_time_stamp();

      // Every block is unowned now and the sweep publishes each one again as
      // it is reclaimed.  Keeping the old entries would hand allocators rows
      // that reclaim is about to rebuild, and the old cursor position would
      // hide them until the sweep appended new entries anyway.  The pause is
      // still holding every other thread, so clearing is safe.
      mFreeBlocks.clear();
      // Room for every block the sweep will publish.  The array is shared
      // with the mutator while it runs, so it has to be large enough up
      // front: growing it during the sweep would move the buffer under the
      // allocator's scan.  64k pointers covers a 1GB heap at 16k blocks.
      mFreeBlocks.safeReserveExtra(65536);
      for(int i=0;i<BLOCK_OFSIZE_COUNT;i++)
         mNextFreeBlockOfSize[i] = 0;

      mZeroList.clear();
   }

   bool StepIncrementalSweep(int inBudgetMicros)
   {
      if (!mSweepActive)
         return true;

      double start = __hxcpp_time_stamp();
      double budget = (inBudgetMicros>0 ? inBudgetMicros : 200) * 1.0e-6;
      int total = mAllBlocks.size();

      while(mSweepCursor < total)
      {
         BlockDataInfo *info = mAllBlocks[mSweepCursor++];

         if (info->mOwned)
         {
            // An allocator picked this block up while the sweep was running;
            // the mutator owns its holes now, leave them alone.
            mSweepOwnedRows += info->mUsedRows;
            continue;
         }

         BlockDataStats stats;
         stats.clear();
         info->reclaim<true>(&stats);
         mSweepStats.add(stats);

         if (info->GetFreeRows()>0 && info->mMaxHoleSize>256)
         {
            int idx = mFreeBlocks.size();
            mFreeBlocks.push(info);
            for(int s=0;s<BLOCK_OFSIZE_COUNT;s++)
               if (mNextFreeBlockOfSize[s] > idx)
                  mNextFreeBlockOfSize[s] = idx;
         }

         if (__hxcpp_time_stamp() - start >= budget)
            break;
      }

      sIncrStepTotal += __hxcpp_time_stamp() - start;
      sIncrStepFrames++;

      if (mSweepCursor < total)
         return false;

      FinishIncrementalSweepList();
      return true;
   }

   void FinishIncrementalSweepList()
   {
      // Wait for any thread still reclaiming a block: the statistics below
      // are only complete once every claimed block has finished.
      std::lock_guard<std::mutex> lock(mSweepLock);
      if (!mSweepActive)
         return;

      mRowsInUse = mSweepStats.rowsInUse + mSweepStats.fraggedRows + mSweepOwnedRows;

      // Feed the pacer with what the cycle actually cost.  MemCurrent() sits
      // at the optimistic "rows handed to the mutator" value until the sweep
      // publishes the real live rows below, so the difference to the previous
      // collection is the allocation volume the marker raced against.
      size_t cycleAllocated = MemCurrent() > sUsageAtLastCollect ? MemCurrent() - sUsageAtLastCollect : 0;
      double now = __hxcpp_time_stamp();
      double cycleSeconds = now - sCycleBeginTime;
      double wallSeconds = sLastCycleEndTime > 0 ? now - sLastCycleEndTime : cycleSeconds;

      // Only the pauses and the bounded steps are GC time; the sweep spans
      // many frames but the mutator runs between them.
      double gcSeconds = sStwPauseSeconds + sIncrStepTotal;
      if (gcSeconds > 1.0e-6 && wallSeconds > gcSeconds)
      {
         double ratio = gcSeconds / wallSeconds;
         sGcTimeRatioEma = sGcTimeRatioEma <= 0 ? ratio : sGcTimeRatioEma + (ratio - sGcTimeRatioEma) * 0.3;
      }
      sLastCycleEndTime = now;
      sCyclePauseTotal += sStwPauseSeconds + sIncrStepTotal;

      // Heap sizing: keep the long-standing headroom policy (the percentage
      // configured in sgTargetFreeSpacePercentage) as the target.  MMTk's
      // MemBalancer is only used as an upper adjustment when the measured
      // allocation rate really calls for a larger heap - its raw result is
      // far too tight for a game (a few ms of headroom) and would collect
      // several times per second.
      size_t mem = mRowsInUse<<IMMIX_LINE_BITS;
      size_t minHeap = std::max(mem + (size_t)hx::sgMinimumFreeSpace, (size_t)hx::sgMinimumWorkingMemory);

      size_t targetFree = mem/100 * (size_t)hx::sgTargetFreeSpacePercentage;
      if (targetFree < (size_t)hx::sgMinimumFreeSpace)
         targetFree = (size_t)hx::sgMinimumFreeSpace;
      targetFree = std::min(targetFree, (size_t)sgMaximumFreeSpace);
      size_t target = mem + targetFree;

      if (target < minHeap)
         target = minHeap;
      sWorkingMemorySize = target;

      size_t blockSize = GetWorkingMemory();
      if (blockSize > mLargeAllocSpace)
         mLargeAllocSpace = blockSize;
      mLargeAllocForceRefresh = mLargeAllocated + mLargeAllocSpace;

      mTotalAfterLastCollect = MemUsage();

      #ifdef HXCPP_GC_MOVING
      sgTimeToNextTableUpdate = 7;
      #else
      sgTimeToNextTableUpdate = 15;
      #endif

      mAllBlocksCount = mAllBlocks.size();
      mCurrentRowsInUse = mRowsInUse;
      mRowsAtLastCollect = mCurrentRowsInUse;

      mSweepActive = false;

      // Only now is the incremental cycle over.  Until this point the
      // allocator must be allowed to grow the heap rather than collect,
      // because the free rows are still being rebuilt.
      hx::gIncrementalMarking = false;
      sgIncrementalActive = 0;
      sRowsSinceCycle = 0;
      sUsageAtLastCollect = MemUsage();
      sGcLastCollectFrame = sGcFrameCount;
      sGcLastTickUsage = MemUsage();
      sGcMemAtLastCollect = sGcLastTickUsage;
      {
         std::lock_guard<std::mutex> l(sgIncrThreadLock);
         sgIncrThreadDone = false;
      }

      backgroundProcessFreeList(true);

      GCTrace("sweep-done");
      #ifdef HXCPP_DEBUG
      GCPerfLog("sweep total=%.3f blocks=%d rows=%d used=%d target=%d gcRatio=%.2f%% cycleAlloc=%d",
         (__hxcpp_time_stamp()-sSweepStartTime)*1000, (int)mAllBlocks.size(),
         (int)mRowsInUse, (int)MemUsage(), (int)sWorkingMemorySize,
         sGcTimeRatioEma*100.0, (int)cycleAllocated);
      #endif
   }


   void reclaimBlocks(bool full, BlockDataStats &outStats)
   {
      if (MAX_GC_THREADS>1)
      {
         for(int i=0;i<MAX_GC_THREADS;i++)
            sThreadBlockDataStats[i].clear();
         StartThreadJobs(full ? tpjReclaimFull : tpjReclaim, mAllBlocks.size(), true);
         outStats = sThreadBlockDataStats[0];
         for(int i=1;i<MAX_GC_THREADS;i++)
            outStats.add(sThreadBlockDataStats[i]);
      }
      else
      {
         outStats.clear();
         for(int i=0;i<mAllBlocks.size();i++)
         {
            if (full)
               mAllBlocks[i]->reclaim<true>(&outStats);
            else
               mAllBlocks[i]->reclaim<false>(&outStats);
         }
      }
   }


   void countRows(BlockDataStats &outStats)
   {
      if (MAX_GC_THREADS>1)
      {
         for(int i=0;i<MAX_GC_THREADS;i++)
            sThreadBlockDataStats[i].clear();
         StartThreadJobs(tpjCountRows, mAllBlocks.size(), true);
         outStats = sThreadBlockDataStats[0];
         for(int i=1;i<MAX_GC_THREADS;i++)
            outStats.add(sThreadBlockDataStats[i]);
      }
      else
      {
         outStats.clear();
         for(int i=0;i<mAllBlocks.size();i++)
            mAllBlocks[i]->countRows(outStats);
      }
   }


   // buils mFreeBlocks and maybe starts the async-zero process on mZeroList
   void createFreeList()
   {
      mFreeBlocks.clear();

      for(int i=0;i<mAllBlocks.size();i++)
      {
         BlockDataInfo *info = mAllBlocks[i];
         if (info->GetFreeRows() > 0 && info->mMaxHoleSize>256)
         {
            info->mOwned = false;
            mFreeBlocks.push(info);
         }
      }

      int extra = std::max( mAllBlocks.size(), 8<<IMMIX_BLOCK_GROUP_BITS);
      mFreeBlocks.safeReserveExtra(extra);

      std::sort(&mFreeBlocks[0], &mFreeBlocks[0] + mFreeBlocks.size(), SmallestFreeFirst );

      for(int i=0;i<BLOCK_OFSIZE_COUNT;i++)
         mNextFreeBlockOfSize[i] = mFreeBlocks.size();

      for(int i=mFreeBlocks.size()-1;i>=0;i--)
      {
         int slot = mFreeBlocks[i]->mMaxHoleSize >> IMMIX_LINE_BITS;
         if (slot>=BLOCK_OFSIZE_COUNT)
            slot = BLOCK_OFSIZE_COUNT-1;
         mNextFreeBlockOfSize[slot] = i;
      }

      for(int i=BLOCK_OFSIZE_COUNT-2;i>=0;i--)
         if (mNextFreeBlockOfSize[i]>mNextFreeBlockOfSize[i+1])
            mNextFreeBlockOfSize[i] = mNextFreeBlockOfSize[i+1];

      mZeroList.clear();
   }

   void backgroundProcessFreeList(bool inJit)
   {
      mZeroListQueue = 0;
      // Bisection: skip the async zeroing entirely - claimers then zero their
      // blocks inline (ZEROED_NOT path), removing the zero-vs-claim race
      // from the equation.
      if (gcBisectFlag("HXCPP_NO_ASYNC_ZERO"))
      {
         mZeroList.clear();
         return;
      }
      #ifdef HX_GC_ZERO_EARLY
      mZeroList.setSize(mFreeBlocks.size());
      memcpy( &mZeroList[0], &mFreeBlocks[0], mFreeBlocks.size()*sizeof(void *));

      StartThreadJobs(tpjAsyncZero, mZeroList.size(),true);
      #else
      if ( MAX_GC_THREADS>1 && mFreeBlocks.size()>4)
      {
         mZeroList.setSize(mFreeBlocks.size());
         memcpy( &mZeroList[0], &mFreeBlocks[0], mFreeBlocks.size()*sizeof(void *));

         // Only use one thread for parallel zeroing.  Try to get though the work wihout
         //  slowing down the main thread
         StartThreadJobs(inJit ? tpjAsyncZeroJit : tpjAsyncZero, mZeroList.size(), false, 1);
      }
      #endif
   }




   size_t MemLarge()
   {
      return mLargeAllocated;
   }

   size_t MemReserved()
   {
      return mLargeAllocated + (mAllBlocksCount*IMMIX_USEFUL_LINES<<IMMIX_LINE_BITS);
   }

   size_t MemCurrent()
   {
      return mLargeAllocated + (mCurrentRowsInUse<<IMMIX_LINE_BITS);
   }

   size_t MemUsage()
   {
      return mLargeAllocated + (mRowsInUse<<IMMIX_LINE_BITS);
   }

   bool IsAllBlock(BlockData *block)
   {
      if (mAllBlocks.size())
      {
         int min = 0;
         int max = mAllBlocks.size()-1;
         if (block==mAllBlocks[0]->mPtr)
            return true;
         if (block==mAllBlocks[max]->mPtr)
            return true;
         if (block>mAllBlocks[0]->mPtr && block<mAllBlocks[max]->mPtr)
         {
            while(min<max-1)
            {
               int mid = (max+min)>>1;
               if (mAllBlocks[mid]->mPtr==block)
                  return true;

               if (mAllBlocks[mid]->mPtr<block)
                  min = mid;
               else
                  max = mid;
            }
         }
      }
      return false;
   }

   MemType GetMemType(void *inPtr)
   {
      BlockData *block = (BlockData *)( ((size_t)inPtr) & IMMIX_BLOCK_BASE_MASK);

      bool isBlock = IsAllBlock(block);
      /*
      bool found = false;
      for(int i=0;i<mAllBlocks.size();i++)
      {
         if (mAllBlocks[i]==block)
         {
            found = true;
            break;
         }
      }
      */

      if (isBlock)
         return memBlock;

      for(int i=0;i<mLargeList.size();i++)
      {
         unsigned int *blob = mLargeList[i] + 2;
         if (blob==inPtr)
            return memLarge;
      }

      return memUnmanaged;
   }


   size_t mRowsInUse;
   size_t mCurrentRowsInUse;
   // Row count at the end of the last collection.  MMTk's Immix triggers its
   // GC on "allocation since last GC", not on total heap usage; this is the
   // same signal for the frame scheduler (see RowsAllocatedSinceGC).
   size_t mRowsAtLastCollect;
   size_t mLargeAllocSpace;
   size_t mLargeAllocForceRefresh;
   size_t mLargeAllocated;
   size_t mTotalAfterLastCollect;
   size_t mAllBlocksCount;
   double mGenerationalRetainEstimate;

   hx::MarkContext mMarker;

   volatile int mNextFreeBlockOfSize[BLOCK_OFSIZE_COUNT];
   volatile int mThreadJobId;

   BlockList mAllBlocks;
   BlockList mFreeBlocks;
   BlockList mZeroList;
   volatile int mZeroListQueue;

   // Incremental sweep state (main thread only).
   BlockList mSweepList;
   BlockDataStats mSweepStats;
   int mSweepCursor;
   bool mSweepActive;
   size_t mSweepOwnedRows;

   LargeList mLargeList;
   std::mutex mLargeListLock;
   hx::QuickVec<LocalAllocator *> mLocalAllocs;
   LocalAllocator *mLocalPool[LOCAL_POOL_SIZE];
   hx::QuickVec<unsigned int *> largeObjectRecycle;
};



namespace hx
{

MarkChunk *MarkChunk::swapForNew()
{
   // MMTk's ObjectBarrier enqueues the modified object where the workers can
   // pick it up immediately; pushJobNoWake left full referrer chunks sitting
   // on the global list while the workers slept, so every chunk pushed after
   // the initial drain accumulated until the finish pause drained the whole
   // backlog in one stop-the-world step (finish mark grew with the frame
   // rate: 24-28ms at ~800fps).  pushJob wakes a parked worker and still
   // returns a fresh chunk for the next barrier buffer.
   return sGlobalChunks.pushJob(this,true);
}



void MarkConservative(int *inBottom, int *inTop,hx::MarkContext *__inCtx)
{
   #ifdef VERIFY_STACK_READ
   VerifyStackRead(inBottom, inTop);
   #endif

   #ifdef SHOW_MEM_EVENTS
   GCLOG("Mark conservative %p...%p (%d) [...", inBottom, inTop, (int)(inTop-inBottom) );
     #ifdef HX_WATCH
     GCLOG("\n");
     #endif
   #endif

   #ifdef HXCPP_STACK_UP
   int *start = inTop-1;
   inTop = inBottom+1;
   inBottom = start;
   #endif

   if (sizeof(int)==4 && sizeof(void *)==8)
   {
      // Can't start pointer on last integer boundary...
      inTop--;
   }

   void *prev = 0;
   void *lastPin = 0;
   #ifdef HX_WATCH
   void *lastWatch = 0;
   bool isWatch = false;
   #endif

   #ifdef HXCPP_GC_GENERATIONAL
   // If this is a generational mark, then the byte marker has not been increased.
   // Previous mark Ids are therfore from more than 1 collection ago
   bool allowPrevious = !__inCtx->isGenerational;
   #else
   const bool allowPrevious = true;
   #endif


   for(int *ptr = inBottom ; ptr<inTop; ptr++)
   {
      void *vptr = *(void **)ptr;

      MemType mem;
      #ifdef HXCPP_ALIGN_ALLOC
      const size_t validObjectMask = 0x07;
      #else
      const size_t validObjectMask = 0x03;
      #endif

      if (vptr && !((size_t)vptr & validObjectMask) && vptr!=prev && vptr!=lastPin)
      {

         #ifdef PROFILE_COLLECT
         hx::localCount++;
         #endif
         MemType mem = sGlobalAlloc->GetMemType(vptr);

         #ifdef HX_WATCH
         isWatch = false;
         if (hxInWatchList(vptr) && vptr!=lastWatch)
         {
            isWatch = true;
            lastWatch = vptr;
            GCLOG("********* Watch location conservative mark %p:%d\n",vptr,mem);
         }
         #endif

         if (mem!=memUnmanaged)
         {
            if (mem==memLarge)
            {
               unsigned char &mark = ((unsigned char *)(vptr))[HX_ENDIAN_MARK_ID_BYTE];
               if (mark!=gByteMarkID)
                  mark = gByteMarkID;
            }
            else
            {
               BlockData *block = (BlockData *)( ((size_t)vptr) & IMMIX_BLOCK_BASE_MASK);
               BlockDataInfo *info = (*gBlockInfo)[block->mId];

               int pos = (int)(((size_t)vptr) & IMMIX_BLOCK_OFFSET_MASK);
               AllocType t = sgCheckInternalOffset ?
                     info->GetEnclosingAllocType(pos-sizeof(int),&vptr, allowPrevious):
                     info->GetAllocType(pos-sizeof(int), allowPrevious);

               #ifdef HX_WATCH
               if (!isWatch && hxInWatchList(vptr))
               {
                  isWatch = true;
                  GCLOG("********* Watch location conservative mark offset %p:%d\n",vptr,mem);
               }
               #endif


               if ( t==allocObject )
               {
                  #ifdef HX_WATCH
                  if (isWatch)
                  {
                     GCLOG(" Mark object %p (%p)\n", vptr,ptr);
                  }
                  #endif
                  hx::MarkObjectAlloc( ((hx::Object *)vptr), __inCtx );
                  lastPin = vptr;
                  info->pin();
               }
               else if (t==allocString)
               {
                  #ifdef HX_WATCH
                  if (isWatch)
                     GCLOG(" Mark string %p (%p)\n", vptr,ptr);
                  #endif
                  HX_MARK_STRING(vptr);
                  lastPin = vptr;
                  info->pin();
               }
               else if (t==allocMarked)
               {
                  #ifdef HX_WATCH
                  if (isWatch)
                     GCLOG(" pin alloced %p (%p)\n", vptr,ptr);
                  #endif
                  lastPin = vptr;
                  info->pin();
               }
               #ifdef HX_WATCH
               else // memBlock
               {
                  if (isWatch)
                  {
                     GCLOG(" missed watch %p:%d\n", vptr,t);
                     int x = info->GetAllocType(pos-sizeof(int),allowPrevious);
                     int y = info->GetEnclosingAllocType(pos-sizeof(int),&vptr,allowPrevious);
                     #ifdef HXCPP_GC_NURSERY
                     void *nptr;
                     int z = info->GetEnclosingNurseryType(pos-sizeof(int),&nptr);
                     #else
                     int z = 0;
                     #endif
                     printf("but got alloc type=%d, enclosing=%d nurs=%d o=%d\n",x,y,z,sgCheckInternalOffset);
                  }
               }
               #endif
            }
         }
         // GCLOG(" rejected %p %p %d %p %d=%d\n", ptr, vptr, !((size_t)vptr & 0x03), prev,
         // sGlobalAlloc->GetMemType(vptr) , memUnmanaged );
      }
   }
   #ifdef SHOW_MEM_EVENTS
   GCLOG("...]\n");
   #endif
}

} // namespace hx


// --- LocalAllocator -------------------------------------------------------
//
// One per thread ...

static int sFragIgnore=0;

class LocalAllocator : public hx::StackContext
{
   int            mCurrentHole;
   int            mCurrentHoles;
   HoleRange     *mCurrentRange;
   int           *mFraggedRows;

   bool           mMoreHoles;

   #ifndef HXCPP_EXPLICIT_STACK_EXTENT
   int *mTopOfStack;
   int *mBottomOfStack;
   #endif

   hx::RegisterCaptureBuffer mRegisterBuf;
   int                   mRegisterBufSize;

   #ifndef HXCPP_SINGLE_THREADED_APP
   bool            mGCFreeZone;
   HxSemaphore     mReadyForCollect;
   HxSemaphore     mCollectDone;
   #endif

   int             mID;


   // Must be called locked
   ~LocalAllocator()
   {
   }

public:
   bool            mGlobalStackLock;
   int             mStackLocks;

public:
   LocalAllocator(int *inTopOfStack=0)
   {
      Reset();

      #if defined(HXCPP_GC_GENERATIONAL) || defined(HXCPP_GC_INCREMENTAL)
      mOldReferrers = 0;
      #endif

      AttachThread(inTopOfStack);
   }


   void AttachThread(int *inTopOfStack)
   {
      #ifndef HXCPP_EXPLICIT_STACK_EXTENT
      mTopOfStack = mBottomOfStack = inTopOfStack;
      #endif

      mRegisterBufSize = 0;
      mStackLocks = 0;
      mGlobalStackLock = false;
      #ifdef HX_WINDOWS
      mID = GetCurrentThreadId();
      #endif

      #if defined(HXCPP_GC_GENERATIONAL) || defined(HXCPP_GC_INCREMENTAL)
      if (mOldReferrers)
      {
         GCLOG("Uncleaned referrers\n");
      }

      if (sGcMode==gcmGenerational)
         mOldReferrers = hx::sGlobalChunks.alloc();
      else
         mOldReferrers = hx::gIncrementalMarking ? hx::sGlobalChunks.alloc() : 0;
      #endif


      // It is in the free zone - wait for 'SetTopOfStack' to activate
      #ifndef HXCPP_SINGLE_THREADED_APP
      mGCFreeZone = true;
      mReadyForCollect.Set();
      #endif
      sGlobalAlloc->AddLocal(this);
   }

   void Release()
   {
      mStackLocks = 0;

      onThreadDetach();

      #ifndef HXCPP_SINGLE_THREADED_APP
      if (!mGCFreeZone)
         EnterGCFreeZone();
      #endif

      std::lock_guard<std::recursive_mutex> lock(*gThreadStateChangeLock);

      #ifdef HX_WINDOWS
      mID = 0;
      #endif

      #if defined(HXCPP_GC_GENERATIONAL) || defined(HXCPP_GC_INCREMENTAL)
      if (mOldReferrers)
      {
         if ( mOldReferrers->count )
            hx::sGlobalChunks.pushJob( mOldReferrers, false );
         else
            hx::sGlobalChunks.free( mOldReferrers );
         mOldReferrers = 0;
      }
      #endif

      #ifndef HXCPP_EXPLICIT_STACK_EXTENT
      mTopOfStack = mBottomOfStack = 0;
      #endif

      sGlobalAlloc->RemoveLocalLocked(this);

      hx::tlsStackContext = 0;

      if (!sGlobalAlloc->ReturnToPoolLocked(this))
         delete this;
   }

   void Reset()
   {
      allocBase = 0;
      mCurrentHole = 0;
      mCurrentHoles = 0;
      mFraggedRows = 0;
      #ifdef HXCPP_GC_NURSERY
      spaceFirst = 0;
      spaceOversize = 0;
      #else
      spaceEnd = 0;
      spaceStart = 0;
      #endif
      mMoreHoles = false;
   }

   // The main of haxe calls SetTopOfStack(top,false)
   //   via hxcpp_set_top_of_stack or HX_TOP_OF_STACK in HxcppMain.cpp/Macros.h
   // The means "register current thread indefinitely"
   // Other places may call this to ensure the the current thread is registered
   //  indefinitely (until forcefully revoked)
   //
   // Normally libraries/mains will then let this dangle.
   //
   // However after the main, on android it calls SetTopOfStack(0,true), to unregister the thread,
   // because it is likely to be the ui thread, and the remaining call will be from
   // callbacks from the render thread.
   // 
   // When threads want to attach temporarily, they will call
   // gc_set_top_of_stack(top,true)
   //  -> SetTopOfStack(top,true)
   //    do stuff...
   // gc_set_top_of_stack(0,true)
   //  -> SetTopOfStack(0,true)
   //
   //  OR
   //
   //  PushTopOfStack(top)
   //   ...
   //  PopTopOfStack
   //
   //  However, we really want the gc_set_top_of_stack(top,true) to allow recursive locks so:
   //
   //  SetTopOfStack(top,false) -> ensure global stack lock exists
   //  SetTopOfStack(top,true) -> add stack lock
   //  SetTopOfStack(0,_) -> pop stack lock. If all gone, clear global stack lock
   //

   #ifdef HXCPP_EXPLICIT_STACK_EXTENT // {

   void SetTopOfStack(int *inTop,bool inPush) { }
   void PushTopOfStack(void *inTop) { }
   void PopTopOfStack() { }
   void SetBottomOfStack(int *inBottom) { }
   void PauseForCollect() { }
   void EnterGCFreeZone() { }
   bool TryGCFreeZone() { return true; }
   bool TryExitGCFreeZone() { return false; }
   void ExitGCFreeZoneLocked() { }


   #else // } !HXCPP_EXPLICIT_STACK_EXTENT {
   void SetTopOfStack(int *inTop,bool inPush)
   {
      if (inTop)
      {
         if (!mTopOfStack)
            mTopOfStack = inTop;
         // EMSCRIPTEN the stack grows upwards - not wasm.
         // It could be that the main routine was called from deep with in the stack,
         //  then some callback was called from a higher location on the stack
         #ifdef HXCPP_STACK_UP
         else if (inTop < mTopOfStack)
            mTopOfStack = inTop;
         #else
         else if (inTop > mTopOfStack)
            mTopOfStack = inTop;
         #endif

         if (inPush)
            mStackLocks++;
         else
            mGlobalStackLock = true;

         #ifndef HXCPP_SINGLE_THREADED_APP
         if (mGCFreeZone)
            ExitGCFreeZone();
         #endif
      }
      else
      {
         if (mStackLocks>0)
            mStackLocks--;
         else
            mGlobalStackLock = false;

         if (!mStackLocks && !mGlobalStackLock)
         {
            Release();
         }
      }

      #ifdef VerifyStackRead
      VerifyStackRead(mBottomOfStack, mTopOfStack)
      #endif
   }


   void PushTopOfStack(void *inTop)
   {
      SetTopOfStack((int *)inTop,true);
   }


   void PopTopOfStack()
   {
      mStackLocks--;
      if (mStackLocks<=0 && !mGlobalStackLock)
      {
         Release();
      }
   }



   void SetBottomOfStack(int *inBottom)
   {
      mBottomOfStack = inBottom;
      #ifdef VerifyStackRead
      VerifyStackRead(mBottomOfStack, mTopOfStack)
      #endif
   }


   void PauseForCollect()
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      volatile int dummy = 1;
      mBottomOfStack = (int *)&dummy;
      CAPTURE_REGS;
      #ifdef VerifyStackRead
      VerifyStackRead(mBottomOfStack, mTopOfStack)
      #endif

      if (sgIsCollecting)
         CriticalGCError("Bad Allocation while collecting - from finalizer?");

      mReadyForCollect.Set();
      mCollectDone.Wait();
      #endif
   }

   void EnterGCFreeZone()
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      volatile int dummy = 1;
      mBottomOfStack = (int *)&dummy;
      if (mTopOfStack)
      {
         CAPTURE_REGS;
      }
      #ifdef VerifyStackRead
      VerifyStackRead(mBottomOfStack, mTopOfStack)
      #endif

      mGCFreeZone = true;
      mReadyForCollect.Set();
      #endif
   }

   bool TryGCFreeZone()
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      if (mGCFreeZone)
         return false;
      EnterGCFreeZone();
      #endif
      return true;
   }

   bool TryExitGCFreeZone()
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      if (!mGCFreeZone)
         return false;
      ExitGCFreeZone();
      return true;
      #endif
      return false;
   }


   void ExitGCFreeZone()
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      if (!mGCFreeZone)
         CriticalGCError("GCFree Zone mismatch");

      std::lock_guard<std::recursive_mutex> lock(*gThreadStateChangeLock);
      mReadyForCollect.Reset();
      mGCFreeZone = false;
      #endif
   }
        // For when we already hold the lock
   void ExitGCFreeZoneLocked()
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      mReadyForCollect.Reset();
      mGCFreeZone = false;
      #endif
   }



   // Called by the collecting thread to make sure this allocator is paused.
   // The collecting thread has the lock, and will not be releasing it until
   //  it has finished the collect.
   //
   //  The mGCFreeZone is set without a lock in the EnterGCFreeZone code, and then
   //   mReadyForCollect is set.  So it is possible the mGCFreeZone check may or may not
   //   trigger.  If this call happens first, mGCFreeZone will be zero, and mReadyForCollect
   //   will wait.  By this time mGCFreeZone will be set and the next call not check
   //   mReadyForCollect again.  If this one happens later, it is possible mReadyForCollect
   //   will not be waited on. mReadyForCollect will be cleared when the zone is left.
   //
   //  The mMoreHoles/spaceOversize/spaceEnd get zeroed without a lock.  The timing should
   //   not be critical since the allocation code shold expect that these are volatile.
   //   If the allocation works, all is good.  If it fails then the collection will happed soon.
   #if defined(__has_feature)
     #if __has_feature(thread_sanitizer)
      __attribute__((no_sanitize("thread")))
     #endif
   #endif
   void WaitForSafe()
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      if (!mGCFreeZone)
      {
         // Cause allocation routines to fail ...
         mMoreHoles = false;
         #ifdef HXCPP_GC_NURSERY
         spaceOversize = 0;
         #else
         spaceEnd = 0;
         #endif
         mReadyForCollect.Wait();
      }
      #endif
   }

   void ReleaseFromSafe()
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      if (!mGCFreeZone)
         mCollectDone.Set();
      #endif
   }

   #endif // }  HXCPP_EXPLICIT_STACK_EXTENT


   // Capture the current stack extent and registers without collecting.
   // The incremental cycle calls this on the collecting thread before it
   // scans that thread's roots.
   void CaptureRegisters()
   {
      #ifndef HXCPP_EXPLICIT_STACK_EXTENT
      CAPTURE_REGS;
      #endif
   }


   void CaptureForMark()
   {
      #ifndef HXCPP_EXPLICIT_STACK_EXTENT
      volatile int dummy = 1;
      mBottomOfStack = (int *)&dummy;

      CAPTURE_REGS;

      if (!mTopOfStack)
         mTopOfStack = mBottomOfStack;

      #ifdef HXCPP_STACK_UP
      if (mBottomOfStack < mTopOfStack)
         mTopOfStack = mBottomOfStack;
      #else
      if (mBottomOfStack > mTopOfStack)
         mTopOfStack = mBottomOfStack;
      #endif
      #endif
   }


   void SetupStackAndCollect(bool inMajor, bool inForceCompact, bool inLocked=false,bool inFreeIsFragged=false) HXCPP_OVERRIDE
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
        #if HXCPP_DEBUG
        if (mGCFreeZone)
           CriticalGCError("Collecting from a GC-free thread");
        #endif
      #endif

      #ifndef HXCPP_EXPLICIT_STACK_EXTENT
      volatile int dummy = 1;
      mBottomOfStack = (int *)&dummy;

      CAPTURE_REGS;

      if (!mTopOfStack)
         mTopOfStack = mBottomOfStack;

      // EMSCRIPTEN the stack grows upwards
      #ifdef HXCPP_STACK_UP
      if (mBottomOfStack < mTopOfStack)
         mTopOfStack = mBottomOfStack;
      #else
      if (mBottomOfStack > mTopOfStack)
         mTopOfStack = mBottomOfStack;
      #endif

      #ifdef VerifyStackRead
      VerifyStackRead(mBottomOfStack, mTopOfStack)
      #endif

      #endif


      sGlobalAlloc->Collect(inMajor, inForceCompact, inLocked, inFreeIsFragged);
   }



   void ExpandAlloc(int &ioSize)
   {
      #ifdef HXCPP_ALIGN_ALLOC
      // Do nothing here - aligning to the end of the row will bump the
      // next allocation, so it's not clear if its a good idea.
      #else
         #ifdef HXCPP_GC_NURSERY
         int spaceStart = spaceFirst - allocBase - 4;
         int spaceEnd = spaceOversize - allocBase - 4;
         #endif

         int size = ioSize + sizeof(int);
         int end = spaceStart + size;
         if (end <= spaceEnd)
         {
            int linePad = IMMIX_LINE_LEN - (end & (IMMIX_LINE_LEN-1));
            if (linePad>0 && linePad<=64)
               ioSize += linePad;
         }
      #endif
   }


   void *CallAlloc(int inSize,unsigned int inObjectFlags) HXCPP_OVERRIDE
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      #if HXCPP_DEBUG
      if (mGCFreeZone)
         CriticalGCError("Allocating from a GC-free thread");
      #endif
      if (hx::gPauseForCollect)
         PauseForCollect();
      #endif

      if (inSize==0)
         return hx::emptyAlloc;

      #if defined(HXCPP_VISIT_ALLOCS) && (defined(HXCPP_M64)||defined(HXCPP_ARM64))
      // Make sure we can fit a relocation pointer
      int allocSize = sizeof(int) + std::max(8,inSize);
      #else
      int allocSize = sizeof(int) + inSize;
      #endif

      #if HXCPP_GC_DEBUG_LEVEL>0
      if (inSize & 3) DebuggerTrap();
      #endif

      while(1)
      {
         #ifdef HXCPP_GC_NURSERY
            unsigned char *buffer = spaceFirst;
            #ifdef HXCPP_ALIGN_ALLOC
            if ((size_t)buffer & 0x4 )
               buffer += 4;
            #endif
            unsigned char *end = buffer + allocSize;

            if ( end <= spaceOversize )
            {
               spaceFirst = end;

               int size = allocSize - 4;
               ((unsigned int *)buffer)[-1] = size | inObjectFlags;

               #if defined(HXCPP_GC_CHECK_POINTER) && defined(HXCPP_GC_DEBUG_ALWAYS_MOVE)
               hx::GCOnNewPointer(buffer);
               #endif

               return buffer;
            }
            // spaceOversize might have been set to zero for quick-termination of alloc.
            unsigned char *s = spaceOversize;
            if (s>spaceFirst && mFraggedRows)
               *mFraggedRows += (s - spaceFirst)>>IMMIX_LINE_BITS;
         #else
            #ifdef HXCPP_ALIGN_ALLOC
            if (!((size_t)spaceStart & 0x4 ))
               spaceStart += 4;
            #endif

            int end = spaceStart + allocSize;
            if (end <= spaceEnd)
            {
               unsigned int *buffer = (unsigned int *)(allocBase + spaceStart);

               int startRow = spaceStart>>IMMIX_LINE_BITS;
               allocStartFlags[ startRow ] |= hx::gImmixStartFlag[spaceStart &127];

               int endRow = (end+(IMMIX_LINE_LEN-1))>>IMMIX_LINE_BITS;

               *buffer++ = inObjectFlags | hx::gMarkID |
                     (inSize<<IMMIX_ALLOC_SIZE_SHIFT) | (endRow-startRow);

               spaceStart = end;

               #if defined(HXCPP_GC_CHECK_POINTER) && defined(HXCPP_GC_DEBUG_ALWAYS_MOVE)
               hx::GCOnNewPointer(buffer);
               #endif

               #ifdef HXCPP_TELEMETRY
               __hxt_gc_alloc(buffer, inSize);
               #endif

               return buffer;
            }
            if (mFraggedRows)
            {
               int frag = spaceEnd-spaceStart;
               if (frag>0)
                  *mFraggedRows += frag>>IMMIX_LINE_BITS;
            }
         #endif


         if (mMoreHoles)
         {
            #ifdef HXCPP_GC_NURSERY
            spaceFirst = allocBase + mCurrentRange[mCurrentHole].start + sizeof(int);
            spaceOversize = spaceFirst + mCurrentRange[mCurrentHole].length;
            #else
            spaceStart = mCurrentRange[mCurrentHole].start;
            spaceEnd = spaceStart + mCurrentRange[mCurrentHole].length;
            #endif
            mCurrentHole++;
            mMoreHoles = mCurrentHole<mCurrentHoles;

         }
         else
         {
            // For opmtimized windows 64 builds, this dummy var technique does not
            //  quite work, since the compiler might recycle one of the earlier stack
            //  slots, and place dummy behind the stack values we are actually trying to
            //  capture.  Moving the dummy into the GetFreeBlock seems to have fixed this.
            //  Not 100% sure this is the best answer, but it is working.
            //volatile int dummy = 1;
            //mBottomOfStack = (int *)&dummy;
            //CAPTURE_REGS;

            BlockDataInfo *info = sGlobalAlloc->GetFreeBlock(allocSize,this);

            allocBase = (unsigned char *)info->mPtr;
            mCurrentRange = info->mRanges;
            allocStartFlags = info->allocStart;
            mCurrentHoles = info->mHoles;
            mFraggedRows = &info->mFraggedRows;
            #ifdef HXCPP_GC_NURSERY
            spaceFirst = allocBase + mCurrentRange->start + sizeof(int);
            spaceOversize = spaceFirst + mCurrentRange->length;
            #else
            spaceStart = mCurrentRange->start;
            spaceEnd = spaceStart + mCurrentRange->length;
            #endif
            mCurrentHole = 1;
            mMoreHoles = mCurrentHole<mCurrentHoles;
         }

         // Other thread may have started collect, in which case we may just
         //  overwritted the 'mMoreHoles' and 'spaceEnd' termination attempt
         if (hx::gPauseForCollect)
         {
            mMoreHoles = 0;
            #ifdef HXCPP_GC_NURSERY
            spaceOversize = 0;
            #else
            spaceEnd = 0;
            #endif
         }
      }
      return 0;
   }

   #ifdef HXCPP_VISIT_ALLOCS
   void Visit(hx::VisitContext *__inCtx)
   {
      #ifdef HXCPP_COMBINE_STRINGS
      if (stringSet)
      {
         __inCtx->visitObject( (hx::Object **)&stringSet);
      }
      #endif
   }
   #endif


   void Mark(hx::MarkContext *__inCtx)
   {
      #ifndef HXCPP_SINGLE_THREADED_APP
      if (!mTopOfStack)
      {
         Reset();
         return;
      }
      #endif

      #ifdef SHOW_MEM_EVENTS
      //int here = 0;
      //GCLOG("=========== Mark Stack ==================== %p ... %p (%p)\n",mBottomOfStack,mTopOfStack,&here);
      #endif

      #ifdef HXCPP_DEBUG
         MarkPushClass("Stack",__inCtx);
         MarkSetMember("Stack",__inCtx);

         #ifdef HXCPP_EXPLICIT_STACK_EXTENT
           hx::MarkConservative( (int *)emscripten_stack_get_current(),(int *)emscripten_stack_get_base(), __inCtx);
         #else
         if (mTopOfStack && mBottomOfStack)
            hx::MarkConservative(mBottomOfStack, mTopOfStack , __inCtx);
         #endif

         #ifdef HXCPP_SCRIPTABLE
            MarkSetMember("ScriptStack",__inCtx);
            hx::MarkConservative((int *)(stack), (int *)(pointer),__inCtx);
         #endif
         MarkSetMember("Registers",__inCtx);
         hx::MarkConservative(CAPTURE_REG_START, CAPTURE_REG_END, __inCtx);


         MarkPopClass(__inCtx);
      #else

         #ifdef HXCPP_EXPLICIT_STACK_EXTENT
           hx::MarkConservative( (int *)emscripten_stack_get_current(), (int *) emscripten_stack_get_base(), __inCtx);
         #else
            if (mTopOfStack && mBottomOfStack)
               hx::MarkConservative(mBottomOfStack, mTopOfStack , __inCtx);
            hx::MarkConservative(CAPTURE_REG_START, CAPTURE_REG_END, __inCtx);
         #endif

         #ifdef HXCPP_SCRIPTABLE
            hx::MarkConservative((int *)(stack), (int *)(pointer),__inCtx);
         #endif
      #endif

      #ifdef HXCPP_COMBINE_STRINGS
         if (stringSet)
            MarkMember( *(hx::Object **)&stringSet, __inCtx);
      #endif

      Reset();

   }

};




inline LocalAllocator *GetLocalAlloc(bool inAllowEmpty=false)
{
   #ifndef HXCPP_SINGLE_THREADED_APP
      LocalAllocator *result = (LocalAllocator *)(hx::ImmixAllocator *)hx::tlsStackContext;
      if (!result && !inAllowEmpty)
         hx::BadImmixAlloc();

      return result;
   #else
      return (LocalAllocator *)hx::gMainThreadContext;
   #endif
}

#ifndef HXCPP_SINGLE_THREADED_APP
void WaitForSafe(LocalAllocator *inAlloc)
{
   inAlloc->WaitForSafe();
}

void ReleaseFromSafe(LocalAllocator *inAlloc)
{
   inAlloc->ReleaseFromSafe();
}
#endif

void MarkLocalAlloc(LocalAllocator *inAlloc,hx::MarkContext *__inCtx)
{
   inAlloc->Mark(__inCtx);
}

void CaptureLocalStack(LocalAllocator *inAlloc, int *inBottom)
{
   inAlloc->SetBottomOfStack(inBottom);
   inAlloc->CaptureRegisters();
}

void ClearPooledAlloc(LocalAllocator *inAlloc)
{
   inAlloc->Reset();
}

#ifdef HXCPP_VISIT_ALLOCS
void VisitLocalAlloc(LocalAllocator *inAlloc,hx::VisitContext *__inCtx)
{
   inAlloc->Visit(__inCtx);
}
#endif



void CollectFromThisThread(bool inMajor,bool inForceCompact)
{
   LocalAllocator *la = GetLocalAlloc();
   la->SetupStackAndCollect(inMajor,inForceCompact);
}

namespace hx
{

void *ImmixAllocator::CallAlloc(int inSize,unsigned int inObjectFlags)
{
   return reinterpret_cast<LocalAllocator *>(this)->CallAlloc(inSize, inObjectFlags);
}



void PauseForCollect()
{
   GetLocalAlloc()->PauseForCollect();
}



void EnterGCFreeZone()
{
   #ifndef HXCPP_SINGLE_THREADED_APP
      LocalAllocator *tla = GetLocalAlloc();
      tla->EnterGCFreeZone();
   #endif
}


bool TryGCFreeZone()
{
   #ifndef HXCPP_SINGLE_THREADED_APP
      LocalAllocator *tla = GetLocalAlloc();
      return tla->TryGCFreeZone();
   #else
      return false;
   #endif
}

bool TryExitGCFreeZone()
{
   #ifndef HXCPP_SINGLE_THREADED_APP
      LocalAllocator *tla = GetLocalAlloc(true);
      if (!tla)
         return 0;
      bool left = tla->TryExitGCFreeZone();
      return left;
   #else
      return false;
   #endif
}


void ExitGCFreeZone()
{
   #ifndef HXCPP_SINGLE_THREADED_APP
      LocalAllocator *tla = GetLocalAlloc();
      tla->ExitGCFreeZone();
   #endif
}

void ExitGCFreeZoneLocked()
{
   #ifndef HXCPP_SINGLE_THREADED_APP
      LocalAllocator *tla = GetLocalAlloc();
      tla->ExitGCFreeZoneLocked();
   #endif
}

void InitAlloc()
{
   for(int i=0;i<IMMIX_LINE_LEN;i++)
      gImmixStartFlag[i] = 1<<( i>>2 ) ;

   hx::CommonInitAlloc();
   sgAllocInit = true;
   sGlobalAlloc = new GlobalAllocator();
   sgFinalizers = new FinalizerList();
   sFinalizerLock = new std::mutex();
   sGCRootLock = new std::mutex();
   hx::Object tmp;
   void **stack = *(void ***)(&tmp);
   sgObject_root = stack[0];

   //GCLOG("__root pointer %p\n", sgObject_root);
   gMainThreadContext =  new LocalAllocator();

   tlsStackContext = gMainThreadContext;

   ExitGCFreeZone();

   // Setup main thread ...
   __hxcpp_thread_current();

   gMainThreadContext->onThreadAttach();
}


void GCPrepareMultiThreaded()
{
   #ifdef HXCPP_SINGLE_THREADED_APP
   CriticalGCError("GCPrepareMultiThreaded called with HXCPP_SINGLE_THREADED_APP");
   #endif
}



void SetTopOfStack(int *inTop,bool inForce)
{
   bool threadAttached = false;
   if (inTop)
   {
      if (!sgAllocInit)
         InitAlloc();
      else
      {
         if (tlsStackContext==0)
         {
            GCPrepareMultiThreaded();
            RegisterCurrentThread(inTop);
            threadAttached = true;
         }
      }
   }

   LocalAllocator *tla = (LocalAllocator *)(hx::ImmixAllocator *)tlsStackContext;

   if (tla)
   {
      tla->SetTopOfStack(inTop,inForce);
      if (threadAttached)
         tla->onThreadAttach();
   }
}


void *InternalNew(int inSize,bool inIsObject)
{
   // HX_STACK_FRAME("GC", "new", 0, "GC::new", __FILE__, __LINE__, 0)

   #ifdef HXCPP_DEBUG
   if (sgSpamCollects && sgAllocsSinceLastSpam>=sgSpamCollects)
   {
      //GCLOG("InternalNew spam\n");
      CollectFromThisThread(false,false);
   }
   _hx_atomic_add(&sgAllocsSinceLastSpam, 1);
   #endif

   if (inSize>=IMMIX_LARGE_OBJ_SIZE)
   {
      void *result = sGlobalAlloc->AllocLarge(inSize, true);
      return result;
   }
   else
   {
      LocalAllocator *tla = GetLocalAlloc();

      if (inIsObject)
      {
         void* result = tla->CallAlloc(inSize,IMMIX_ALLOC_IS_CONTAINER);
         return result;
      }
      else
      {
         #if defined(HXCPP_GC_MOVING) && defined(HXCPP_M64)
         if (inSize<8)
            return tla->CallAlloc(8,0);
         #endif

         void* result = tla->CallAlloc( (inSize+3)&~3,0);
         return result;
      }
   }
}


// Force global collection - should only be called from 1 thread.
int InternalCollect(bool inMajor,bool inCompact)
{
   if (!sgAllocInit)
       return 0;

   GetLocalAlloc()->SetupStackAndCollect(inMajor, inCompact);

   return sGlobalAlloc->MemUsage();
}

inline unsigned int ObjectSize(void *inData)
{
   unsigned int header = ((unsigned int *)(inData))[-1];

   return (header & IMMIX_ALLOC_ROW_COUNT) ?
            ( (header & IMMIX_ALLOC_SIZE_MASK) >> IMMIX_ALLOC_SIZE_SHIFT) :
             ((unsigned int *)(inData))[-2];
}


unsigned int ObjectSizeSafe(void *inData)
{
   unsigned int header = ((unsigned int *)(inData))[-1];
   if (header & HX_GC_CONST_ALLOC_BIT)
      return 0;

   #ifdef HXCPP_GC_NURSERY
   if (!(header & 0xff000000))
   {
      // Small object
      if (header & 0x00ffffff)
         return header & 0x0000ffff;
      // Large object
   }
   #endif


   return (header & IMMIX_ALLOC_ROW_COUNT) ?
            ( (header & IMMIX_ALLOC_SIZE_MASK) >> IMMIX_ALLOC_SIZE_SHIFT) :
             ((unsigned int *)(inData))[-2];
}

void GCChangeManagedMemory(int inDelta, const char *inWhy)
{
   sGlobalAlloc->onMemoryChange(inDelta, inWhy);
}

void InternalReleaseMem(void *inMem)
{
   if (inMem)
   {
      unsigned int s = ObjectSizeSafe(inMem);
      if (s>=IMMIX_LARGE_OBJ_SIZE)
      {
         //Can release asap
         sGlobalAlloc->FreeLarge(inMem);
      }
   }
}



void *InternalRealloc(int inFromSize, void *inData,int inSize, bool inExpand)
{
   if (inData==0 || inFromSize==0)
   {
      if (inData)
         InternalReleaseMem(inData);
      return hx::InternalNew(inSize,false);
   }

   // HX_STACK_FRAME("GC", "realloc", 0, "GC::relloc", __FILE__ , __LINE__, 0)

   #ifdef HXCPP_DEBUG
   if (sgSpamCollects && sgAllocsSinceLastSpam>=sgSpamCollects)
   {
      //GCLOG("InternalNew spam\n");
      CollectFromThisThread(false,false);
   }
   _hx_atomic_add(&sgAllocsSinceLastSpam, 1);
   #endif

   void *new_data = 0;
   if (inSize==0)
   {
      new_data = hx::emptyAlloc;
   }
   else if (inSize>=IMMIX_LARGE_OBJ_SIZE)
   {
      new_data = sGlobalAlloc->AllocLarge(inSize, false);
      if (inSize>inFromSize)
         ZERO_MEM((char *)new_data + inFromSize,inSize-inFromSize);
   }
   else
   {
      LocalAllocator *tla = GetLocalAlloc();

      #if defined(HXCPP_GC_MOVING) && defined(HXCPP_M64)
      if (inSize<8)
          new_data =  tla->CallAlloc(8,0);
      else
      #endif
      {
         inSize = (inSize+3) & ~3;
         if (inExpand)
            tla->ExpandAlloc(inSize);

         new_data = tla->CallAlloc(inSize,0);
      }
   }


#ifdef HXCPP_TELEMETRY
   //printf(" -- reallocating %018x to %018x, size from %d to %d\n", inData, new_data, s, inSize);
   __hxt_gc_realloc(inData, new_data, inSize);
#endif

   int min_size = inFromSize < inSize ? inFromSize : inSize;

   if (min_size)
      memcpy(new_data, inData, min_size );

   InternalReleaseMem(inData);

   return new_data;
}

#ifdef HXCPP_GC_GENERATIONAL
void NewMarkedObject(hx::Object *inPtr)
{
   HX_OBJ_WB_PESSIMISTIC_GET(inPtr);
}
#endif

void RegisterCurrentThread(void *inTopOfStack)
{
   // Create a local-alloc
   LocalAllocator *local = sGlobalAlloc->GetPooledAllocator();
   if (!local)
   {
      local = new LocalAllocator((int *)inTopOfStack);
   }
   else
   {
      local->AttachThread((int *)inTopOfStack);
   }

   tlsStackContext = local;
   #ifdef HXCPP_SCRIPTABLE
   local->byteMarkId = hx::gByteMarkID;
   #endif
}

void UnregisterCurrentThread()
{
   LocalAllocator *local = (LocalAllocator *)(hx::ImmixAllocator *)tlsStackContext;
   local->Release();
}

void RegisterVTableOffset(int inOffset)
{
   if (inOffset>sgCheckInternalOffset)
   {
      sgCheckInternalOffset = inOffset;
      sgCheckInternalOffsetRows = 1 + (inOffset>>IMMIX_LINE_BITS);
   }
}

void PushTopOfStack(void *inTop)
{
   bool threadAttached = false;
   if (!sgAllocInit)
      InitAlloc();
   else
   {
      if (tlsStackContext==0)
      {
         GCPrepareMultiThreaded();
         RegisterCurrentThread(inTop);
         threadAttached = true;
      }
   }
 
   LocalAllocator *tla = GetLocalAlloc();
   tla->PushTopOfStack(inTop);
   if (threadAttached)
      tla->onThreadAttach();
}

void PopTopOfStack()
{
   LocalAllocator *tla = GetLocalAlloc();
   tla->PopTopOfStack();
}

int GcGetThreadAttachedCount()
{
   LocalAllocator *tla = GetLocalAlloc(true);
   if (!tla)
      return 0;
   return tla->mStackLocks + (tla->mGlobalStackLock ? 1 : 0);
}


#ifdef HXCPP_VISIT_ALLOCS
class GcFreezer : public hx::VisitContext
{
public:
   void visitObject(hx::Object **ioPtr) HXCPP_OVERRIDE
   {
      hx::Object *obj = *ioPtr;
      if (!obj || IsConstAlloc(obj))
         return;

      unsigned int s = ObjectSize(obj);
      void *result = InternalCreateConstBuffer(obj,s,false);
      //printf(" Freeze %d\n", s);
      *ioPtr = (hx::Object *)result;
      (*ioPtr)->__Visit(this);
   }

   void visitAlloc(void **ioPtr) HXCPP_OVERRIDE
   {
      void *data = *ioPtr;
      if (!data || IsConstAlloc(data))
         return;
      unsigned int s = ObjectSize(data);
      //printf(" Freeze %d\n", s);
      void *result = InternalCreateConstBuffer(data,s,false);
      *ioPtr = result;
   }
};
#endif


} // end namespace hx


Dynamic _hx_gc_freeze(Dynamic inObject)
{
#ifdef HXCPP_VISIT_ALLOCS
   hx::GcFreezer freezer;
   hx::Object *base = inObject.mPtr;
   freezer.visitObject(&base);
   return base;
#else
   return inObject;
#endif
}



void __hxcpp_spam_collects(int inEveryNCalls)
{
   #ifdef HXCPP_DEBUG
   sgSpamCollects = inEveryNCalls;
   #else
   GCLOG("Spam collects only available on debug versions\n");
   #endif
}

int __hxcpp_gc_trace(hx::Class inClass,bool inPrint)
{
    #if  !defined(HXCPP_DEBUG)
       #ifdef ANDROID
       __android_log_print(ANDROID_LOG_ERROR, "hxcpp", "GC trace not enabled in release build.");
       #elif defined(HX_WINRT)
       WINRT_LOG("GC trace not enabled in release build.");
       #else
       printf("WARNING : GC trace not enabled in release build.\n");
       #endif
       return 0;
    #else
       gCollectTrace = inClass.GetPtr();
       gCollectTraceCount = 0;
       gCollectTraceDoPrint = inPrint;
       hx::InternalCollect(false,false);
       gCollectTrace = 0;
       return gCollectTraceCount;
    #endif
}

int   __hxcpp_gc_large_bytes()
{
   return sGlobalAlloc->MemLarge();
}

int   __hxcpp_gc_reserved_bytes()
{
   return sGlobalAlloc->MemReserved();
}

double __hxcpp_gc_mem_info(int inWhich)
{
   switch(inWhich)
   {
      case MEM_INFO_USAGE:
         return (double)sGlobalAlloc->MemUsage();
      case MEM_INFO_RESERVED:
         return (double)sGlobalAlloc->MemReserved();
      case MEM_INFO_CURRENT:
         return (double)sGlobalAlloc->MemCurrent();
      case MEM_INFO_LARGE:
         return (double)sGlobalAlloc->MemLarge();
   }
   return 0;
}

int   __hxcpp_gc_used_bytes()
{
   return sGlobalAlloc->MemUsage();
}

void  __hxcpp_gc_do_not_kill(Dynamic inObj)
{
   hx::GCDoNotKill(inObj.GetPtr());
}

hx::Object *__hxcpp_get_next_zombie()
{
   return hx::GCGetNextZombie();
}


void _hx_set_finalizer(Dynamic inObj, void (*inFunc)(Dynamic) )
{
   GCSetHaxeFinalizer( inObj.mPtr, inFunc );
}

void __hxcpp_set_finalizer(Dynamic inObj, void *inFunc)
{
   GCSetHaxeFinalizer( inObj.mPtr, (hx::HaxeFinalizer) inFunc );
}

void __hxcpp_add_member_finalizer(hx::Object *inObject, _hx_member_finalizer f, bool inPin)
{
   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   hx::sFinalizableList.push( hx::Finalizable(inObject, f, inPin) );
}

void __hxcpp_add_alloc_finalizer(void *inAlloc, _hx_alloc_finalizer f, bool inPin)
{
   std::lock_guard<std::mutex> lock(*gSpecialObjectLock);
   hx::sFinalizableList.push( hx::Finalizable(inAlloc, f, inPin) );
}



extern "C"
{
void hxcpp_set_top_of_stack()
{
   int i = 0;
   hx::SetTopOfStack(&i,false);
}
}

void __hxcpp_enter_gc_free_zone()
{
   hx::EnterGCFreeZone();
}


bool __hxcpp_try_gc_free_zone()
{
   return hx::TryGCFreeZone();
}



void __hxcpp_exit_gc_free_zone()
{
   hx::ExitGCFreeZone();
}


void __hxcpp_gc_safe_point()
{
    if (hx::gPauseForCollect)
      hx::PauseForCollect();
}

//#define HXCPP_FORCE_OBJ_MAP

#if defined(HXCPP_M64) || defined(HXCPP_GC_MOVING) || defined(HXCPP_FORCE_OBJ_MAP)
#define HXCPP_USE_OBJECT_MAP
#endif

int __hxcpp_obj_id(Dynamic inObj)
{
   hx::Object *obj = inObj.mPtr;
   if (!obj) return -1;
   #ifdef HXCPP_USE_OBJECT_MAP
   return sGlobalAlloc->GetObjectID(obj);
   #else
   return (int)(obj);
   #endif
}

hx::Object *__hxcpp_id_obj(int inId)
{
   #ifdef HXCPP_USE_OBJECT_MAP
   return (hx::Object *)sGlobalAlloc->GetIDObject(inId);
   #else
   return (hx::Object *)(inId);
   #endif
}

#ifdef HXCPP_USE_OBJECT_MAP
unsigned int __hxcpp_obj_hash(Dynamic inObj)
{
   return __hxcpp_obj_id(inObj);
}
#else
unsigned int __hxcpp_obj_hash(Dynamic inObj)
{
   if (!inObj.mPtr) return 0;
   hx::Object *obj = inObj.mPtr;
   #if defined(HXCPP_M64)
   size_t h64 = (size_t)obj;
   return (unsigned int)(h64>>2) ^ (unsigned int)(h64>>32);
   #else
   return ((unsigned int)inObj.mPtr) >> 4;
   #endif
}
#endif




void DummyFunction(void *inPtr) { }


#ifndef HX_MULTI_THREAD_MARKING
// Dedicated incremental-marking worker for builds without the marking thread
// pool; pool builds hand tpjMark to StartThreadJobs instead.
static void IncrMarkThreadProc()
{
   while(true)
   {
      {
         std::unique_lock<std::mutex> l(sgIncrThreadLock);
         sgIncrThreadCv.wait(l, [](){ return sgIncrThreadRequest || sgIncrThreadQuit; });
         if (sgIncrThreadQuit)
            return;
         sgIncrThreadRequest = false;
         sgIncrThreadBusy = true;
         sgIncrThreadDone = false;
      }

      sGlobalAlloc->DrainMarkStackInBackground();

      {
         std::lock_guard<std::mutex> l(sgIncrThreadLock);
         sgIncrThreadBusy = false;
         sgIncrThreadDone = true;
      }
      sgIncrThreadCv.notify_all();
   }
}
#endif


// --- Frame-driven collection scheduling ------------------------------------
//
// The haxe side calls this once per frame, from the main thread.  The throttle
// follows the two mechanisms MMTk uses for concurrent Immix: the trigger point
// is relative to the heap size (ConcurrentImmix starts marking once half of
// the heap has been allocated), and the heap target comes from MemBalancer
// (see FinishIncrementalSweepList).  Nothing here is tied to a particular
// frame rate or content size.

bool __hxcpp_gc_frame_tick(int inBudgetMicros, bool inAllowFull, double inFrameMs)
{
   (void)inAllowFull;

   sGcFrameCount++;

   // Track the frame time.  The budget follows the fastest recent frame:
   // scaling it with the current frame would make an already slow frame pay
   // even more GC work, which is a positive feedback loop.
   if (inFrameMs > 0)
   {
      if (sFrameTimeEmaMs <= 0)
      {
         sFrameTimeEmaMs = inFrameMs;
         sBestFrameMs = inFrameMs;
      }
      else
      {
         sFrameTimeEmaMs += (inFrameMs - sFrameTimeEmaMs) * 0.1;
         // Relax the best frame by 1% per second, not per frame: at high
         // refresh rates a per-frame factor grows much faster than the
         // frame time does.
         sBestFrameMs *= 1.0 + 0.01 * (inFrameMs * 0.001);
         if (inFrameMs < sBestFrameMs)
            sBestFrameMs = inFrameMs;
      }
   }

   int budget = inBudgetMicros > 0 ? inBudgetMicros : GcPacerBudget();

   // No allocation system yet, or the collector was explicitly disabled.
   if (!sGlobalAlloc || !sgInternalEnable)
      return false;

   if (sgIncrementalActive)
   {
      if (sGlobalAlloc->SweepActive())
      {
         // Drive the lazy sweep from the frame tick with a small budget.
         // The allocation path only advances the sweep on free-list misses,
         // so a healthy free list leaves the sweep crawling for a whole
         // scene: sgIncrementalActive stays set, the pacer is blocked, and
         // every frag-finish re-runs the finish (the full-fps crash).
         double sweepDeadline = __hxcpp_time_stamp() + (budget > 0 ? budget : 200) * 1.0e-6;
         while (sGlobalAlloc->SweepActive())
         {
            if (!sGlobalAlloc->SweepOneBlock())
               break;
            if (__hxcpp_time_stamp() >= sweepDeadline)
               break;
         }
         if (sGlobalAlloc->SweepDone())
            sGlobalAlloc->FinishIncrementalSweepList();
         return true;
      }

      // The worker drains the mark stack; the main thread only checks whether
      // it is finished and then pays the short finishing pause.
      if (sGlobalAlloc->BackgroundMarkFinished())
         sGlobalAlloc->FinishIncremental();
      return true;
   }

   // Never re-enter while another thread is collecting.
   if (sgIsCollecting || hx::gPauseForCollect)
      return false;

   // Idle: cycle starts are decided by the allocation path (CallAlloc), the
   // same place MMTk polls.  The frame timer only reports a status line now
   // and then; starting cycles from here made the tick retry every frame
   // whenever the allocator was out of capacity and produced log storms.
   static double sLastPacerLog = 0;
   double now = __hxcpp_time_stamp();
   if (now - sLastPacerLog >= 30.0)
   {
      sLastPacerLog = now;
      GCPerfLog("pacer-idle frame=%d frameMs=%.2f rowsSince=%d live=%d cap=%d target=%d budget=%d cycles=%d pauseTotal=%.1fms",
         sGcFrameCount, sFrameTimeEmaMs, (int)sRowsSinceCycle,
         (int)sGlobalAlloc->LiveBytes(), (int)sGlobalAlloc->GetWorkingMemory(),
         (int)sWorkingMemorySize, budget, sCycleCount, sCyclePauseTotal*1000.0);
      GCPerfLog("gc-phases n=%d cycle max=%.3fms avg=%.3fms | begin wait=%.3f setup=%.3f roots=%.3f alloc=%.3f total=%.3f | finish wait=%.3f drain=%.3f roots=%.3f mark=%.3f zomb=%.3f weak=%.3f final=%.3f sweep=%.3f total=%.3f",
         sGcPhases.cycles,
         sGcPhases.cycleMax*1000.0,
         sGcPhases.cycles ? sGcPhases.cycleSum*1000.0/sGcPhases.cycles : 0.0,
         sGcPhases.beginWait*1000.0, sGcPhases.beginSetup*1000.0,
         sGcPhases.beginRoots*1000.0, sGcPhases.beginAlloc*1000.0,
         sGcPhases.beginTotal*1000.0,
         sGcPhases.finishWait*1000.0, sGcPhases.finishDrain*1000.0,
         sGcPhases.finishRoots*1000.0, sGcPhases.finishMark*1000.0,
         sGcPhases.finishZombies*1000.0, sGcPhases.finishWeak*1000.0,
         sGcPhases.finishFinal*1000.0, sGcPhases.finishSweep*1000.0,
         sGcPhases.finishTotal*1000.0);
      sGcPhases.reset();
   }
   return false;
}


double __hxcpp_gc_frame_pressure()
{
   if (!sGlobalAlloc)
      return 0.0;

   size_t target = sWorkingMemorySize;
   if (target < 1)
      return 0.0;

   return (double)sGlobalAlloc->MemUsage() / (double)target;
}


void __hxcpp_gc_set_frame_interval(int inMinFrames)
{
   if (inMinFrames < 1)
      inMinFrames = 1;
   if (inMinFrames > 600)
      inMinFrames = 600;

   sGcMinCollectFrames = inMinFrames;
}

