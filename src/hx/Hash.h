#include <stdio.h>
#include <stdlib.h>

#ifdef HXCPP_TELEMETRY
extern void __hxt_new_hash(void* obj, int size);
#endif

namespace hx
{


inline unsigned int HashCalcHash(int inKey) { return inKey; }
inline unsigned int HashCalcHash(cpp::Int64 inKey) { return (unsigned int)((inKey >> 32) ^ inKey); }
inline unsigned int HashCalcHash(const String &inKey) { return inKey.hash(); }
inline unsigned int HashCalcHash(const Dynamic &inKey)
{
   return __hxcpp_obj_hash(inKey);
}

inline void HashClear(int &ioValue) { }
inline void HashClear(Dynamic &ioValue) { ioValue=null(); }
inline void HashClear(String &ioValue) { ioValue=String(); }
inline void HashClear(Float &ioValue) {  }
inline void HashClear(cpp::Int64 &ioValue) { }

template<typename T>
struct NeedsMarking { enum { Yes = 0 }; };
template<> struct NeedsMarking<Dynamic> { enum { Yes = 1 }; };
template<> struct NeedsMarking<String> { enum { Yes = 1 }; };

// An int element has key = hash
template<typename VALUE>
struct TIntElement
{
   typedef int   Key;
   typedef VALUE Value;

   enum { IgnoreHash = 1 };
   enum { WeakKeys = 0 };
   enum { ManageKeys = 0 };

   typedef TIntElement<int>        IntValue;
   typedef TIntElement<Float>      FloatValue;
   typedef TIntElement<Dynamic>    DynamicValue;
   typedef TIntElement<String>     StringValue;
   typedef TIntElement<cpp::Int64> Int64Value;

public:
   inline void  setKey(int inKey, unsigned int )
   {
      key = inKey;
   }
   inline unsigned int getHash()   { return key; }

   Value               value;
   Key                 key;
   TIntElement<VALUE>  *next;
};

//
template<typename VALUE>
struct TInt64Element
{
   typedef cpp::Int64 Key;
   typedef VALUE Value;

   enum { IgnoreHash = 0 };
   enum { WeakKeys = 0 };
   enum { ManageKeys = 1 };

   typedef TInt64Element<int>        IntValue;
   typedef TInt64Element<Float>      FloatValue;
   typedef TInt64Element<Dynamic>    DynamicValue;
   typedef TInt64Element<String>     StringValue;
   typedef TInt64Element<cpp::Int64> Int64Value;

public:
   inline void setKey(cpp::Int64 inKey, unsigned int inHash)
   {
      key = inKey;
      hash = inHash;
   }
   inline unsigned int getHash() { return hash; }

   Value                value;
   Key                  key;
   unsigned int         hash;
   TInt64Element<VALUE> *next;
};

// An string element gets hash from string or calculates it
template<typename VALUE>
struct TStringElement
{
   typedef String Key;
   typedef VALUE  Value;

   enum { IgnoreHash = 0 };
   enum { WeakKeys = 0 };
   enum { ManageKeys = 1 };

   typedef TStringElement<int>        IntValue;
   typedef TStringElement<Float>      FloatValue;
   typedef TStringElement<Dynamic>    DynamicValue;
   typedef TStringElement<String>     StringValue;
   typedef TStringElement<cpp::Int64> Int64Value;


public:
   inline void  setKey(String inKey, unsigned int inHash)
   {
      key = inKey;
      hash = inHash;
   }
   inline unsigned int getHash() { return hash; }

   Value                  value;
   Key                    key;
   unsigned int           hash;
   TStringElement<VALUE>  *next;
};


struct TWeakStringSet
{
   typedef null Value;
   typedef String Key;

   enum { IgnoreHash = 0 };
   enum { WeakKeys = 1 };
   enum { ManageKeys = 1 };

   typedef TWeakStringSet  IntValue;
   typedef TWeakStringSet  FloatValue;
   typedef TWeakStringSet  DynamicValue;
   typedef TWeakStringSet  StringValue;
   typedef TWeakStringSet  Int64Value;


public:
   inline void  setKey(String inKey, unsigned int inHash)
   {
      key = inKey;
      hash = inHash;
   }
   inline unsigned int getHash() { return hash; }

   Key                key;
   unsigned int       hash;
   Value              value;
   TWeakStringSet     *next;
};


struct TNonGcStringSet
{
   typedef null Value;
   typedef String Key;

   enum { IgnoreHash = 0 };
   enum { WeakKeys = 1 };
   enum { ManageKeys = 0 };

   typedef TNonGcStringSet  IntValue;
   typedef TNonGcStringSet  FloatValue;
   typedef TNonGcStringSet  DynamicValue;
   typedef TNonGcStringSet  StringValue;
   typedef TNonGcStringSet  Int64Value;


public:
   inline void  setKey(String inKey, unsigned int inHash)
   {
      key = inKey;
      hash = inHash;
   }
   inline unsigned int getHash() { return hash; }

   Key                key;
   unsigned int       hash;
   Value              value;
   TNonGcStringSet    *next;
};




// An Dyanamic element must use the GC code to get a hash
template<typename VALUE,bool WEAK>
struct TDynamicElement
{
   typedef Dynamic Key;
   typedef VALUE   Value;

   enum { IgnoreHash = 0 };
   enum { WeakKeys = WEAK };
   enum { ManageKeys = 1 };

   typedef TDynamicElement<int,WEAK>        IntValue;
   typedef TDynamicElement<Float,WEAK>      FloatValue;
   typedef TDynamicElement<Dynamic,WEAK>    DynamicValue;
   typedef TDynamicElement<String,WEAK>     StringValue;
   typedef TDynamicElement<cpp::Int64,WEAK> Int64Value;

public:
   inline void  setKey(Dynamic inKey, unsigned int inHash)
   {
      key = inKey;
      hash = inHash;
   }
   inline unsigned int getHash() { return hash; }

   Value                        value;
   Key                          key;
   unsigned int                 hash;
   TDynamicElement<VALUE,WEAK>  *next;
};




enum HashStore
{
   hashInt,
   hashFloat,
   hashString,
   hashObject,
   hashNull,
   hashInt64
};
template<typename T> struct StoreOf{ enum {store=hashObject}; };
template<> struct StoreOf<int> { enum {store=hashInt}; };
template<> struct StoreOf< ::String> { enum {store=hashString}; };
template<> struct StoreOf<Float> { enum {store=hashFloat}; };
template<> struct StoreOf<null> { enum {store=hashNull}; };
template<> struct StoreOf<cpp::Int64> { enum {store=hashInt64}; };

namespace
{
inline void CopyValue(Dynamic &outValue, const Dynamic &inValue) { outValue = inValue; }
inline void CopyValue(String &outValue, const String &inValue) { outValue = inValue; }
inline void CopyValue(String &outValue, Float inValue) {  }
inline void CopyValue(String &outValue, const Dynamic &inValue) { outValue = inValue; }
inline void CopyValue(int &outValue, int inValue) { outValue = inValue; }
inline void CopyValue(int &outValue, cpp::Int64 inValue) { }
inline void CopyValue(int &outValue, Float inValue) { outValue = (int)inValue; }
inline void CopyValue(int &outValue, const Dynamic &inValue) { outValue = inValue; }
inline void CopyValue(int &outValue, const String &inValue) {  }
inline void CopyValue(Float &outValue, Float inValue) { outValue = inValue; }
inline void CopyValue(Float &outValue, const Dynamic &inValue) { outValue = inValue; }
inline void CopyValue(Float &outValue, const String &inValue) {  }
inline void CopyValue(cpp::Int64 &outValue, cpp::Int64 inValue) { outValue = inValue; }
inline void CopyValue(cpp::Int64 &outValue, int inValue) { outValue = inValue; }
inline void CopyValue(cpp::Int64 &outValue, Float inValue) { }
inline void CopyValue(cpp::Int64 &outValue, const Dynamic &inValue) { outValue = inValue; }
inline void CopyValue(cpp::Int64 &outValue, const String &inValue) {  }
inline void CopyValue(null &, const null &) {  }
template<typename T> inline void CopyValue(T &outValue, const null &) {  }
template<typename T> inline void CopyValue(null &, const T &) {  }
}


struct HashRoot : public Object
{
   HashStore store;
   int       size;
   int       mask;
   int       bucketCount;

    HX_IS_INSTANCE_OF enum { _hx_ClassId = hx::clsIdHash };

   virtual void updateAfterGc() = 0;
   virtual bool markWeakValues(MarkContext *__inCtx) = 0;

   inline int getSize() { return size; }
};

template<typename KEY>
struct HashBase : public HashRoot
{
   HashBase(int inStore)
   {
      store = (HashStore)inStore;
      size = 0;
      mask = 0;
      bucketCount = 0;
   }


   virtual bool query(KEY inKey,int &outValue) = 0;
   virtual bool query(KEY inKey,::String &outValue) = 0;
   virtual bool query(KEY inKey,Float &outValue) = 0;
   virtual bool query(KEY inKey,Dynamic &outValue) = 0;
   virtual bool query(KEY inKey,cpp::Int64 &outValue) = 0;

   virtual void set(KEY inKey, const int &inValue) = 0;
   virtual void set(KEY inKey, const ::String &inValue) = 0;
   virtual void set(KEY inKey, const Float &inValue) = 0;
   virtual void set(KEY inKey, const Dynamic &inValue) = 0;
   virtual void set(KEY inKey, const cpp::Int64 &inValue) = 0;

   virtual void clear() = 0;

   virtual HashBase<KEY> *convertStore(HashStore inStore) = 0;

   virtual bool remove(KEY inKey) = 0;
   virtual bool exists(KEY inKey) = 0;
   virtual Array<KEY> keys() = 0;
   virtual Dynamic values() = 0;

   virtual ::String toStringRaw() { return toString(); }
};

extern void RegisterWeakHash(HashBase<Dynamic> *);
extern void RegisterWeakHash(HashBase< ::String> *);

inline void RegisterWeakHash(HashBase<int> *) { };
inline void RegisterWeakHash(HashBase<cpp::Int64> *) { };


template<typename T>
struct ArrayValueOf{ typedef T Value; };
template<> struct ArrayValueOf<null> { typedef Dynamic Value; };

template<typename ELEMENT>
struct Hash : public HashBase< typename ELEMENT::Key >
{
   using HashRoot::size;
   using HashRoot::mask;
   using HashRoot::bucketCount;
   using HashRoot::getSize;

   typedef typename ELEMENT::Key   Key;
   typedef typename ELEMENT::Value Value;
   typedef typename ArrayValueOf<Value>::Value ArrayValue;

   typedef ELEMENT Element;
   enum { IgnoreHash = Element::IgnoreHash };


   ELEMENT **bucket;

   // Rehash-in-progress flag.  A marker walking the buckets while the
   // mutator is mid-rebucket/compact can hit an element in neither chain
   // (the unlink/relink pair is not atomic) and miss it, after which the
   // sweep frees live data (the Hash::find SEGV under concurrent mutators).
   // The re-link loop holds no safepoints and completes in microseconds, so
   // a concurrent marker simply spins until it is done; the STW pause can
   // only park this thread outside the region, where the table is whole.
    volatile int rehashing;


    Hash() : HashBase<Key>( StoreOf<Value>::store )
    {
       bucket = 0;
       rehashing = 0;
       if (ELEMENT::WeakKeys && Element::ManageKeys)
          RegisterWeakHash(this);
    }

   template<typename T>
   bool TIsWeakRefValid(T &) { return true; }
   bool TIsWeakRefValid(Dynamic &key) { return IsWeakRefValid(key.mPtr); }
   bool TIsWeakRefValid(String &key) { return IsWeakRefValid(key.raw_ptr()); }

   template<typename T>
   bool TMarkWeakValue(T &, MarkContext *) { return false; }
   bool TMarkWeakValue(Dynamic &inValue, MarkContext *__inCtx)
   {
      hx::Object *value = inValue.mPtr;
      if (!value || (((unsigned int *)value)[-1] & hx::gPrevMarkIdMask))
         return false;

      HX_MARK_MEMBER(inValue);
      return true;
   }
   bool TMarkWeakValue(String &inValue, MarkContext *__inCtx)
   {
      const HX_CHAR *value = inValue.raw_ptr();
      if (!value || (((unsigned int *)value)[-1] & hx::gPrevMarkIdMask))
         return false;

      HX_MARK_MEMBER(inValue);
      return true;
   }

   bool markWeakValues(MarkContext *__inCtx) HXCPP_OVERRIDE
   {
      if (!Element::WeakKeys || !Element::ManageKeys)
         return false;

      while (rehashing) { }

      bool marked = false;
      for(int b=0;b<bucketCount;b++)
      {
         Element *element = bucket[b];
         while(element)
         {
            if (TIsWeakRefValid(element->key))
               marked = TMarkWeakValue(element->value, __inCtx) || marked;
            element = element->next;
         }
      }
      return marked;
   }


   void updateAfterGc() HXCPP_OVERRIDE
   {
      if (Element::WeakKeys && Element::ManageKeys)
      {
         for(int b=0;b<bucketCount;b++)
         {
            Element **headPtr = &bucket[b];
            while(*headPtr)
            {
               Element &el = **headPtr;
               if (!TIsWeakRefValid(el.key))
               {
                  *headPtr = el.next;
                  size--;
               }
               else
                  headPtr = &el.next;
            }
         }
      }
   }

   void rebucket(int inNewCount)
   {
#ifdef HXCPP_TELEMETRY
      bool is_new = bucket==0;
#endif
      mask = inNewCount-1;
      //printf("expand %d -> %d\n",bucketCount, inNewCount);
      // The realloc allocates (a safepoint!), so it runs BEFORE the rehashing
      // flag goes up: a thread must never park inside the re-link loop, or a
      // marker walking the buckets would see the half-rehashed chains, miss
      // an element that is in neither chain, and the sweep would free live
      // data (the Hash::find SEGV under concurrent mutators).
      bucket = (Element **)InternalRealloc(bucketCount*sizeof(ELEMENT *), bucket,inNewCount*sizeof(ELEMENT *));
      HX_OBJ_WB_GET(this, bucket);
      //for(int b=bucketCount;b<inNewCount;b++)
      //   bucket[b] = 0;

#ifdef HXCPP_TELEMETRY
      if (is_new) __hxt_new_hash(bucket, inNewCount*sizeof(ELEMENT *));
#endif


      // The re-link loop has no safepoints: a concurrent marker spinning on
      // the flag below is guaranteed the loop completes and the chains are
      // whole again, and the STW pause can only park this thread outside the
      // region, where the table is consistent.
      rehashing = 1;
      for(int b=0;b<bucketCount;b++)
      {
         Element **head = &bucket[b];
         while(*head)
         {
            Element &e = **head;
            int newBucket = e.getHash()&mask;
            if ( newBucket != b )
            {
               *head = e.next;
               e.next = bucket[newBucket];
               bucket[newBucket] = &e;
            }
            else
               head = &e.next;
         }
      }

      bucketCount = inNewCount;
      rehashing = 0;
   }

   void reserve(int inSize)
   {
      if (inSize<8)
          inSize = 8;

      expandBuckets(inSize);
   }

   void compact()
   {
      int origSize = bucketCount;
      int newSize = bucketCount>>1;
      // printf("compact -> %d\n", newSize);
      mask = newSize-1;
      // Same concurrent-marker protection as rebucket: the splice
      // transiently orphans the appended chain, and the loop must not be
      // interruptible by a safepoint.  The realloc (which allocates) stays
      // outside the flag.
      rehashing = 1;
      for(int b=newSize; b<bucketCount; b++)
      {
         Element *head = bucket[b];
         if (head)
         {
            Element *oldHead = bucket[b-newSize];
            bucket[b-newSize] = head;

            if (oldHead)
            {
               // Append to last element
               Element **lastPtr = &(head->next);
               while(*lastPtr)
                  lastPtr = & (*lastPtr)->next;
               *lastPtr = oldHead;
            }
            bucket[b] = 0;
         }
      }
      bucketCount = newSize;
      rehashing = 0;
      bucket = (Element **)InternalRealloc(origSize*sizeof(ELEMENT *),bucket, sizeof(ELEMENT *)*bucketCount );
      HX_OBJ_WB_GET(this, bucket);
   }

   bool remove(Key inKey) HXCPP_OVERRIDE
   {
      if (!bucket)
         return false;
      unsigned int hash = HashCalcHash(inKey);
      Element **head = bucket + (hash&mask);
      while(*head)
      {
         Element &el = **head;
         if ( (IgnoreHash || el.getHash()==hash) && el.key==inKey)
         {
            *head = el.next;
            size--;
            if (bucketCount>8 && size < (bucketCount>>1) )
               compact();
            return true;
         }
         head = &el.next;
      }
      return false;
   }

   ELEMENT *allocElement()
   {
      ELEMENT *result = (ELEMENT *)InternalNew( sizeof(ELEMENT), false );
      size++;
      expandBuckets(size);
      return result;
   }

   inline void expandBuckets(int inSize)
   {
      // Trades memory vs bucket occupancy - more memory is used for elements anyhow, so not too critical
      enum { LOG_ELEMS_PER_BUCKET = 1 };
      if ( inSize > (bucketCount<<LOG_ELEMS_PER_BUCKET) )
      {
         int newCount = bucketCount;
         if (newCount==0)
            newCount = 2;
         else
            while( inSize > (newCount<<LOG_ELEMS_PER_BUCKET) )
               newCount<<=1;
         if (newCount!=bucketCount)
            rebucket(newCount);
      }
   }

   Element *find(int inHash, Key inKey)
   {
      if (!bucket) return 0;
      Element *head = bucket[inHash & mask];
      while(head)
      {
         if (::hx::GcWalkValidationEnabled() && !::hx::GcHeapRangeCheck((void *)head))
         {
            ::hx::GcBadLinkLog((void *)head, (void *)this);
            return 0;
         }
         if ( (IgnoreHash || head->getHash()==inHash) && head->key==inKey)
            return head;
         head = head->next;
      }
      return 0;
   }

   bool exists(Key inKey) HXCPP_OVERRIDE { return find( HashCalcHash(inKey), inKey ); }


   HashBase<Key> *convertStore(HashStore inStore) HXCPP_OVERRIDE
   {
      switch(inStore)
      {
         case hashInt:
            return TConvertStore< typename ELEMENT::IntValue >();
         case hashFloat:
            return TConvertStore< typename ELEMENT::FloatValue >();
         case hashString:
            return TConvertStore< typename ELEMENT::StringValue >();
         case hashObject:
            return TConvertStore< typename ELEMENT::DynamicValue >();
         case hashInt64:
            return TConvertStore< typename ELEMENT::Int64Value >();
         case hashNull:
             ;
      }
      return 0;
   }


   template<typename OUT_VALUE>
   bool TQuery(Key inKey,OUT_VALUE &outValue)
   {
      Element *result = find( HashCalcHash(inKey), inKey );
      if (!result)
         return false;
      CopyValue(outValue,result->value);
      return true;
   }

   bool query(Key inKey,int &outValue) HXCPP_OVERRIDE { return TQuery(inKey,outValue); }
   bool query(Key inKey,::String &outValue) HXCPP_OVERRIDE { return TQuery(inKey,outValue); }
   bool query(Key inKey,Float &outValue) HXCPP_OVERRIDE { return TQuery(inKey,outValue); }
   bool query(Key inKey,Dynamic &outValue) HXCPP_OVERRIDE { return TQuery(inKey,outValue); }
   bool query(Key inKey,cpp::Int64 &outValue) HXCPP_OVERRIDE { return TQuery(inKey, outValue); }


   Value get(Key inKey)
   {
      Element *result = find( HashCalcHash(inKey), inKey );
      if (result)
         return result->value;
      return 0;
   }


   template<typename Finder>
   bool findEquivalentKey(Key &outKey, int inHash, const Finder &inFinder)
   {
      if (!bucket) return false;
      Element *head = bucket[inHash & mask];
      while(head)
      {
         if (::hx::GcWalkValidationEnabled() && !::hx::GcHeapRangeCheck((void *)head))
         {
            ::hx::GcBadLinkLog((void *)head, (void *)this);
            return false;
         }
         if ( (IgnoreHash || head->getHash()==inHash) && inFinder==head->key)
         {
            outKey = head->key;
            return true;
         }
         head = head->next;
      }
      return false;
   }

   static inline bool IsNursery(const void *inPtr)
   {
      return inPtr && !(((unsigned char *)inPtr)[ HX_ENDIAN_MARK_ID_BYTE]);
   }

   template<typename SET>
   void TSet(Key inKey, const SET &inValue)
   {
      unsigned int hash = HashCalcHash(inKey);
      Element *el = find(hash,inKey);
      if (el)
      {
         CopyValue(el->value,inValue);
         if (hx::ContainsPointers<Value>())
            HX_OBJ_WB_GET(this,hx::PointerOf(el->value));
         return;
      }
      el = allocElement();
      el->setKey(inKey,hash);
      CopyValue(el->value,inValue);
      // The two linking stores are not atomic together: an element between
      // them is in neither chain, and a concurrent marker walking the
      // buckets would miss it (the sweep would then free it while the hash
      // still references it - the Hash::find SEGV).  Hold the rehashing
      // flag across the stores; a concurrent marker spins for two
      // instructions.  The flag also gates the re-scan itself: it happens
      // below, after the flag clears, so it always sees the linked element.
      rehashing = 1;
      el->next = bucket[hash&mask];
      bucket[hash&mask] = el;
      rehashing = 0;

      #if defined(HXCPP_GC_GENERATIONAL) || defined(HXCPP_GC_INCREMENTAL)
      unsigned char &mark =  ((unsigned char *)(this))[ HX_ENDIAN_MARK_ID_BYTE];
      #ifdef HXCPP_GC_INCREMENTAL
      // Incremental marking: any insertion can create a black->white edge
      // (a fresh String key, or an old key that has not been marked yet).
      // Record the hash; the worker that picks the chunk up re-scans it
      // promptly.  Native threads without a GC context must not touch GC
      // metadata (same rule as ObjectAssignWriteBarrier).
      if (::hx::gIncrementalMarking && mark == hx::gByteMarkID)
      {
         hx::StackContext *__wbCtx = HX_CTX_GET;
         if (__wbCtx)
         {
            mark|=HX_GC_REMEMBERED;
            __wbCtx->pushReferrer(this);
         }
      }
      #else
      if (mark == hx::gByteMarkID)
      {
         // Look for nursery objects...
         if ( IsNursery(el) || IsNursery(hx::PointerOf(el->key)) ||
             (hx::ContainsPointers<Value>() && IsNursery(hx::PointerOf(el->value)) ) )
         {
            mark|=HX_GC_REMEMBERED;
            (HX_CTX_GET)->pushReferrer(this);
         }
      }
      #endif
      #endif
   }

   void set(Key inKey, const int &inValue) HXCPP_OVERRIDE { TSet(inKey, inValue); }
   void set(Key inKey, const ::String &inValue) HXCPP_OVERRIDE { TSet(inKey, inValue); }
   void set(Key inKey, const Float &inValue) HXCPP_OVERRIDE { TSet(inKey, inValue); }
   void set(Key inKey, const Dynamic &inValue) HXCPP_OVERRIDE { TSet(inKey, inValue); }
   void set(Key inKey, const null &inValue)  { TSet(inKey, inValue);  }
   void set(Key inKey, const cpp::Int64 &inValue) HXCPP_OVERRIDE { TSet(inKey, inValue); }

   void clear() HXCPP_OVERRIDE
   {
      bucket = 0;
      size = 0;
      mask = 0;
      bucketCount = 0;
   }


   template<typename F>
   void iterate(F &inFunc)
   {
      for(int b=0;b<bucketCount;b++)
      {
         Element *el = bucket[b];
         while(el)
         {
            if (::hx::GcWalkValidationEnabled() && !::hx::GcHeapRangeCheck((void *)el))
            {
               ::hx::GcBadLinkLog((void *)el, (void *)this);
               break;
            }
            inFunc(el);
            el = el->next;
         }
      }
   }

   // Convert
   template<typename NEW>
   struct Converter
   {
      NEW *result;

      Converter(NEW *inResult) : result(inResult) { }

      void operator()(typename Hash::Element *elem)
      {
         result->set(elem->key,elem->value);
      }
   };


   template<typename NEW_ELEM>
   HashBase<Key> *TConvertStore()
   {
      Hash<NEW_ELEM> *result = new Hash<NEW_ELEM>();

      result->reserve(getSize()*3/2);

      Converter< Hash<NEW_ELEM> > converter(result);

      iterate(converter);

      return result;
   }



   // Keys ...
   struct KeyBuilder
   {
      Array<Key> array;

      KeyBuilder(int inReserve = 0)
      {
         array = Array<Key>(0,inReserve);
      }
      void operator()(typename Hash::Element *elem)
      {
         array->push(elem->key);
      }
   };
   Array<Key> keys() HXCPP_OVERRIDE
   {
      KeyBuilder builder(getSize());
      iterate(builder);
      return builder.array;;
   }


   // Values...
   struct ValueBuilder
   {
      Array<ArrayValue> array;
      ValueBuilder(int inReserve = 0)
      {
         array = Array<ArrayValue>(0,inReserve);
      }

      void operator()(typename Hash::Element *elem)
      {
         array->push(elem->value);
      }
   };
   Dynamic values() HXCPP_OVERRIDE
   {
      ValueBuilder builder(getSize());
      iterate(builder);
      return builder.array;;
   }


   // Strings ...
   struct StringBuilder
   {
      Array<String> array;
      bool raw;

      StringBuilder(int inReserve = 0,bool inRaw=false)
      {
         raw = inRaw;
         array = Array<String>(0,inReserve*4+1);
         if (!raw) {
            #if (HXCPP_API_LEVEL >= 430)
            array->push(HX_CSTRING("["));
            #else
            array->push(HX_CSTRING("{ "));
            #endif
         }
      }
      void operator()(typename Hash::Element *elem)
      {
         if (array->length>1)
            array->push(HX_CSTRING(", "));
         array->push(String(elem->key));
         array->push(HX_CSTRING(" => "));
         array->push(String(elem->value));
      }
      ::String toString()
      {
         if (!raw) {
            #if (HXCPP_API_LEVEL >= 430)
            array->push(HX_CSTRING("]"));
            #else
            array->push(HX_CSTRING(" }"));
            #endif
         }
         return array->length==0 ? String() : array->join(HX_CSTRING(""));
      }
   };

   String toString() HXCPP_OVERRIDE
   {
      StringBuilder builder(getSize());
      iterate(builder);
      return builder.toString();
   }


   String toStringRaw() HXCPP_OVERRIDE
   {
      StringBuilder builder(getSize(),true);
      iterate(builder);
      return builder.toString();
   }


   // Mark ...
   struct HashMarker
   {
      hx::MarkContext *__inCtx;
      HashMarker(hx::MarkContext *ctx) : __inCtx(ctx) { }
      void operator()(typename Hash::Element *inElem)
      {
         if (::hx::GcWalkValidationEnabled() && !::hx::GcHeapRangeCheck((void *)inElem))
         {
            ::hx::GcBadLinkLog((void *)inElem, 0);
            return;
         }
         HX_MARK_ARRAY(inElem);
         if (!Hash::Element::WeakKeys)
         {
            HX_MARK_MEMBER(inElem->key);
            HX_MARK_MEMBER(inElem->value);
         }
      }
   };

   void __Mark(hx::MarkContext *__inCtx) HXCPP_OVERRIDE
   {
      // A marker must not walk a half-rehashed table - the re-link loop has
      // no safepoints and finishes in microseconds, so spin it out.  With
      // STW budgeted mark steps the world is paused for the whole walk, so
      // the spin always passes immediately; the flag remains for the
      // mutator-side find()/TSet() paths.
      while (rehashing) { }

      HX_MARK_ARRAY(bucket);

      HashMarker marker(__inCtx);
      iterate(marker);
   }

#ifdef HXCPP_VISIT_ALLOCS

   void __Visit(hx::VisitContext *__inCtx) HXCPP_OVERRIDE
   {
      //printf(" visit hash %p\n", this);
      HX_VISIT_ARRAY(bucket);
      for(int b=0;b<bucketCount;b++)
      {
         HX_VISIT_ARRAY(bucket[b]);
         Element *el = bucket[b];
         while(el)
         {
            HX_VISIT_MEMBER(el->key);
            HX_VISIT_MEMBER(el->value);
            HX_VISIT_ARRAY(el->next);
            el = el->next;
         }
      }
   }
#endif
};


} // end namespace hx

