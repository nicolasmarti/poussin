#include<stdio.h> //printf
#include<malloc.h> //memalign
#include<string.h> //memset

#ifndef GC_INCLUDE
#define GC_INCLUDE

typedef unsigned long uint;

typedef char bool;

#define true 1
#define false 0

// gc initialization with segment of size 2**n
char gc_init(uint n);

// allocation function (the bool means that it is a root)
void* gc_alloc(uint size, bool root);

// the freeing of data (only work for root)
void gc_free(void* data);

// unset as root
void unset_root(void* data);

// set as root
void set_root(void* data);


#endif

/*

   this is a memeory allocator / garbage collector
   based on 
   An Efficient Non-Moving Garbage Collector for Functional Languages (ICFP 2011)
   
   http://www.pllab.riec.tohoku.ac.jp/papers/icfp2011UenoOhoriOtomoAuthorVersion.pdf
   http://www.pllab.riec.tohoku.ac.jp/~katsu/slide-20110920.pdf


 */

char *byte_to_binary
(
    uint x
)
{
    static char b[33];
    b[0] = '\0';

    uint z;
    for (z = 1; z > 0; z <<= 1)
    {
        strcat(b, ((x & z) == z) ? "1" : "0");
    }

    return b;
}

// the size of pointers
#define ptr_size_byte (uint)(sizeof(void*))
#define ptr_size_bit (uint)(ptr_size_byte*8) // here we assert 8 bits per byte

// compute floor(log2(x))
uint floor_log2(uint x)
{
  uint r = 0;
  while (x >>= 1) // unroll for more speed...
    {
      r++;
    }
  return (r);
}

// compute cell(log2(x))
uint cell_log2(uint x)
{
  uint y = x;
  uint r = 0;
  while (y >>= 1) // unroll for more speed...
    {
      r++;
    }

  if ((1 << r) < x)
    ++r;

  return (r);
}

uint cell_log_n2(uint x, uint y)
{
  uint r = 1;
  while (x >>= y) // unroll for more speed...
    {
      r++;
    }
  return (r);
}

// compute the floor value of the division of x by y
uint cell_div(uint x, uint y){
  
  int z = x/y;
  if (x % y == 0)
    return z;
  else 
    return z+1;

}

uint ptr_size_bit_pow2;

uint cell_div_ptr_size_bit(uint x)
{
  uint y = x >> ptr_size_bit_pow2;
  
  if (x > y << ptr_size_bit_pow2)
    ++y;

  return y;
 
}


/***********************************************************************************************/
// the segment are defined as an array of 2^n void* and align on 2^n
// this allow to optimize the computation of a segment address from a chunk address
uint segment_size_n;
typedef void** segment;
// this is the mask to apply to a bulk address to grab back the segment address
uint segment_mask;
// this is a mask to know if the value we have is a pointer to a bulk (align on a void*)
uint pointer_mask;

// in order to make sure that we are pointing to a segment, we create at initialization
// a magic number which will be place at the start of each segment
void* magic_number;

// in order to check if a pointer is in a segment that we allocated we keep the min of all segment starting address, and the max of all segment last address
void* min_segment_start = (void*)(-1);
void* max_segment_end = (void*)(0);

// we have a global list of free segment
void* free_segment_start = NULL;
void* free_segment_end = NULL;

// bit pointers
typedef uint bm_index;
typedef uint bm_mask;
typedef uint bm_level;

// a heap is a list of segment, a pointer to the current segment, the number of bulk and their size, and a bit pointer

typedef struct {
  void* segment_start;
  void* segment_end;
  void* curr_segment;
  uint nb_bulk;
  uint bulk_size;
  bm_index index;
  bm_mask mask;
} heap;

/*
  a segment contain <nb_bulk> elements of void*[<bulk_size>] is composed of

  - a magic number (size = sizeof(void*))
  
  - a pointer to the next segment (size = sizeof(void*))
  - a pointer to the previous segment (size = sizeof(void*))

  - a pointer to the heap

  - a counter of the number of allocated elements (size = sizeof(void*))

  - a bitmap composed of
    (BM[0], ..., BM[L-1]) bitmaps where
    BM[0] is an array of void* of size floor(nb_bulk / ptr_size_bit) (one bit per bulk)
    and recursively BM[i+1] is an array of void* of size floor(size(BM[i]) / ptr_size_bit) (one bit per element on BM[i]

    Thus we can compute statically the max level L as L := floor(log_{ptr_size_bit}(nb_bulk))
    BM[i](j) is the j-th bit of BM[i]
    BM[i][j] is the j-th element of BM[i]

    this bitmap is used to store the information about allocated blocks

  - a bitmap similar to the previous one, keeping the root information

  - an array of void* of size nb_bulk*bulk_size

  - a buffer use as a stack for the tracing algorithm
    (we use for now an array of void* of size nb_bulk)

    Question: given bulk_size and the size of the segment, what is the number of bulk_size that can registered ?
  
 */

// the max level for a given number of bulk
uint max_level(uint nb_bulk)
{
  return cell_log_n2(nb_bulk, ptr_size_bit_pow2);
}


// bitmap_size in pointer
uint bitmap_size_elt(uint nb_bulk)
{
  uint size = 0;
  uint curr_level = 0;
  uint curr_level_size = cell_div_ptr_size_bit(nb_bulk);

  for (; curr_level_size > 1; 
       ++curr_level, 
	 curr_level_size = cell_div_ptr_size_bit(curr_level_size)
       )
    {
      //printf("sizeof(bitmap[%lu]) := %lu (<= %lu)\n", curr_level, curr_level_size, curr_level_size * ptr_size_bit);
      size += curr_level_size;  
    }

  /*
  if (curr_level+1 != max_level(nb_bulk))
    printf("cell_log_n2(...) := %lu <> %lu\n", cell_log_n2(nb_bulk, ptr_size_bit_pow2), curr_level+1);
  */

  return ++size;
}

// size of a segment in byte
uint segment_size(uint nb_bulk, uint bulk_size)
{
  return (
	  1 + // magic
	  2 + // next/prev
	  1 + // the heap pointer
	  1 + // counter
	  bitmap_size_elt(nb_bulk) + //bitmap for allocated bits
	  bitmap_size_elt(nb_bulk) + //bitmap for root bits
	  (nb_bulk * bulk_size) + // data
	  nb_bulk // stack
	  ) * ptr_size_byte;

}

// compute the nb_bulk max for a segment of max_size byte with bulk of bulk_size
uint nb_bulk_ub(uint max_size, uint bulk_size)
{
  // a first guess
  uint res = cell_div(max_size, bulk_size*ptr_size_byte);

  //printf("init guess := %lu\n", res);
  
  // then we iterate to find the max number of bulk
  while (segment_size(res, bulk_size) > max_size)
    --res;

  return res;

}

// lookup the magic_number
void* get_magic_number (void* segment){
  return *(void**)(segment);
}

// mutate the magic_number
void set_magic_number (void* segment, void* magic){
  *(void**)(segment) = magic;
}

// lookup the previous segment pointer
void* get_segment_prev(void* segment){
  return *(void**)(segment + 1*ptr_size_byte);
}

// lookup the next segment pointer
void* get_segment_next(void* segment){
  return *(void**)(segment + 2*ptr_size_byte);
}

// mutate the previous segment pointer
void set_segment_prev(void* segment, void* prev){
  *(void**)(segment + 1*ptr_size_byte) = prev;
}

// mutate the next segment pointer
void set_segment_next(void* segment, void* next){
  *(void**)(segment + 2*ptr_size_byte) = next;
}

// get the heap pointer
heap* get_segment_heap(void* segment){
  return *(heap**)(segment + 3*ptr_size_byte);
}

// mutate the next segment pointer
void set_segment_heap(void* segment, heap* h){
  *(heap**)(segment + 3*ptr_size_byte) = h;
}

// lookup the counter
uint get_segment_counter(void* segment){
  return *(uint*)(segment + 4*ptr_size_byte);
}

//mutate the counter
void set_segment_counter(void* segment, uint counter){
  *(uint*)(segment + 4*ptr_size_byte) = counter;
}

// increment the segment counter
void inc_segment_counter(void* segment){
  uint* counter = (uint*)(segment + 4*ptr_size_byte);
  *counter = *counter + 1;
}

// decrement the segment counter
void dec_segment_counter(void* segment){
  uint* counter = (uint*)(segment + 4*ptr_size_byte);
  *counter = *counter - 1;
}

// get pointer to the alloc bitmap
void* get_alloc_bitmap_ptr(void* segment)
{
  return (segment + 5*ptr_size_byte);
}

// get pointer to the root bitmap
void* get_root_bitmap_ptr(void* segment, uint nb_bulk)
{
  return (segment + (5 + bitmap_size_elt(nb_bulk))*ptr_size_byte);
}

// get a pointer to the data
void* get_bulk_ptr(void* segment, uint nb_bulk)
{
  return (segment + (
		     5 + 
		     bitmap_size_elt(nb_bulk) * 2
		     ) * ptr_size_byte
	  );

}

// get a pointer to the twork area the data
void* get_segment_twork_ptr(void* segment, uint nb_bulk, uint bulk_size)
{

  return segment + (
	  1 + // magic
	  2 + // next/prev
	  1 + // the heap pointer
	  1 + // counter
	  bitmap_size_elt(nb_bulk) + //bitmap for allocated bits
	  bitmap_size_elt(nb_bulk) + //bitmap for root bits
	  (nb_bulk * bulk_size)
	  ) * ptr_size_byte;

}

// from the starting address of a bitmap (given a nb_bulk), return the address of the level l bitmap
void* get_level_bitmap_ptr(void* bitmap_ptr, uint nb_bulk, uint level){
  
  uint offset = 0;
  uint curr_level = 0;
  uint curr_level_size = cell_div_ptr_size_bit(nb_bulk);

  for (; curr_level < level; 
       ++curr_level, 
	 curr_level_size = cell_div_ptr_size_bit(curr_level_size))
    {
      offset += curr_level_size;  
    }
  
  //printf("sizeof(bitmap[%lu]) := 1 (<= %lu)\n", curr_level+1, ptr_size_bit);

  return bitmap_ptr + offset*ptr_size_byte; 

}


// clear counter and alloc bitmap of a segment 
void clearABMandCount(void* segment, uint nb_bulk)
{
  memset(segment + 4*ptr_size_byte, // counter is at offset 4
	 0, // we put zeros
	 (1+bitmap_size_elt(nb_bulk))*ptr_size_byte // on an array of void* of the size of the bitmap + counter
	 );
}

// clear counter and alloc&root bitmap of a segment 
void clearARBMandCount(void* segment, uint nb_bulk)
{
  memset(segment + 4*ptr_size_byte, // counter is at offset 4
	 0, // we put zeros
	 (1+2*bitmap_size_elt(nb_bulk))*ptr_size_byte // on an array of void* of the size of the bitmap + counter
	 );
}

/* chaining of segments */

// inserting a segment at the end of a list
void insert_segment_end(void** start, void** end, void* segment)
{
  // if the list is empty start == end == null
  // thus we set both to segment and set next and prev of segment to nil
  if (*start == NULL){
    *start = segment;
    *end = segment;
    set_segment_prev(segment, NULL);
    set_segment_next(segment, NULL);
    return;
  }

  // else we set the next of segment to NULL,
  // prev, to the value of end
  // the next pointer of the previous segment to segment
  // and end to the segment
  set_segment_next(segment, NULL);
  set_segment_prev(segment, *end);
  set_segment_next(*end, segment);
  *end = segment;
  return;

}

// inserting a segment at the start of a list
void insert_segment_start(void** start, void** end, void* segment)
{
  // if the list is empty start == end == null
  // thus we set both to segment and set next and prev of segment to nil
  if (*start == NULL){
    *start = segment;
    *end = segment;
    set_segment_prev(segment, NULL);
    set_segment_next(segment, NULL);
    return;
  }

  // else we set the prev of segment to NULL,
  // next, to the value of start
  // the prev pointer of the next segment to segment
  // and start to the segment
  set_segment_prev(segment, NULL);
  set_segment_next(segment, *start);
  set_segment_prev(*start, segment);
  *start = segment;
  return;

}

// taking a segment at the begining of a list
void* take_segment_start(void** start, void** end)
{
  // if the list is empty start == end == null
  // thus we return NULL
  if (*start == NULL){
    return NULL;
  }

  // else we grab the value of start as or result,
  // we set it to the next of the grabbed segment,
  // if there is a segment at the head of the list, then we set its prev to NULL
  // else we set end at NULL
  void* res = *start;
  
  *start = get_segment_next(res);
  
  if (*start != NULL)
    set_segment_prev(*start, NULL);
  else
    *end = NULL;

  return res;
}

// taking a segment in a list
void take_segment(void** start, void** end, void* segment)
{
  void* next_segment = get_segment_next(segment);
  void* prev_segment = get_segment_prev(segment);

  // we first update the next segment
  if (next_segment == NULL)
    {
      // there is no next segment, we update the end pointer
      *end = prev_segment;
    }
  else
    {
      // else we set the prev of next to prev
      set_segment_prev(next_segment, prev_segment);
    }

  // we then update the prev segment
  if (prev_segment == NULL)
    {
      // there is no prev segment, we update the start pointer
      *start = next_segment;
    }
  else
    {
      // else we set the prev of next to prev
      set_segment_next(prev_segment, next_segment);
    }
  
  return;
}

// switch to segment (the one pointed by segment, and its next one
void switch_segment_next(void** start, void** end, void* segment)
{
  void* next_segment = get_segment_next(segment);
  if (next_segment == NULL) return;

  // we switch segment in the list
  set_segment_next(segment, get_segment_next(next_segment));
  set_segment_prev(next_segment, get_segment_prev(segment));
  
  set_segment_prev(segment, next_segment);
  set_segment_next(next_segment, segment);
  
  // we possibly update the start end pointer of the heap or the previous
  if (get_segment_next(segment) == NULL)
    *end = segment;
  else
    set_segment_prev(get_segment_next(segment), segment);
  
  if (get_segment_prev(next_segment) == NULL)
    *start = next_segment;
  else
    set_segment_next(get_segment_prev(next_segment), next_segment);

  return;
}

//***************************************************************

//increment a bitpointer
void inc_bitptr(bm_index* index, bm_mask* mask)
{
  // we shift the mask
  *mask <<= 1;

  // if it becomes 0 then we increase the index and reset the mask
  if (*mask == 0)
    {
      ++(*index);
      *mask = 1;
    }

  return;
}

//convert a bit index to a bit pointer
void indexToBitPtr(bm_index i, bm_index* index, bm_mask* mask)
{
  *index = i / ptr_size_bit;
  *mask = 1 << (i % ptr_size_bit);
}

//convert a bitptr to a bit index
bm_index bitPtrToIndex(bm_index index, bm_mask mask)
{
  return index * ptr_size_bit + (floor_log2(mask));
}

// convert a bitptr to a bulk address
void* blockAddress(void* data_ptr, bm_index index, bm_mask mask, uint bulk_size){

  return data_ptr + bitPtrToIndex(index, mask)*bulk_size*ptr_size_byte;

}

// give the size of element of a given level (correspond to the max index)
bm_index get_level_max_index(uint nb_bulk, uint level){
  
  uint curr_level = 0;
  uint curr_level_size = cell_div_ptr_size_bit(nb_bulk);

  for (; curr_level < level; 
       ++curr_level 
       )
    {
      curr_level_size = cell_div_ptr_size_bit(curr_level_size);
    }
  
  //printf("sizeof(bitmap[%lu]) := 1 (<= %lu)\n", curr_level+1, ptr_size_bit);

  return --curr_level_size; 

}

// give the maximal mask for the last index of a given level
bm_mask get_level_max_mask(uint nb_bulk, uint level){
  
  uint level_max_index = get_level_max_index(nb_bulk, level);
  uint max_bulk_num = ptr_size_bit * level_max_index;
  uint i;
  for (i = 0; i < level; ++i) 
    max_bulk_num *= ptr_size_bit;

  return 1 << (ptr_size_bit - (max_bulk_num - nb_bulk));
}

// test if the bitptr for level i is set or not
uint isMarked(void* level_bitmap_ptr, bm_index index, bm_mask mask)
{
  return (mask & *(uint*)(level_bitmap_ptr + index*ptr_size_byte)) ? 1 : 0;  
}

//return the next mask such that the bit is marked | unmarkd
bm_mask nextMask(void* bitmap_ptr, bm_index index, bm_mask mask, uint level, uint nb_bulk, uint lookingfor)
{
  if (mask == 0) return 0;
  // overflow of index
  uint level_max_index = get_level_max_index(nb_bulk, level);
  if (index > level_max_index) return 0;
  uint max_index_max_mask = get_level_max_mask(nb_bulk, level);

  void* level_bitmap_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);

  //printf("nextMask (%lu, %s) := ", index, byte_to_binary(mask));

  // here we split the cases on the fact or not that we are on the max
  if (index == level_max_index){

    uint is_marked;
    // loop while
    while (mask && // the mask is not 0 and
	   mask < max_index_max_mask && // we are lower or equal to the max mask and
	   lookingfor != (is_marked = isMarked(level_bitmap_ptr, index, mask)) // the current bit is what we are looking for
	   )
      // we increment the mask
      mask <<= 1;
    
    // if it is not what we are looking for then we set the mask to 0
    if (is_marked != lookingfor) mask = 0;
    
  } else {

    // same as before, except that we do not test for the max mask
    uint is_marked;
    // loop while
    while (mask && // the mask is not 0 and
	   lookingfor !=  (is_marked = isMarked(level_bitmap_ptr, index, mask)) // the current bit is not what we are looking for
	   )
      // we increment the mask
      mask <<= 1;
    
    // if it is not what we are looking for, we set the mask to 0
    if (is_marked != lookingfor) mask = 0;

  }
   
  //printf("%s\n", byte_to_binary(mask));

  // we return the mask
  return mask;
}

// setBitAnd: set a bit, and update the upper level w.r.t. a bitwise andif all bits are to one
void setBitAnd(void* bitmap_ptr, bm_index index, bm_mask mask, uint nb_bulk, uint level)
{
  // grab the bitmap pointer of the level
  void* bitmap_level_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);
  
  // grab the corresponding bitmap of the index
  uint bm = *(uint*)(bitmap_level_ptr + index*ptr_size_byte);

  // compute and and with the mask and store
  bm |= mask;

  *(uint*)(bitmap_level_ptr + index*ptr_size_byte) = bm;

  // update upper map if necessary
  if (level + 1 < max_level(nb_bulk) && bm == ~0)
    {
      bm_index i = index;
      indexToBitPtr(i, &index, &mask);
      setBitAnd(bitmap_ptr, index, mask, nb_bulk, level+1);
    }

  return;
}

// setBitAnd: set a bit, and update the upper level w.r.t. a bitwise andif all bits are to one
void unsetBitAnd(void* bitmap_ptr, bm_index index, bm_mask mask, uint nb_bulk, uint level)
{
  // grab the bitmap pointer of the level
  void* bitmap_level_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);
  
  // grab the corresponding bitmap of the index
  uint bm = *(uint*)(bitmap_level_ptr + index*ptr_size_byte);

  // set and with mask negation
  *(uint*)(bitmap_level_ptr + index*ptr_size_byte) = bm & ~ mask;

  // update upper map if necessary
  if (level + 1 < max_level(nb_bulk))
    {
      bm_index i = index;
      indexToBitPtr(i, &index, &mask);
      unsetBitAnd(bitmap_ptr, index, mask, nb_bulk, level+1);
    }
  return;
}

// setBitOr: set a bit, and update the upper level w.r.t. a bitwise andif at least one bit is one
void setBitOr(void* bitmap_ptr, bm_index index, bm_mask mask, uint nb_bulk, uint level)
{
  // grab the bitmap pointer of the level
  void* bitmap_level_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);
  
  // grab the corresponding bitmap of the index
  uint bm = *(uint*)(bitmap_level_ptr + index*ptr_size_byte);

  // compute and and with the mask and store
  bm |= mask;
  *(uint*)(bitmap_level_ptr + index*ptr_size_byte) = bm;

  // update upper map if necessary
  if (level + 1 < max_level(nb_bulk))
    {
      bm_index i = index;
      indexToBitPtr(i, &index, &mask);
      setBitOr(bitmap_ptr, index, mask, nb_bulk, level+1);
    }
  
  return;
}

// setBitAnd: set a bit, and update the upper level w.r.t. a bitwise andif all bits are to one
void unsetBitOr(void* bitmap_ptr, bm_index index, bm_mask mask, uint nb_bulk, uint level)
{
  // grab the bitmap pointer of the level
  void* bitmap_level_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);
  
  // grab the corresponding bitmap of the index
  uint bm = *(uint*)(bitmap_level_ptr + index*ptr_size_byte);

  // set and with mask negation
  *(uint*)(bitmap_level_ptr + index*ptr_size_byte) = bm & ~ mask;

  // update upper map if necessary
  if (level + 1 < max_level(nb_bulk) && bm == mask)
    {
      bm_index i = index;
      indexToBitPtr(i, &index, &mask);
      unsetBitOr(bitmap_ptr, index, mask, nb_bulk, level+1);
    }

  return;
}

// forwardBitPtr: forward the bitptr, until it points to a valid unset bit
 void forwardBitPtr(void* bitmap_ptr, bm_index *index, bm_mask *mask, uint nb_bulk, uint level, uint lookingfor)
{
 
  // we return false, if we are beyond the proper number of level
  if (level + 1 >= max_level(nb_bulk))
    {
      *mask = 0;
      return;
    }

  // looking for overflow
  bm_mask next_mask;
  bm_index next_index;

  // compute the index in the upper level
  indexToBitPtr(*index, &next_index, &next_mask);

  // look for the next mask
  next_mask = nextMask(bitmap_ptr, next_index, next_mask, level+1, nb_bulk, lookingfor);

  // in case we fail => try to look at upper lovel
  if (next_mask == 0)
    {
      forwardBitPtr(bitmap_ptr, &next_index, &next_mask, nb_bulk, level+1, lookingfor);
      if (next_mask == 0)
	{
	  *mask = 0;
	  return;
	}
    }

  // we have or info in next_xxx
  *index = bitPtrToIndex(next_index, next_mask);  
  *mask = nextMask(bitmap_ptr, *index, 1, level, nb_bulk, lookingfor);

  //printf("forward bit ptr stop\n");

  return;
}

// findNextFreeBlock: look for the next available free block
void findNextFreeBlock(void* bitmap_ptr, bm_index *index, bm_mask *mask, uint nb_bulk, uint level)
{
  *mask = nextMask(bitmap_ptr, *index, *mask, level, nb_bulk, 0);

  if (*mask == 0)
    {
      forwardBitPtr(bitmap_ptr, index, mask, nb_bulk, level, 0);
      if (*mask == 0)
	  return;
    }
  
  return;
}

// findNextAllocatedBlock: look for the next allocated block (and increment)
void findNextAllocatedBlock(void* bitmap_ptr, bm_index *index, bm_mask *mask, uint nb_bulk, uint level)
{
  //printf("findNextAllocatedBlock: (%lu, %s)\n", *index, byte_to_binary(*mask));

  uint i = *index;
  
  *mask = nextMask(bitmap_ptr, *index, *mask, level, nb_bulk, 1);

  //printf("next: (%lu, %s)\n", *index, byte_to_binary(*mask));
  
  if (*mask == 0)
    {
      //printf("forwardBitPtr: (%lu, %s)\n", *index, byte_to_binary(*mask));
      forwardBitPtr(bitmap_ptr, index, mask, nb_bulk, level, 1);
      //printf("forwardBitPtr: (%lu, %s)\n", *index, byte_to_binary(*mask));
      if (i >= *index)
	*mask = 0;
    }
  
  return;
}

// getBulkBitPtr: from a bulk address, get the bit pointer
void getBulkBitPtr(void* data, bm_index *index, bm_mask *mask, void** seg)
{
  // first we check that the data might be in our segments
  if (data < min_segment_start || data > max_segment_end)
    {
      /*
      printf("getBulkBitPtr: pointer outside segment range %p\n", 
	     data
	     );
      */
      *mask = 0; return;
    }

  // then we check that data is indeed a pointer of bulk
  if (((uint)(data) & (pointer_mask)) > 0)
    {
      /*
      printf("getBulkBitPtr: not a pointer, %p(%s) & %p > 0 \n", 
	     data, byte_to_binary((uint)(data)),
	     (void*)(pointer_mask)
	     //byte_to_binary((uint)(data)), 
	     //byte_to_binary((uint)(pointer_mask))
	     );
      */
      *mask = 0; return;
    }

  // first we grab the segment pointer
  void* segment = (void*)((uint)(data) & (uint)(segment_mask));
  
  // we grab the magic number of the segment and check that is is valid
  if (magic_number != *(void**)(segment))
    {
      //printf("getBulkBitPtr: wrong magic number\n");
      *mask = 0; return;
    }

  // seems ok, we can grab the heap, and the nb_bulk/bulk_size info
  heap* h = get_segment_heap(segment);
  uint nb_bulk = h->nb_bulk;
  uint bulk_size = h->bulk_size;
  void* bulk_ptr = get_bulk_ptr(segment, nb_bulk);

  // grab the offset of our bulk
  uint bulk_offset = (uint)(data - bulk_ptr);

  // last check: this is indeed a bulk
  if (bulk_offset % (bulk_size * ptr_size_byte) != 0)
    {
      //printf("getBulkBitPtr: not a bulk offset (%p, %p, %lu)\n", data, bulk_ptr, bulk_offset);
      *mask = 0; return;
    }

  // we can compute the index and mask at level 0
  indexToBitPtr(bulk_offset / (bulk_size * ptr_size_byte), index, mask);

  *seg = segment;

  return;
}

//***************************************************************
// print bitmap
void print_bitmap(void* bitmap_ptr, uint nb_bulk)
{
  uint level; 
  for (level = 0; level < max_level(nb_bulk); ++level)
    {
      printf("level: %lu\n", level);
      uint index;
      void* level_ptr = get_level_bitmap_ptr(bitmap_ptr, nb_bulk, level);
      uint index_max = get_level_max_index(nb_bulk, level);
      printf("max index[%lu] := %lu\n", level, index_max);
      for (index = 0; index <= index_max; ++index)
	printf("bm[%lu] := %s\n", index, byte_to_binary(*(uint*)(level_ptr + index*ptr_size_byte)));

    }
  return;
}

// for debugging
void print_list(void* start, void* end, uint nb_bulk)
{
  printf("start := %p; ", start);
  printf("end := %p\n", end);
  while (start!=NULL)
    {
      void* segment = start;
      printf("*******************************************\n");
      printf("%p <- %p -> %p\n", get_segment_prev(segment), segment, get_segment_next(segment));
      printf("-----------------------\n");
      if (nb_bulk != 0) print_bitmap(get_alloc_bitmap_ptr(segment), nb_bulk);
      printf("-----------------------\n");
      if (nb_bulk != 0) print_bitmap(get_root_bitmap_ptr(segment, nb_bulk), nb_bulk);
      start = get_segment_next(segment);
      printf("*******************************************\n");
    }

  printf("\n\n");

  return;
}



//***************************************************************

// allocate a new segment
void* create_segment(){

  // compute the desired size (which is also the alignment
  uint segment_size_ub = 1 << segment_size_n;

  // allocate
  void* segment = memalign(segment_size_ub, segment_size_ub);

  if (segment == NULL)
    return NULL;
  
  // update boundaries for segments address
  if (min_segment_start > segment) 
    min_segment_start = segment;

  if (max_segment_end < (segment + segment_size_ub)) 
    max_segment_end = (segment + segment_size_ub);

  // 
  set_segment_prev(segment, NULL);
  set_segment_next(segment, NULL);

  // and finally put it in the free segment list
  insert_segment_end(&free_segment_start, &free_segment_end, segment);

  return segment;
}

//initialize a segment for a given nb_bulk / bulk_size
void init_segment(void* segment, uint nb_bulk, uint bulk_size)
{

  // update the magic number
  set_magic_number(segment, magic_number);

  // clear counter and alloc/root bitmap
  clearARBMandCount(segment, nb_bulk);

  return;
}

// alloc in a segment
void* allocSegment(void* segment, bm_index *index, bm_mask *mask, bool root, uint nb_bulk, uint bulk_size)
{

  // we grab the bitmap pointer
  void* bitmap_ptr = get_alloc_bitmap_ptr(segment);

  // check that the bit pointer is valid, else return NULL
  uint level_max_index = get_level_max_index(nb_bulk, 0);
  if (*index > level_max_index) return NULL;
  uint max_index_max_mask = get_level_max_mask(nb_bulk, 0);
  if (*index == level_max_index && *mask >= max_index_max_mask) return NULL;  

  // test if the current pointed bit is marked
  if (isMarked(bitmap_ptr, *index, *mask))
    {
      // yes, let's find the next free block
      findNextFreeBlock(bitmap_ptr, index, mask, nb_bulk, 0);
      
      // if there is none, return NULL
      if (*mask == 0)
	return NULL;
    }
  
  // grab the data pointer
  void* data_ptr = get_bulk_ptr(segment, nb_bulk);
  //printf("data_ptr = %p\n", data_ptr);

  // compute the allocated block index
  void* block = blockAddress(data_ptr, *index, *mask, bulk_size);

  // update the root bitmap if necessary
  if (root)
    {
      void* root_bitmap_ptr = get_root_bitmap_ptr(segment, nb_bulk);
      setBitOr(root_bitmap_ptr, *index, *mask, nb_bulk, 0);
    }
  // update the alloc bitmap
  setBitAnd(bitmap_ptr, *index, *mask, nb_bulk, 0);

  // increment the counter
  inc_segment_counter(segment);

  // increment the bit pointer
  inc_bitptr(index, mask);

  // we reset the mem allocated, to help in case of collection
  memset(block,
	 0,
	 bulk_size*ptr_size_byte
	 );
  

  // we found the next free block, pointed by index/mask
  return block;

}

// allocation in a heap
void* allocHeap(heap* h, bool root)
{
  uint nb_bulk = h->nb_bulk;
  uint bulk_size = h->bulk_size;
  void* segment = h->curr_segment;
  bm_index* index = &(h->index);
  bm_mask* mask = &(h->mask);

  void* block;

  if (h->curr_segment == NULL)
    block = NULL;
  else
    block = allocSegment(segment, index, mask, root, nb_bulk, bulk_size);

  if (block == NULL)
    {
      void* new_segment;
      if (segment != NULL)	
	new_segment = get_segment_next(segment);
      else
	new_segment = NULL;

      if (new_segment != NULL)
	{ h->curr_segment = new_segment;
	  set_segment_heap(new_segment, h);
	  h->index = 0;
	  h->mask = 1;
	  return allocHeap(h, root);
	}
      else
	{
	  new_segment = take_segment_start(&free_segment_start, &free_segment_end);
	  if (new_segment != NULL)
	    {
	      insert_segment_end(&(h->segment_start), &(h->segment_end), new_segment);
	      init_segment(new_segment, nb_bulk, bulk_size);
	      h->curr_segment = new_segment;
	      set_segment_heap(new_segment, h);
	      h->index = 0;
	      h->mask = 1;
	      return allocHeap(h, root);
	    }
	  
	}
    }

  return block;

}

// free in a segment
void freeBlock(void* data)
{
  // first we try to grab the segment/index/mask of the data
  void* segment;
  bm_index index;
  bm_mask mask;

  getBulkBitPtr(data, &index, &mask, &segment);

  // we failed: the data is not managed by the garbage collector
  if (mask == 0)
    return;

  // we grab the segment pointer
  heap* h = get_segment_heap(segment);

  // and the number of bulk and their size
  uint nb_bulk = h->nb_bulk;
  //uint bulk_size = h->bulk_size;

  // we grab the root and alloc bitmap pointer
  void* alloc_bitmap_ptr = get_alloc_bitmap_ptr(segment);
  void* root_bitmap_ptr = get_root_bitmap_ptr(segment, nb_bulk);

  // we test if root is set
  if (isMarked(root_bitmap_ptr, index, mask))
    // yes: reset it
    unsetBitOr(root_bitmap_ptr, index, mask, nb_bulk, 0);
  else
    // nothing to do: it was not allocated
    return;

  // we test if alloc is set
  //if (isMarked(alloc_bitmap_ptr, index, mask))
  // yes: reset it (if the root bit is set, then the alloc is also set
  unsetBitAnd(alloc_bitmap_ptr, index, mask, nb_bulk, 0);

  
  // we update the counter
  dec_segment_counter(segment);

  // if the segment is the current segment, we update the heap
  if (h->curr_segment == segment)
    {
      if (index < h->index)
	{
	  h->index = index; h->mask = mask;
	}
      
      if (index == h->index)
	h->mask = mask;

      return;
    }

  // else we try to shift to the right the segment in the heap list as long as we do not encounter the the heap current pointer or we have a less allocated segment
  void* next_segment;
  while ((next_segment = get_segment_next(segment)) && // their is a next segment
	 get_segment_counter(next_segment) > get_segment_counter(segment) // of size greater than the current one
	 ){

    switch_segment_next(&(h->segment_start), &(h->segment_end), segment);

    // if the heap current segment was the next one, we update the heap
    if (h->curr_segment == next_segment)
      {
	h->curr_segment = segment;
	h->index = index;
	h->mask = mask;
	return;
      }
  }

  return;

}

// rearrangeSegList:
// this function basically order the segment of a heap by decreasing count
// segments with count 0 are put back in the free segment list 
// and the heap current segment is the first not full segment
void rearrangeSegList(heap* h)
{
  void* curr_segment = h->segment_start;
  // we traverse the list of segments
  while (curr_segment != NULL)
    {
      // we save the pointer of the next_segment
      void* next_segment = get_segment_next(curr_segment);

      // if the segment count is zero, we grab it, and put it in the free segment list
      if (get_segment_counter(curr_segment) == 0)
	{
	  take_segment(&(h->segment_start), &(h->segment_end), curr_segment);
	  insert_segment_end(&free_segment_start, &free_segment_end, curr_segment);

	  // if the heap current pointer was on this segment, we set it to the next one
	  if (h->curr_segment == curr_segment)
	    {
	      h->curr_segment = next_segment;
	      h->index = 0;
	      h->mask = 1;
	    }
	}
      else
	{
	  // if the segment is full we grab it, and insert it back at the start of the list
	  // only if the one before is not full
	  if (get_segment_counter(curr_segment) == h->nb_bulk) // this segment is full and    
	    {
	      // if the previous one exists and is not full, we grab it and put it at the start of the list	      
	      if (next_segment != NULL && get_segment_counter(curr_segment) < h->nb_bulk)
		{
		  take_segment(&(h->segment_start), &(h->segment_end), curr_segment);
		  insert_segment_start(&(h->segment_start), &(h->segment_end), curr_segment);
		}

	      // if the heap current pointer was on this segment, we set it to the next one
	      if (h->curr_segment == curr_segment)
		{
		  h->curr_segment = next_segment;
		  h->index = 0;
		  h->mask = 1;
		}
	      
	    }
	  
	  // else we do nothing
	  
	}

      // we update the traversal pointer
      curr_segment = next_segment;
    }

  return;

}

//***************************************************************
// collection

/*
markAndPush(O) {
Si , BitPtr 0 = findBitptr(O);
i
if (not isMarked(BitPtr 0 )) {
i
setBit(Pi , 0);
incrementSegmentCount(Si );
push(O); }
}
 */


// markandpush a given bulk (same as before, but their the bulk is pointed by a bitptr)
void markAndPushBitPtr(void* segment, void* block, void* alloc_bitmap_ptr, void* twork_ptr, uint nb_bulk, uint bulk_size, bm_index index, bm_mask mask, void** stacktop)
{

  // not a valid mask
  if (mask == 0)
    return;

  // we test if root is set
  if (!isMarked(alloc_bitmap_ptr, index, mask))
    {
      // no: we need to set it
      setBitAnd(alloc_bitmap_ptr, index, mask, nb_bulk, 0);

      // increment segment counter
      inc_segment_counter(segment);

      // and push the data
      // for that we grab the twork pointer of the data
      void* tworkptr = twork_ptr + bitPtrToIndex(index, mask)*ptr_size_byte;

      // we store their the last stacktop
      *(void**)(tworkptr) = *stacktop;

      // and the next stacktop is the current object
      *stacktop = block;

    }

  

  return;

}

// markandpush a given bulk
void markAndPush(void* data, void** stacktop)
{
  // first grab all info of the data
  void* segment;
  bm_index index;
  bm_mask mask;

  getBulkBitPtr(data, &index, &mask, &segment);

  // we failed: the data is not managed by the garbage collector
  if (mask == 0)
    return;

    // we grab the segment pointer
  heap* h = get_segment_heap(segment);

  // and the number of bulk and their size
  uint nb_bulk = h->nb_bulk;
  uint bulk_size = h->bulk_size;

  // we grab the alloc bitmap pointer
  void* alloc_bitmap_ptr = get_alloc_bitmap_ptr(segment);

  void* twork_ptr = get_segment_twork_ptr(segment, nb_bulk, bulk_size);

  markAndPushBitPtr(segment,
		    data,
		    alloc_bitmap_ptr,
		    twork_ptr,
		    nb_bulk,
		    bulk_size,
		    index,
		    mask,
		    stacktop
		    );

  return;

}

// tracingliveobjects of a heap
void traceHeapLiveObjects(heap* h)
{
  // the stack pointer (initially NULL)
  void* stackp = NULL;

  uint nb_bulk = h->nb_bulk;
  uint bulk_size = h->bulk_size;

  // we look for all object marked as root in the heap
  // first we traverse all the segments
  void* segment = h->segment_start;
  while (segment != NULL)
    {
      uint count = 0;

      // we traverse the segment root bulk
      bm_index index = 0;
      bm_mask mask = 1;
      
      void* root_bitmap_ptr = get_root_bitmap_ptr(segment, nb_bulk);
      void* alloc_bitmap_ptr = get_alloc_bitmap_ptr(segment);
      void* data_ptr = get_bulk_ptr(segment, nb_bulk);
      void* twork_ptr = get_segment_twork_ptr(segment, nb_bulk, bulk_size);

      //print_bitmap(root_bitmap_ptr, nb_bulk);
      
      findNextAllocatedBlock(root_bitmap_ptr, &index, &mask, nb_bulk, 0);

      uint level_max_index = get_level_max_index(nb_bulk, 0);
      uint max_index_max_mask = get_level_max_mask(nb_bulk, 0);

      // while we find marked bit
      while (mask != 0 && (index < level_max_index || (index == level_max_index && mask < max_index_max_mask)))
	{
	  ++count;
	  //printf("now looking: (%lu, %s)\n", index, byte_to_binary(mask));

	  // markit
	  markAndPushBitPtr(segment,
			    blockAddress(data_ptr, index, mask, bulk_size), 
			    alloc_bitmap_ptr, 
			    twork_ptr, 
			    nb_bulk, 
			    bulk_size, 
			    index, 
			    mask, 
			    &stackp);

	  inc_bitptr(&index, &mask);
	  
	  // and find next
	  findNextAllocatedBlock(root_bitmap_ptr, &index, &mask, nb_bulk, 0);

	} 

      //printf("tracing segment: %p (%lu)\n", segment, count);

      // go to nextblock
      segment = get_segment_next(segment);

    }

  // then pop all marked object and push their children
  
  while(stackp != NULL)
    {
      //printf("stackp := %p\n", stackp);

      // we pop the value

      // the last object is pointed by stackp
      void* o = stackp;

      // we pop the elements and its parameters
      void* o_segment;
      bm_index o_index;
      bm_mask o_mask;
      
      getBulkBitPtr(o, &o_index, &o_mask, &o_segment);

      heap* o_heap = get_segment_heap(o_segment);
      uint o_nb_bulk = o_heap->nb_bulk;
      uint o_bulk_size = o_heap->bulk_size;

      void* o_twork_ptr = get_segment_twork_ptr(o_segment, o_nb_bulk, o_bulk_size);

      void* o_tworkptr = o_twork_ptr + bitPtrToIndex(o_index, o_mask)*ptr_size_byte;
      
      stackp = *(void**)(o_tworkptr);

      // we mark all its children
      uint i;
      for (i = 0; i < o_bulk_size; ++i)
	{
	  markAndPush(*(void**)(o + i*ptr_size_byte), &stackp);
	}

    }

  //printf("tracing done\n");

  // finished
  return;

}

// initialization of a heap for a given bulk_size
void initHeap(heap* h, uint bulk_size)
{

  // segment_size
  uint segment_size_ub = 1 << segment_size_n;

  h->segment_start = NULL;
  h->segment_end = NULL;
  h->curr_segment = NULL;
  h->bulk_size = bulk_size;
  h->nb_bulk = nb_bulk_ub(segment_size_ub, bulk_size);
  h->index = 0;
  h->mask = 1;

  return;
}

// clearing all bitmaps and counts of the segments of a given heap
void clearAllBitmapsAndCount(heap* h)
{
  void* curr_segment = h->segment_start;

  uint nb_bulk = h->nb_bulk;

  // we traverse the list of segments
  while (curr_segment != NULL)
    {
      clearABMandCount(curr_segment, nb_bulk);
      
      curr_segment = get_segment_next(curr_segment);
    }

  return;
}

/******************************************************************************************/
// global variables of the GC

// the maximal bulk_size in power of 2 of void* (represents also the number of heap - 1)
uint max_bulk_size;

// the heaps: a series of heap of bulk_size = 2^n, for increasing n (with at least one element)
heap *heaps;

// entry functions

// tracing all live objects
void traceLiveObjects()
{
  // we just traverse all the heap and call their trace functions
  uint i;

  for (i = 0; i <= max_bulk_size; ++i)
    traceHeapLiveObjects(&(heaps[i]));

  return;

}

// bitmap marking and garbage collecting
void bitmapMarkingGC()
{
  // first clear all alloc bitmap and counter for all heap
  uint i;

  for (i = 0; i <= max_bulk_size; ++i)
    clearAllBitmapsAndCount(&(heaps[i]));

  // trace live objects
  traceLiveObjects();

  // rearrange the segments
  for (i = 0; i <= max_bulk_size; ++i)
    rearrangeSegList(&(heaps[i]));

  return;

}

// allocation function (the bool means that it is a root)
void* gc_alloc(uint size, bool root)
{
  if (size == 0)
    return NULL;

  // first grab the cell floor of log 2 of size: this is the index in the heap array
  // size is in byte, while the bulk_size are in sizeof(void*) 
  uint n = cell_log2(size/ptr_size_byte);

  // to big to allocate (here we might want to have the copying GC)
  if (n > max_bulk_size)
    return NULL;

  void* res = allocHeap(&(heaps[n]), root);

  // the allocation fails
  if (res== NULL)
    {
      // first, let's try to clean up a bit
      bitmapMarkingGC();
      // then retry allocating
      res = allocHeap(&(heaps[n]), root);

      // still a failure
      if (res== NULL)
	{
	  // let's try allocating a new segment
	  if (create_segment() != NULL)
	    // last chance allocation (should be ok)
	    res = allocHeap(&(heaps[n]), root);

	}

    }

  return res;

}

// the freeing of data (only work for root)
void gc_free(void* data)
{
  return freeBlock(data);
}

// unset as root
void unset_root(void* data)
{
  // first we try to grab the segment/index/mask of the data
  void* segment;
  bm_index index;
  bm_mask mask;

  getBulkBitPtr(data, &index, &mask, &segment);

  // we failed: the data is not managed by the garbage collector
  if (mask == 0)
    return;

  // we grab the segment pointer
  heap* h = get_segment_heap(segment);

  // and the number of bulk and their size
  uint nb_bulk = h->nb_bulk;

  // we grab the root and alloc bitmap pointer
  void* root_bitmap_ptr = get_root_bitmap_ptr(segment, nb_bulk);

  // we test if root is set
  if (isMarked(root_bitmap_ptr, index, mask))
    // yes: reset it
    unsetBitOr(root_bitmap_ptr, index, mask, nb_bulk, 0);

  return;

}

// set as root
void set_root(void* data)
{
  // first we try to grab the segment/index/mask of the data
  void* segment;
  bm_index index;
  bm_mask mask;

  getBulkBitPtr(data, &index, &mask, &segment);

  // we failed: the data is not managed by the garbage collector
  if (mask == 0)
    return;

  // we grab the segment pointer
  heap* h = get_segment_heap(segment);

  // and the number of bulk and their size
  uint nb_bulk = h->nb_bulk;

  // we grab the root and alloc bitmap pointer
  void* root_bitmap_ptr = get_root_bitmap_ptr(segment, nb_bulk);

  // we test if root is set
  if (!isMarked(root_bitmap_ptr, index, mask))
    // no: set it
    setBitOr(root_bitmap_ptr, index, mask, nb_bulk, 0);

  return;

}

/*********************************************/
void print_heaps()
{
  uint i;
  for (i = 0; i <= max_bulk_size; ++i)
    {
      printf("-------------------------\n");
      printf("heap (nb_bulk := %lu, bulk_size := %lu):=\n", heaps[i].nb_bulk, heaps[i].bulk_size);
      print_list(heaps[i].segment_start, heaps[i].segment_end, heaps[i].nb_bulk);
      printf("-------------------------\n\n");

    }
  
}

/******************************************************************************************/

char gc_init(uint n){

  // compute the power of two of a the size of a pointer
  ptr_size_bit_pow2 = floor_log2(ptr_size_bit);

  // do some check
  if(sizeof(void*) != sizeof(uint)) {
    //we assert that it is a proper power of two
    printf("catasrophic: uint and void* are of different size !!!");
    return 1;
  }

  if(ptr_size_bit != (uint)(1) << ptr_size_bit_pow2) {
    //we assert that it is a proper power of two
    printf("catasrophic: ptr_size_bit is not a power of 2: %lu != 1 << %lu == %lu\n", ptr_size_bit, ptr_size_bit_pow2, (uint)(1) << ptr_size_bit_pow2);
    return 1;
  }

  // init the the segment size and the mask
  segment_size_n = n;
  printf("n := %lu\n", n);

  segment_mask = 1;
  uint i;
  for (i = 1; i < segment_size_n; ++i)
    {
      segment_mask <<= 1;
      segment_mask+=1;
    }
  segment_mask = ~segment_mask;
  printf("segment_mask = %s\n", byte_to_binary((uint)(segment_mask)));
  
  // initialize the pointer mask
  pointer_mask = 1;
  for (i = 1; i < floor_log2(ptr_size_byte); ++i)
    {
      pointer_mask <<= 1;
      pointer_mask+=1;
    }
  printf("pointer_mask = %s\n", byte_to_binary((uint)(pointer_mask)));  

  // initialize magic_number
  magic_number = (void*)(0xdeadbeef);

  // initialize free segment list
  free_segment_start = NULL;
  free_segment_end = NULL;

  // segment_size
  uint segment_size_ub = 1 << segment_size_n;

  // initialize the heap
  // first compute the max bulk_size (as a power of two, starting from n)
  max_bulk_size = n;
  while (nb_bulk_ub(segment_size_ub, 1 << max_bulk_size) == 0)
    (--max_bulk_size);
  
  printf("max_bulk_size = %lu (== max alloc := %lu bytes)\n", max_bulk_size, (1<<max_bulk_size)*ptr_size_byte);

  //allocate the heap
  heaps = (heap*)(malloc(sizeof(heap) * (max_bulk_size+1)));

  // and initialize the heaps
  for (i = 0; i <= max_bulk_size; ++i)
    initHeap(&heaps[i], 1 << i);

  return 0;
}

#ifdef WITHMAIN
int main(int argc, char** argv, char** arge)
{
  gc_init(12);

  // something stupid: allocated until you can't (increasing wanted size)
  uint size = 1;
  void* data;
  while ((data = gc_alloc(size, false)) != NULL)
    {
      //printf("size := %lu, data := %p\n", size, data);
      ++size;
    }
  
  printf("max size := %lu", size);

  print_heaps();  

  gc_alloc(--size, true);
  gc_alloc(size, true);
  gc_alloc(size, true);
  gc_alloc(size, true);
  gc_alloc(size, true);
  gc_alloc(size, true);

  print_heaps();  

  return 0;
}
#endif
