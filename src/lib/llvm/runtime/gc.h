#ifndef GC_INCLUDE
#define GC_INCLUDE

typedef unsigned long uint;

typedef char bool;

#define true 1;
#define false 0;

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
