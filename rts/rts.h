#ifndef RTS_H
#define RTS_H 1

#include "config.h"

typedef long Word;  // This is the type of a mahchine word/address

// We allocate an extra page to use for protection.
Word heap1[HEAP_SIZE_WORDS  + PAGE_SIZE_WORDS]
  __attribute__ ((aligned (PAGE_SIZE_BYTES)));
Word heap2[HEAP_SIZE_WORDS  + PAGE_SIZE_WORDS]
  __attribute__ ((aligned (PAGE_SIZE_BYTES)));
Word stack[STACK_SIZE_WORDS + PAGE_SIZE_WORDS]
  __attribute__ ((aligned (PAGE_SIZE_BYTES)));

#define in_page(page,addr)  ((Word)(page) == ((Word)(addr) & PAGE_MASK))
#define stack_fault(addr)   in_page(stack,addr)
#define heap_fault(addr)    ( in_page(heap1 + HEAP_SIZE_WORDS, addr) \
                           || in_page(heap2 + HEAP_SIZE_WORDS, addr) )


// -- GC related --------------------------------------------------------------

// a Scavanger is a function that given a pointer to an object
typedef Word* (*Scavenger)(Word*);

#define is_forwarding(p)  (((p) & 1) == 0)
#define get_obj_descr(p)  ((p) >> (WORD_SIZE_BITS / 2))

Word *from_heap, *to_heap;    // the bases of the current, and other heap
Word *to_heap_top;            // used while we are scavanging the to-heap.

// These are defined by the compiler
extern Word       __gc_copy_table[];    // sizes of objects
extern Scavenger  __gc_scav_table[];    // how to scavange an object
extern void       __gc_scav_glob();

Word* __gc_copy(Word* src);
void  __gc_collector(Scavenger scavenge, Word* frame);


// -- Misc

void __go();                                // for starting programs
void __crash(const char* msg, Word tag);    // for crahsing
void __trace(Word base, Word x);            // for debugging
#endif
