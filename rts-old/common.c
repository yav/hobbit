#include "rts.h"


Byte *from_heap, *to_heap;
DWord __gc_dummy = 0;

void __trace(unsigned base, unsigned x) {
  if (base == 10) __debug("trace (%u): %u\n", base, x);
             else __debug("trace (%u): 0x%x\n", base, x);
}


void __crash(const char* msg, unsigned tag) {
  __debug(msg);
  __debug("gc_tag = %d, data_tag = %d\n", tag >> 16, tag & 0xFFFF);
  __stop();
}


DWord __start_gc(DWord bad, DWord eax, DWord esp) {
  DWord heap, free;
  Byte* tmp;

  if (!heapFault(bad)) {
    if (stackFault(bad)) __debug("Out of stack.\n");
                   else  __debug("Bad memory access (0x%x).\n",bad);
    __stop();
  }

  __debug("GC... ");

  /* GC! */
  asm volatile
    ("cld                    \n\t"    /* Copy up */
     "movl %[to_heap], %%edi \n\t"    /* EDI: the to-heap */
     "movl %[esp], %%ebx   \n\t"      /* EBX: beginning of frame */
     "movl %[scav], %%eax    \n\t"    /* EAX: scavenger method */
     "call __gc_walk_stack   \n\t"    /* Go! */
     "movl %%edi, %[heap]        "    /* The final to-heap is in 'heap' */

    : [heap] "=g" (heap)
    : [to_heap] "g" (to_heap), [esp] "g" (esp), [scav]  "g" (eax)
    : "eax", "ebx", "ecx", "edx", "esi", "edi", "memory");
    /* Do we need memory? This is such a terrible construct. */

  free = freeBytes((DWord)to_heap,heap);
  __debug("heap: %uK, stack: %uK\n", free >> 10, 
                                    ((DWord)esp - (DWord)stack) >> 10);

  if (free < TOO_SMALL) {
    __debug("Out of memory.\n");
    __stop();
  }

  tmp       = to_heap;         /* Swap the two heaps */
  to_heap   = from_heap;
  from_heap = tmp;

  return heap;
}





