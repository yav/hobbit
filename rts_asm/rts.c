#include <stdlib.h>
#include <stdio.h>
#include <sys/mman.h>
#include <errno.h>
#include "rts.h"

inline
void set_heap(DWord* h) {
  heap      = h;
  heap_end  = h + HEAP_SIZE;  
}

inline unsigned roundUp(unsigned n, unsigned unit) {
  return ((n + unit - 1) / unit) * unit;
}

void init (unsigned ptr_stack_size) {
  unsigned ps = getpagesize();
  unsigned ss = roundUp(ptr_stack_size,ps);

  if ((ptr_stack = (ObjHeader**) 
        mmap(0, ss + ps, PROT_READ | PROT_WRITE
                       , MAP_ANONYMOUS | MAP_PRIVATE, 0, 0)) == MAP_FAILED) {
    printf("Failed\n");
    perror("init (1)"); 
    exit(ERR_CANNOT_INIT);
  } 
 
  if ( mprotect(ptr_stack + (ss / sizeof(*ptr_stack)), ps, PROT_NONE) == -1 ) {
    printf("Failed\n");
    perror ("init (2)"); 
    exit(ERR_CANNOT_INIT);
  }

  set_heap(heap1);
}



void crash() { 
  printf("crashed!\n");
  exit(ERR_PMATCH_FAILURE);
}

DWord* alloc(unsigned word_num) {
  DWord* result;          
  
  if (freeHeap < word_num) {
    ObjHeader **end_ptr_stack;
    stackPtrTo(end_ptr_stack);
    gc(end_ptr_stack);
      
    if (freeHeap < word_num) { 
      puts("Out of heap.");
      exit(ERR_OUT_OF_HEAP);
    }
  }      
  result = heap;
  heap  += word_num;
  return result;
} 

void gc(ObjHeader **end_ptr_stack) {
  ObjHeader **root, *todo;

  set_heap ((heap_end == heap1 + HEAP_SIZE) ? heap2 : heap1);
  todo = (ObjHeader*)heap;

  for (root = ptr_stack; root <= end_ptr_stack; ++root) 
    *root = copy(*root);

  while ((DWord*)todo < heap) 
    todo = scavenge(todo);
} 

ObjHeader* copy(ObjHeader* p) {
  DWord* from;
  unsigned n;

  if (p->header.tag.not_forwarded) {
    ObjHeader* addr = (ObjHeader*)heap;
    for (from = (DWord*)p, n = p->header.size; n > 0; --n, ++heap, ++from)
      *heap = *from;
    p->forward = addr;
    return addr;
  } else {
    return p->forward; 
  }
}

ObjHeader* scavenge(ObjHeader* p) {
  unsigned n; 
  ObjHeader **q;

  for ( n = p->header.size - p->header.ptrs_offset, 
        q = (ObjHeader**)((DWord*)p + p->header.ptrs_offset); 
        n > 0; 
        --n, ++q) *q = copy(*q); 

  return (ObjHeader*)q;
}


/* For debugging */
void showHeader(ObjHeader* p) {
  if (p->header.tag.not_forwarded) {
    printf("size: %d, ptrs: %d, tag: %d\n", p->header.size
                                          , p->header.ptrs_offset
                                          , p->header.tag.value);
  } else printf("Forwarded(%p)\n",p->forward);
}

int fromNat(ObjHeader* p) {
  int sum = 0;        
  while(1) {
    Word t = p->header.tag.value;
    switch (t) {
      case 1: return sum;
      case 3: ++sum; break;
      default: printf("Unknown tag: \%d\n",t); exit(1);
    }
    p = (ObjHeader*)(*(((DWord*)p) + 1));
  }
}


int main (int argc, char* args[]) {
  init(PTR_STACK_SIZE);  
  printf("%d\n",fromNat((ObjHeader*)theMain()));
  return 0;
}
            
        


