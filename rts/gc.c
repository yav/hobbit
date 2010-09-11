#include "rts.h"
#include <string.h> // for memcpy
#include <stdio.h> // for memcpy


Word __gc_dummy = 0;

Word* __gc_copy(Word* src) {
  Word size, header = *src;
  Word *new_addr;

  if (is_forwarding(header)) return (Word*)header;
  size = __gc_copy_table[get_obj_descr(header)];
  new_addr = to_heap_top;
  to_heap_top += size;
  memcpy(new_addr,src,size * WORD_SIZE_BYTES);
  *src = (Word)new_addr;
  return new_addr;
}

void __gc_collector(Scavenger scavenge, Word* frame) {
  Word *todo;

  printf("Started collector\n");

  // Process the objects on the stack.
  do {
    Word *ret;
    frame = scavenge(frame);    // process objects in the frame
    ret = (Word*)(*frame);      // the adress of our caller
    frame++;                    // skip the caller address
    scavenge = (Scavenger)(*(ret - 1));
  } while (scavenge);

  // Traverse the gloabal variables
  __gc_scav_glob();

  // Process the objects in the to-heap.
  todo = to_heap;
  for ( todo = to_heap
      ; todo < to_heap_top
      ; todo = __gc_scav_table[get_obj_descr(*todo)](todo)
      );
}
