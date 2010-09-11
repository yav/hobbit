#define _GNU_SOURCE 1

#include <sys/mman.h>       // Memory managment
#include <stdio.h>          // perror, printf
#include <signal.h>         // Signal handler stuff
#include <stdlib.h>         // exit
#include <errno.h>          // errno
#include <sys/ucontext.h>   // contexts (GNU_SOURCE is for this)

#include "rts.h"


// XXX: if we run out of stack, then how does the handler pass us
// its arguments?

static
void start_gc(int sig, siginfo_t *info, void* uctxt) {
  greg_t *regs    = ((ucontext_t*)uctxt)->uc_mcontext.gregs;
  Word* bad       = (Word*)(info->si_addr);
  Scavenger scav  = (Scavenger)(regs[REG_RAX]); // XXX
  Word* frame     = (Word*)(regs[REG_RSP]);     // XXX
  Word free_words;

  if (!heap_fault(bad)) {
    if (stack_fault(bad))
      printf("Out of stack.\n");
    else
      printf("Bad memory access (%p).\n",bad);
    exit(1);
  }

  to_heap_top = to_heap;
  __gc_collector(scav, frame);
  free_words = HEAP_SIZE_WORDS - (to_heap_top - to_heap);
  if (free_words < PAGE_SIZE_WORDS) {
    printf("Out of memory.\n");
    exit(1);
  }
  // the new heap pointer
  regs[REG_RBP] = (Word)to_heap_top;

  // swap the heaps
  to_heap_top = to_heap;
  to_heap = from_heap;
  from_heap = to_heap_top;
}





int main(int argc, char* argv[]) {
  static struct sigaction sa;

  // Protect the ends of the heaps, and the bottom of the stack
  if ( mprotect (heap1 + HEAP_SIZE_WORDS, PAGE_SIZE_BYTES, PROT_NONE) == -1
    || mprotect (heap2 + HEAP_SIZE_WORDS, PAGE_SIZE_BYTES, PROT_NONE) == -1
    || mprotect (stack, PAGE_SIZE_BYTES, PROT_NONE) == -1)
       goto err;

  // Setup signal handler for page faults
  sa.sa_flags     = SA_SIGINFO; /* | SA_ONESHOT; */
  sa.sa_sigaction = start_gc;
  if (sigaction(SIGSEGV, &sa, NULL) == -1) goto err;

  // setup heaps
  from_heap = heap1;
  to_heap = heap2;

  // go!
  __go();
  return 0;

err:
  perror("init_rts");
  return errno;
}


void __crash(const char* msg, Word tag) {
  printf("crash (%lx): %s\n",tag,msg);
  exit(1);
}

void __trace(Word how, Word what) {
  if (how == 16)
    printf("trace(%lu): %lx\n",how,what);
  else
    printf("trace(%lu): %lu\n",how,what);
}


