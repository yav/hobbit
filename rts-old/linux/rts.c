#include <sys/mman.h>       /* Memory managment */
#include <stdio.h>          /*  perror */
#include <signal.h>         /* Signal handler stuff */
#include <stdlib.h>         /* exit */
#define __USE_GNU
#include <sys/ucontext.h>   /* User contexts */

#include "../rts.h"



static
void start_gc(int sig, siginfo_t *info, void* uctxt) {
  greg_t *regs = ((ucontext_t*)uctxt)->uc_mcontext.gregs;
  regs[REG_EBP] = __start_gc( (DWord)(info->si_addr),
                              regs[REG_EAX]
                              regs[REG_ESP] );
}


void init_rts() {
  static struct sigaction sa;

  /* Protect the ends of the heaps, and the bottom of the stack */
  if ( mprotect (heap1 + HEAP_SIZE, PAGE_SIZE, PROT_NONE) == -1
    || mprotect (heap2 + HEAP_SIZE, PAGE_SIZE, PROT_NONE) == -1
    || mprotect (stack - PAGE_SIZE, PAGE_SIZE, PROT_NONE) == -1)
       goto err;

  /* Setup signal handler for page faults */
  sa.sa_flags     = SA_SIGINFO; /* | SA_ONESHOT; */
  sa.sa_sigaction = start_gc;
  if (sigaction(SIGSEGV, &sa, NULL) == -1) goto err;

  return;

err:
  perror("init_rts");
  __stop();
}

void __stop() { exit(0); }



