#include "config.h"

#if WORD_SIZE_BYTES == 8
#define REG(x) r##x
#define WORD(x) x##q
#define END_STACK .quad 0
#endif


#if WORD_SIZE_BYTES == 4
#define REG(x) e##x
#define WORD(x) x##l
#define END_STACK .long 0
#endif

        .text
        .global __go

__go:
        WORD(push) %REG(bx)
        WORD(push) %REG(si)
        WORD(push) %REG(di)
        WORD(push) %REG(bp)

        # switch stacks
        WORD(mov)   %REG(sp), %REG(ax)
        WORD(lea)   (stack + STACK_SIZE_BYTES + PAGE_SIZE_BYTES), %REG(sp)
        WORD(push)  %REG(ax)

        WORD(lea) heap1, %REG(bp) # set heap
        WORD(push) $1f
        jmp __main
        END_STACK

1:      WORD(pop) %REG(sp)
        WORD(pop) %REG(bp)
        WORD(pop) %REG(di)
        WORD(pop) %REG(si)
        WORD(pop) %REG(bx)
        ret





