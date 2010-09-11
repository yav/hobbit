#include "config.h"

# NOTE: we assume that HEAP_SIZE and STACK_SIZE are multiples of PAGE_SIZE

        .section abstract_data, "aw", @nobits


        .global stack
        .global heap1
        .global heap2

        .align PAGE_SIZE

        .space PAGE_SIZE      # protected to detect end of stack
stack:  .space STACK_SIZE

heap1:  .space HEAP_SIZE
        .space PAGE_SIZE      # protected to detect end of heap

heap2:  .space HEAP_SIZE
        .space PAGE_SIZE      # protected to detect end of heap


        .text

################################################################################

        .global __gc_walk_stack

        # EAX: scavange method for the frame
        # EBX: beginning (end) of frame
        # EDI: top of the to-heap

__gc_walk_stack:
        call *%eax              # scavange frame
        movl (%ebx), %eax       # get return address
        addl $4, %ebx           # skip return adddress
        movl -4(%eax), %eax     # get new scavange method
        cmpl $0, %eax
        jnz __gc_walk_stack
        jmp __gc_scav_glob





################################################################################

        .global __gc_collector

        # EDI: top of the to-heap (end of the queue)

__gc_collector:
        movl to_heap, %ebx

1:      cmpl %ebx, %edi
        je 1f 

        movl (%ebx), %eax                     # EAX = object tag
        shrl $16, %eax                        # get GC part of tag
        movl __gc_scav_table(,%eax,4), %eax   # lookup addr of scav. method
        call *%eax                            # call scav method
        jmp 1b

1:      ret



################################################################################

        .global __gc_copy

        # ESI: pointer to the object 
        # EDI: top of the to-heap 
        # DF = 1 (we are copying up)
        # The pointer to the new object is returned in EAX.

        # This should preserve EBX for scavenging to work.

1:      .string "copy\n"

__gc_copy:
        # check if already copied
        movl (%esi), %eax
        testl $1, %eax
        jz 1f

        # get size
        shrl $16, %eax
        movl __gc_copy_table(,%eax,4), %ecx

        # save ptrs for forwarding update, then copy
        movl %esi, %edx         # pointer to old object
        movl %edi, %eax         # pointer to new object
        rep movsl

        # place a forwarding pointer
        movl %eax, (%edx)

1:      ret




        .global main

main:   leal heap1, %ebp                  # setup the heap
        movl %ebp, from_heap              # initialize 'from_heap'
        leal heap2, %eax
        movl %eax, to_heap                # initialize 'to_heap'
        leal (stack + STACK_SIZE), %esp   # setup the stack
        call init_rts
        pushl $1f
        jmp __main
        .long 0                           # scavange globals
1:      jmp __stop

