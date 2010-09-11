#ifndef RTS_H
#define RTS_H

#include "config.h"

typedef unsigned char Byte;
typedef unsigned short int Word;
typedef unsigned int DWord;

extern Byte heap1[], heap2[], stack[];
extern Byte *from_heap, *to_heap;

#define freeBytes(base,top) (HEAP_SIZE - (top - base))

#define inPage(page,addr)   (((page) <= (addr)) \
                          && ((addr) < ((page) + PAGE_SIZE)))

#define stackFault(addr)    (inPage((DWord)stack - PAGE_SIZE,addr))

#define heapFault(addr)     (inPage((DWord)heap1 + HEAP_SIZE,addr) \
                          || inPage((DWord)heap2 + HEAP_SIZE,addr))

const char* itoa(unsigned base, unsigned num);
void __stop();
void __init_rts();
void __trace(unsigned base, unsigned x);
void __crash(const char* msg, unsigned tag);
DWord __start_gc(DWord bad, DWord eax, DWord esp);

void __debug(const char *format, ...);

#endif /* RTS_H */



