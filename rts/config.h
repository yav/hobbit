#define PAGE_BITS           12
#define WORD_SIZE_BYTES     8
#define HEAP_SIZE_PAGES     1024
#define STACK_SIZE_PAGES    1024

// -- Derived ------------------------------------------------------------

#define WORD_SIZE_BITS      (8 * WORD_SIZE_BYTES)

#define PAGE_MASK           ((-1) << PAGE_BITS)

#define PAGE_SIZE_BYTES     (1 << PAGE_BITS)
#define PAGE_SIZE_WORDS     (PAGE_SIZE_BYTES / WORD_SIZE_BYTES)

#define HEAP_SIZE_WORDS     (HEAP_SIZE_PAGES * PAGE_SIZE_WORDS)
#define STACK_SIZE_WORDS    (STACK_SIZE_PAGES * PAGE_SIZE_WORDS)
#define STACK_SIZE_BYTES    (STACK_SIZE_WORDS * WORD_SIZE_BYTES)


