#ifndef CONFIG_H
#define CONFIG_H

// The size of the heap should a be a multiple of the page size.

#define PAGE_SIZE   4096
#define HEAP_SIZE   (2 * 1024 * PAGE_SIZE)
#define STACK_SIZE  (256 * PAGE_SIZE)
#define TOO_SMALL   PAGE_SIZE

#endif /* CONFIG_H */




