
/* errors */
#define ERR_CANNOT_INIT       1
#define ERR_PMATCH_FAILURE    2
#define ERR_OUT_OF_HEAP       3


#define HEAP_SIZE       262144         /* words */
#define PTR_STACK_SIZE  (1024 * 1024)  /* bytes */


#define freeHeap        (heap_end - heap)
#define stackPtrTo(x)   asm("movl (%%ebp), %0" : "=r" (x))


typedef unsigned char   Byte;
typedef unsigned short  Word;
typedef unsigned int    DWord;

typedef union ObjHeader {
  union ObjHeader *forward;    
  struct {
    union {
      Word value;
      Word not_forwarded : 1; 
    } tag;
    Byte size;
    Byte ptrs_offset;
  } header;
} ObjHeader;


DWord *heap, *heap_end;
DWord heap1[HEAP_SIZE];                 
DWord heap2[HEAP_SIZE];                
ObjHeader **ptr_stack; 


void crash(void);
DWord* alloc(unsigned word_num);


void init(unsigned ptr_stack_size);
void gc(ObjHeader **end_ptr_stack);
ObjHeader* copy(ObjHeader *p);
ObjHeader* scavenge(ObjHeader* p);

void showHeader(ObjHeader*);

extern DWord theMain(void);


