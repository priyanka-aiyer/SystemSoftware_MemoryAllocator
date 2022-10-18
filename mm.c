/*
*
* Dynamic Memory Allocator Program using Segregated Free List.
*
* Implementation of a dynamic memory allocator requires to develop main functions, namely; 
* mm_init(), malloc(), free(), realloc() and its related helper functions, and the checkheap() function. 
* Implemented a segregated free list algorithm which makes use of an array of 20 free lists, where each array contains blocks of the same size class. 
* ### Initial: Implemented "Implicit search - First fit" approach
* ### Final: Implemented "Segregation Free List" approach to improve on the Utilization and Throughout. 
*/

#include <assert.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
 
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

#define ALIGNMENT 16

// citation: csapp textbook;
#define WORDSIZE 8          
#define DOUBLESIZE WORDSIZE*2
#define CHUNK (1<<12)

#define INITIALCHUNK (1<<6)
#define SEGLIST_SIZE 20
#define REALLOC_BUF (1<<7)    

////
//// Static functions - Declarations
////
// citation: csapp textbook;
// Max and Min of two numbers

static inline size_t maximum(size_t x, size_t y){
return ((x) > (y) ? (x) : (y));
} 
static inline size_t minimum(size_t x, size_t y){
return ((x) < (y) ? (x) : (y));
}


// Get a word from address p
static inline size_t read_word(void *p){
return (*(size_t *)(p));
}

// Reallocation tag for free block
static inline size_t read_tag(void *p){
return (read_word(p) & 0x2);
}

// Put a word at address p
static inline void write_word(void *p, size_t val){
(*(size_t *)(p) = (val) | read_tag(p));
}

// Write value without tag
static inline void write_no_tag(void *p, size_t val){
(*(size_t *)(p) = (val));
}

//set an allocated bit alongwith size into the word 
static inline size_t set_word(size_t size, size_t alloc){
return ((size) | (alloc));
}

// Set previous and next pointers for a free block
static inline void set_pointer(void *p, void *ptr){
(*(size_t *)(p) = (size_t)(ptr));
}

// Get the size from address p  
static inline size_t fetch_size(void *p){
return (read_word(p) & ~0xf);
}

// Get the allocated word from address p 
static inline size_t fetch_alloc(void *p){
return (read_word(p) & 0x1);
}

// Set and Remove reallocation tag 
static inline void set_realloc_tag(void *p){
size_t x = read_word((void *)p);
x=x|0x2; *(size_t *)p=x;
}

static inline void del_realloc_tag(void *p){
size_t x = read_word((void *)p);
x=x&~0x2; *(size_t *)p=x;
} 

// Get address of a block's header and footer
static inline void* header_ptr(void *ptr){
return ((ptr) - WORDSIZE);
}
static inline void* footer_ptr(void *ptr){
return ((ptr) + fetch_size(header_ptr(ptr)) - DOUBLESIZE);  
}

// Get address of previous and next blocks 
static inline void* next_blockptr(void *ptr){
return ((ptr) + fetch_size((ptr) - WORDSIZE));
}
static inline void* prev_blockptr(void *ptr){
return ((ptr) - fetch_size((ptr) - DOUBLESIZE));  
}

// Get address of free block's predecessor and successor pointers 
static inline void* get_pred_ptr(void *ptr){
return ((ptr));
}
static inline void* get_succ_ptr(void *ptr){
return ((ptr) + WORDSIZE);
}

// Get address of free block's predecessor and successor
static inline void* get_pred(void *ptr){
return (*(void **)(ptr));
}
static inline void* get_succ(void *ptr){
return (*(void **)((ptr) + WORDSIZE));
}

////
//// HELPER functions - Declarations
////
// Heap extension of 'size'
static void *heap_extension(size_t size);

// Merge free blocks - the boundary tags 
static void *block_coalescing(void *ptr);

// Place block of adj_size bytes - split free blocks
static void *insert_block(void *ptr, size_t asize);

// Insertion of node
static void node_insert(void *ptr, size_t size);

// Deletion of node
static void node_del(void *ptr);

////
//// Declarations of given functions
////
static bool in_heap(const void* p);
static bool aligned(const void* p);

//// Global Variables
static char *heap_ptr;             // pointer to first-block in heap 
void *seg_freelist[SEGLIST_SIZE];    // pointer to seg-lists of diff lengths 

/* rounds up to the nearest multiple of DSIZE */
static size_t align(size_t x) {
return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

////
//// HELPER Functions - Definitions
////
// Helper function: Heap extension with a free block required for allocation
static void *heap_extension(size_t size) 
{
    void *ptr;                   
    size_t esize;
    
    // citation: csapp textbook;   
    // esize = (size % 2) ? (size+1) * WORDSIZE : size * WORDSIZE;

    // Maintain alignment by allocating bytes
//*    esize = align(size);
    esize = (((size)+(ALIGNMENT-1)) & ~0xf);

    if ((long) (ptr = mem_sbrk(esize)) == -1) {
        return NULL;
    }
    
    // Citation: csapp textbook;
    // Header and footer of the new chunk of memory from heap extension
    write_no_tag(header_ptr(ptr), set_word(esize, 0));  
    write_no_tag(footer_ptr(ptr), set_word(esize, 0));    
    // Next block should have size 0 and allocated bit=1 (epilogue block header)  
    write_no_tag(header_ptr(next_blockptr(ptr)), set_word(0, 1));

    // Insert the new block in the appropriate seg list
    node_insert(ptr, esize);

    // Check for coalescing
    return block_coalescing(ptr);
}

// Helper function: Insertion of node
static void node_insert(void *ptr, size_t size)
{
    int lst = 0;
    char *find_ptr = ptr;
    char *insert_ptr = NULL;
    
    // Choose the seg list
    while ((lst < SEGLIST_SIZE - 1) && (size > 1)){
        size = size>>1;
        lst++;
    }
    
    // Continue asc. ordered search 
    find_ptr = seg_freelist[lst];
    while ((find_ptr != NULL) && (size > fetch_size(header_ptr(find_ptr)))){
        insert_ptr = find_ptr;
        find_ptr = get_pred(find_ptr);
    }
    
    // Set predecessor and successor
    if (find_ptr != NULL) {
        if (insert_ptr != NULL){
            // case 1: find pointer and insert pointer is not NULL 
            set_pointer(get_pred_ptr(ptr), find_ptr);
            set_pointer(get_succ_ptr(ptr), insert_ptr);
            set_pointer(get_pred_ptr(insert_ptr), ptr);
            set_pointer(get_succ_ptr(find_ptr), ptr);
        } 
        else {
            //case 2: search pointer is not NULL and insert pointer is NULL
            set_pointer(get_pred_ptr(ptr), find_ptr);
            set_pointer(get_succ_ptr(ptr), NULL);
            set_pointer(get_succ_ptr(find_ptr), ptr);
            seg_freelist[lst] = ptr;
        }
    }
    else {  
        if (insert_ptr != NULL) {
            //case 3: search pointer NULL and insert pointer is not NULL
            set_pointer(get_pred_ptr(ptr), NULL);
            set_pointer(get_succ_ptr(ptr), insert_ptr);
            set_pointer(get_pred_ptr(insert_ptr), ptr);
        } 
        else {
            //case 4: search pointer is NULL and insert pointer is NULL
            set_pointer(get_pred_ptr(ptr), NULL);
            set_pointer(get_succ_ptr(ptr), NULL);
            seg_freelist[lst] = ptr;
        }
    }
}

// Helper function: Deletion of node
static void node_del(void *ptr)
{
    int lst = 0;
    size_t size = fetch_size(header_ptr(ptr));
    
    // choose the seg list 
    while ((lst < SEGLIST_SIZE - 1) && (size > 1)) {
        size >>= 1;
        lst++;
    }
    
    if (get_pred(ptr) != NULL) {
        //case 1: pred of ptr is not NULL and succ is not NULL
        if (get_succ(ptr) != NULL) {
            set_pointer(get_succ_ptr(get_pred(ptr)), get_succ(ptr));
            set_pointer(get_pred_ptr(get_succ(ptr)), get_pred(ptr));
        } else {
            //case 2: pred of ptr is not NULL and succ is NULL
            set_pointer(get_succ_ptr(get_pred(ptr)), NULL);
            seg_freelist[lst] = get_pred(ptr);
        }
    } else {
        //case 3: pred of ptr is NULL and succ is not NULL
        if (get_succ(ptr) != NULL) {
            set_pointer(get_pred_ptr(get_succ(ptr)), NULL);
        } else {
            // case 4: pred and succ of ptr is NULL (only block in seg list of the specific size class)
            seg_freelist[lst] = NULL;
        }
    }
}

// Helper function: Merge free blocks - the boundary tags 
static void *block_coalescing(void *ptr)
{
    // Citation: csapp textbook;
    size_t prev_alloc = fetch_alloc(header_ptr(prev_blockptr(ptr)));
    size_t next_alloc = fetch_alloc(header_ptr(next_blockptr(ptr)));
    size_t size = fetch_size(header_ptr(ptr));   
  
    // check reallocation tag of previous block, if 1, do not block_coalescing
    if (read_tag(header_ptr(prev_blockptr(ptr)))){
        prev_alloc = 1;
    }
    
    // Citation: csapp textbook;
    if (prev_alloc==1 && next_alloc==1){                        
        // previous and next blocks occupied, nothing to block_coalescing
        return ptr;
    } 
    else if (prev_alloc==1 && next_alloc==0) {                   
        // previous block occupied, next block free
        node_del(ptr);
        node_del(next_blockptr(ptr));
        size += fetch_size(header_ptr(next_blockptr(ptr)));
        write_word(header_ptr(ptr), set_word(size, 0));
        write_word(footer_ptr(ptr), set_word(size, 0));
    }
    else if (prev_alloc==0 && next_alloc==1) {
        // previous block free, next block occupied  
        node_del(ptr);
        node_del(prev_blockptr(ptr));
        size += fetch_size(header_ptr(prev_blockptr(ptr)));
        write_word(footer_ptr(ptr), set_word(size, 0));
        write_word(header_ptr(prev_blockptr(ptr)), set_word(size, 0));
        ptr = prev_blockptr(ptr);
    } 
    else {                                                
        // previous and next blocks free
        node_del(ptr);
        node_del(prev_blockptr(ptr));
        node_del(next_blockptr(ptr));
        size += fetch_size(header_ptr(prev_blockptr(ptr))) + fetch_size(header_ptr(next_blockptr(ptr)));
        write_word(header_ptr(prev_blockptr(ptr)), set_word(size, 0));
        write_word(footer_ptr(next_blockptr(ptr)), set_word(size, 0));
        ptr = prev_blockptr(ptr);
    }
    
    // Insert in appropriate seg list
    node_insert(ptr, size);
    
    return ptr;
}

// Helper function: Place block of adj_size bytes - split free blocks
static void *insert_block(void *ptr, size_t adj_size)
{
    size_t tot_size = fetch_size(header_ptr(ptr));
    size_t rem_size = tot_size - adj_size;
    
    node_del(ptr);
    
    // Citation: csapp textbook; 
    if (rem_size < DOUBLESIZE*2) { 
        // no splitting of block
        write_word(header_ptr(ptr), set_word(tot_size, 1)); 
        write_word(footer_ptr(ptr), set_word(tot_size, 1)); 
    }    
    else if (adj_size >= 100) {
        // splitting of block
        write_word(header_ptr(ptr), set_word(rem_size, 0));
        write_word(footer_ptr(ptr), set_word(rem_size, 0));
        write_no_tag(header_ptr(next_blockptr(ptr)), set_word(adj_size, 1));
        write_no_tag(footer_ptr(next_blockptr(ptr)), set_word(adj_size, 1));
        node_insert(ptr, rem_size);
        return next_blockptr(ptr);
    }
    else {
        write_word(header_ptr(ptr), set_word(adj_size, 1)); 
        write_word(footer_ptr(ptr), set_word(adj_size, 1));
        write_no_tag(header_ptr(next_blockptr(ptr)), set_word(rem_size, 0)); 
        write_no_tag(footer_ptr(next_blockptr(ptr)), set_word(rem_size, 0)); 
        node_insert(next_blockptr(ptr), rem_size);
    }

    return ptr;
}
// End-of HELPER Functions

////
//// Main Functions ////
////
/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    // allocate memory
    if ((long)(heap_ptr = mem_sbrk(4*WORDSIZE)) == -1){
        return false;
    }
    
    // Initialize seg free lists
    for (int indx = 0; indx < SEGLIST_SIZE; indx++) {
        seg_freelist[indx] = NULL;
    }
    
    // citation: csapp textbook;   
    write_no_tag(heap_ptr, 0); // padding
    // start of heap mem block header (prologue)                         
    write_no_tag(heap_ptr + (1 * WORDSIZE), set_word(DOUBLESIZE, 1));
    // prologue footer
    write_no_tag(heap_ptr + (2 * WORDSIZE), set_word(DOUBLESIZE, 1));
    // last block of heap header(epilogue)
    write_no_tag(heap_ptr + (3 * WORDSIZE), set_word(0, 1));
    
    // Extend heap, when mem_sbrk failed to provide memory
    size_t size = INITIALCHUNK;
    if (heap_extension(size) == NULL) 
        return false;

    mm_checkheap(__LINE__);
    return true;  // Initialization successful
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    size_t adj_size;
    size_t extending_size;
    void *ptr;
    
    // Ignore request
    if (size == 0)
        return NULL;
    
    // Citation: csapp textbook; 
/*  if (size <= DOUBLESIZE)
        adj_size = 2*DOUBLESIZE;
    else 
        adj_size = ( ((size + DOUBLESIZE)+(ALIGNMENT-1)) & ~0xf);     
*/
    // Adjust block size  
//*    adj_size = align(size+DOUBLESIZE);
    adj_size = (((size+DOUBLESIZE)+(ALIGNMENT-1)) & ~0xf);

    size_t find_size = adj_size;
    
    // search for free block in seg list 
    for (int idx=0; (idx < SEGLIST_SIZE); idx++) {
        if ((idx == SEGLIST_SIZE - 1) || ((find_size <= 1) && (seg_freelist[idx] != NULL))) {
            ptr = seg_freelist[idx];
            // don't want blocks of inappropriate size or the blocks with reallocation bit=1
            while ((ptr != NULL) && ((adj_size > fetch_size(header_ptr(ptr))) || (read_tag(header_ptr(ptr))))) {
                ptr = get_pred(ptr);
            }
            if (ptr != NULL)
                break;
        }       
        find_size >>= 1;
    }
    
    // need to extend heap if free block not found
    if (ptr == NULL) {
        // Citation: csapp textbook; 
        //extending_size = maximum(adj_size, CHUNK);
        extending_size = adj_size;
        if ((ptr = heap_extension(extending_size)) == NULL)
            return NULL;
    }
    
    // need to place the block, and then split if larger than required block was allocated
    ptr = insert_block(ptr, adj_size);
    
    mm_checkheap(__LINE__);
    return (char *) ptr;
}

/*
 * free
 */
void free(void *ptr){

    /* IMPLEMENT THIS */
    if (ptr == NULL){
        return;
    }

    // get size of block pointed to by ptr
    size_t size = fetch_size(header_ptr(ptr));
    
    del_realloc_tag(header_ptr(next_blockptr(ptr)));

    // changing the allocation bit of the header and footer
    write_word(header_ptr(ptr), set_word(size, 0));
    write_word(footer_ptr(ptr), set_word(size, 0));
    
    node_insert(ptr, size);
    block_coalescing(ptr);
    
    mm_checkheap(__LINE__);
    return;
}

/*
 * realloc
 */
void *realloc(void *oldptr, size_t size)
{
    /* IMPLEMENT THIS */
    // This function changes the size of the memory block 
    
    if (size == 0){
        free(oldptr);
        return NULL;
    }

    if (oldptr == NULL){  
        return malloc(size);
    }
   
    // Allocate memory of the new size using malloc
    char *newptr = (char *) malloc(size);
    if (newptr == NULL) {
        return NULL; //returns NULL if malloc fails
    }
    
    // Copy data from old location to new location
    //size_t cpy_size = minimum(size, fetch_size(header_ptr(oldptr)) - WORDSIZE);
    size_t cpy_size = size;
    memcpy(newptr, oldptr, cpy_size);        
    
    free(oldptr);

    mm_checkheap(__LINE__);
    
    return newptr;
}


/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
    #ifdef DEBUG
    /* Write code to check heap invariants here */
    /* IMPLEMENT THIS */
  
    /* Heap checker function performs a scan on the heap invariants and consistency. 
    * checks if the pointer points to the First byte of heap 
    * checks the correctness of the first-block's Header and Footer in heap
    * checks the size & allocations of all the blocks 
    * checks if the block pointer lies within heap
    * checks if the block pointers are properly aligned.
    * checks if the block pointer is reached end-of heap 
    * checks whether the header and footer are different
    * checks the correctness of the Epilogue's header info.
    */

    if (lineno <= 0) 
        return false;
    dbg_printf("\n ************* Line number: %d  ***************\n" , lineno);
    
    char *start_blockptr = heap_ptr + DOUBLESIZE;
    char *block_ptr;
    size_t hsize, halloc; 
    size_t fsize, falloc;   

    // [Unit-test:1] Check the correctness of the First-block's Header in heap
    hsize = fetch_size(header_ptr(start_blockptr) );
    halloc = fetch_alloc(header_ptr(start_blockptr) ); 
    if (hsize != DOUBLESIZE || ( !halloc ) ) {
        dbg_printf("Heap start-block Header-data is incorrect \n");
        return false;
    }
    
    // [Unit-test:2] Check the correctness of the First-block's Footer in heap
    fsize = fetch_size(footer_ptr(start_blockptr) );
    falloc = fetch_alloc(footer_ptr(start_blockptr) ); 
    if (fsize != DOUBLESIZE || ( !falloc ) ) {
        dbg_printf("Heap start-block Footer-data is incorrect \n");
        return false;
    }

    // [Unit-test:3] Check if pointer points to the First byte of heap 
    if ((heap_ptr) != mem_heap_lo())
        dbg_printf ("(Start location of heap)"); 

    // [Unit-test:4] Check size & allocations of all the blocks that lie within Heap and that are Aligned.
    for (block_ptr = next_blockptr(start_blockptr); fetch_size(header_ptr(block_ptr)) > 0; block_ptr = next_blockptr(block_ptr)) {   

        hsize = fetch_size(header_ptr(block_ptr));
        halloc = fetch_alloc(header_ptr(block_ptr)); 
        fsize = fetch_size(footer_ptr(block_ptr));
        falloc = fetch_alloc(footer_ptr(block_ptr));    
        
        // Information of the block e.g. Block address, size and allocations.
        dbg_printf("Block address is: %p\n", block_ptr);
        dbg_printf("Header and Footer size is: %zu, fsize = %zu\n", hsize, fsize);
        dbg_printf("Header and Footer alloc is: %zu, falloc = %zu\n", halloc, falloc);

        // [Unit-test:5] Check if block pointer lies within heap
        if (!in_heap(block_ptr)) {
              dbg_printf("Block pointer lies outside heap\n");
            return false;  
        }
        
        // [Unit-test:6] Check if block pointer is properly aligned
        if (!aligned(block_ptr)) {
              dbg_printf("Block pointer is not aligned\n");
            return false;  
        }

        // [Unit-test:7] Check if the block is at end-of heap 
        if (hsize == 0) { 
            dbg_printf("(End-of heap is reached %p)\n", block_ptr);
            return false;  
        }

        // [Unit-test:8] Check if the header and footer are different
        if ((header_ptr(block_ptr)) == (footer_ptr(block_ptr))) {
            dbg_printf("Footer is the same as the Header)");
            return false;  
        }
          
    // [Unit-test:9] Check the epilogue's Header info.
    hsize = fetch_size(header_ptr(block_ptr) );
    halloc = fetch_alloc(header_ptr(block_ptr) ); 
    if (hsize != 0 || ( !halloc ) ) {
        dbg_printf("Last-block header is incorrect \n");
        return false;
    }
      
  } //end-of For loop    

    #endif /* DEBUG */
    
    return true;
}
// End-of checkheap function
