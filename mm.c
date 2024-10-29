/*
 * mm.c
 *
 * Name 1: [Roger Carter]
 * PSU ID 1: [rjc6361]
 * 
 * Name 2: Andrew Kim
 * PSU ID 2: apk5726
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * Also, read malloclab.pdf carefully and in its entirety before beginning.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
static void* heap_pointer;
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
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16
#define CHUNKSIZE (1 << 12)
#define WORDSIZE 8

static bool in_heap(const void* p);
static bool aligned(const void* p);

static void *segregated_list[16];

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x + ALIGNMENT - 1) / ALIGNMENT);
}

/* beginning of helper functions */

static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

// Combines a size and an allocate bit and returns a value that can be stored in a header or footer
static size_t pack(size_t size, size_t allocation) {
    return (size | allocation); // 0 if not allocated, 1 if allocated
}

// Reads and returns the word referenced by pointer
static size_t get(char* ptr) {
    return (* (size_t*)(ptr));
}

// Stores value to the pointer's payload
static void put(char* ptr, size_t value) {
    (* (size_t*)(ptr)) = value;
}

// returns the size of a block from either header or footer of the pointer
static size_t getSize(char* ptr) {
    // bitwise AND to measure the 29 high-order bits of the block size
    return get(ptr) & ~0x7; 
}

// returns the allocation bit (LSB) from the pointer
static size_t getAllocation(char* ptr) {
    return get(ptr) & 0x1;
}

// returns the header/footer address of the pointer heap block 
// CSAPS figure 9.35 - header is a one word sized inner block storing allocation information. 
static char* getHeader(char* ptr) {
    // In 64-bits system, a word = wordSize = 8 bytes
    return (ptr - WORDSIZE); 
}
static char* getFooter(char* ptr) {
    // size from header - ALIGNMENT(double words) size to get the size of the heap block without header and footer
    return (ptr + getSize(getHeader(ptr)) - ALIGNMENT);
}

// returns the pointer's next/previous memory heap block's address
static char* getNextBlock(char* ptr) {
    return (ptr + getSize(getHeader(ptr)));
}
static char* getPrevBlock(char* ptr) {
    return (ptr - getSize(ptr - ALIGNMENT));
}

// returns pointer's next/previous address
static char* getNextAddress(char* ptr) {
    return (ptr + WORDSIZE);
}
static char* getPrevAddress(char* ptr) {
    return (ptr);
}

// returns pointer's next/previous free block address
static char* getNextFree(char* ptr){
    return ((char*) get(ptr + WORDSIZE));
}
static char* getPrevFree(char* ptr){
    return ((char*) get(ptr));
}

// find an appropriate index within the seg list for a 'size' sized blk pointer
static int list_index(size_t size){
    int i = 0;
    
    // each index holds 2^n sized free blks
    // a smallest blk would have at least 2 double-words: header and footer
    while (size > (4 * WORDSIZE)) {
        size >>= 1;
        i++;
    }
  
    // if the blk size was too big (bigger than 2^(5+15)), group them all together in the index 15
    if (i > 14) {
        return 15;
    }
    return i;
}

// insert the free blk pointer to the segregated list
static void insert_segregated_list(char * ptr, size_t size) {
    // printf("%ld\n", size);
    int i = list_index(size);
    char *blk_size = segregated_list[i];
    char *list_blk = NULL;

    // if (blk_size != NULL) {
    //     printf("%ld size and %ld getSize\n", size, getSize(getHeader(blk_size)));
    // }

    // search through the segregated list until we find the best fitting blk size
    if (i == 8) { // searching from 2^8 or smaller --> reallistically, anything bigger than 2^8 could be put together
        while (blk_size != NULL && size < getSize(getHeader(blk_size))) {
            list_blk = blk_size;
            blk_size = getPrevFree(blk_size);
            // if (blk_size != NULL) {
            //     printf("loop: %d list_blk and %d blk_size\n", *list_blk, *blk_size);
            // }
        }
    }

    // if there was no small enough blk in the segregated list
    if (blk_size == NULL) {
        // if the list is empty - no 'ptr' sized blk is registered in the list yet
        if (list_blk == NULL) {
            // insert the ptr blk as the first blk of the list
            put(getPrevAddress(ptr), (size_t)NULL);
            put(getNextAddress(ptr), (size_t)NULL);
            segregated_list[i] = ptr;
        } else {
            // insert the ptr blk at the end of the list
            put(getPrevAddress(ptr), (size_t)NULL);
            put(getNextAddress(ptr), (size_t)list_blk);
            put(getPrevAddress(list_blk), (size_t)ptr);
        }
    } 
    // else - there is an appropriate size for the ptr blk in the list
    else {
        // if the list is empty
        if (list_blk == NULL) {
            // insert the ptr blk as the first blk of the list
            put(getPrevAddress(ptr), (size_t)blk_size);
            put(getNextAddress(blk_size), (size_t)ptr);
            put(getNextAddress(ptr), (size_t)NULL);

            // register the ptr blk to the list
            segregated_list[i] = ptr;
        } else {
            // insert the ptr blk in between two sizes of the list
            put(getPrevAddress(ptr), (size_t)blk_size);
            put(getNextAddress(blk_size), (size_t)ptr);
            put(getNextAddress(ptr), (size_t)list_blk);
            put(getPrevAddress(list_blk), (size_t)ptr);
        }
    }
    return;
}

// delete the free blk pointer from the segregated list
static void delete_segregarted_list(char * ptr) {
    size_t size = getSize(getHeader(ptr));
    int i = list_index(size);

    // if the ptr blk is the first blk of the size class's list
    if (getPrevFree(ptr) == NULL) {
        // ptr blk was the only blk of the size class's list
        if (getNextFree(ptr) == NULL) { 
            segregated_list[i] = NULL; // could nullify the whole index of the list
        }
        // else - set the next blk of the size class's previous blk address (ptr blk) to be NULL since it is being removed
        else {
            put(getPrevAddress(getNextFree(ptr)), (size_t)NULL);
        }
    }
    // else - if not the first blk case
    else {
        // if the ptr blk was the last of the size class's list
        if (getNextFree(ptr) == NULL) {
            put(getNextAddress(getPrevFree(ptr)), (size_t)NULL);
            segregated_list[i] = getPrevFree(ptr); // now the last of the size class's list is the one previous of the ptr blk
        }
        // else - ptr blk was in between other free blks within the size class's list 
        else {
            put(getPrevAddress(getNextFree(ptr)), (size_t)getPrevFree(ptr));
            put(getNextAddress(getPrevFree(ptr)), (size_t)getNextFree(ptr));
        }
    }
}

// CSAPP - coalescing freed block's adjeacent memory blocks
static void* coalesce(void* ptr) {

    size_t previousAllocation = getAllocation(getHeader(getPrevBlock(ptr)));
    size_t nextAllocation = getAllocation(getHeader(getNextBlock(ptr)));
    size_t size = getSize(getHeader(ptr));

    // case1 - both previous and next blocks are allocated
    if (previousAllocation && nextAllocation) {
        return ptr;
    } 
    // case2 - only previous block is allocated
    else if (previousAllocation && !nextAllocation) {
        delete_segregarted_list(ptr); // the ptr blk itself
        delete_segregarted_list(getNextBlock(ptr)); // the unallocated free blk that is to be linked with the ptr blk
        size = size + getSize(getHeader(getNextBlock(ptr)));
        put(getHeader(ptr), pack(size, 0));
        put(getFooter(ptr), pack(size, 0));
    }
    // case3 - only next block is allocated
    else if (!previousAllocation && nextAllocation) {
        delete_segregarted_list(ptr); // the ptr blk itself
        delete_segregarted_list(getPrevBlock(ptr)); // the unallocated free blk that is to be linked with the ptr blk
        size = size + getSize(getHeader(getPrevBlock(ptr)));
        put(getFooter(ptr), pack(size, 0));
        put(getHeader(getPrevBlock(ptr)), pack(size, 0));
        ptr = getPrevBlock(ptr);
    }
    // case4 - none of the previous or next blocks are allocated
    else {
        delete_segregarted_list(ptr); // the ptr blk itself
        delete_segregarted_list(getNextBlock(ptr)); // the unallocated free blk that is to be linked with the ptr blk
        delete_segregarted_list(getPrevBlock(ptr)); // the unallocated free blk that is to be linked with the ptr blk
        size = size + getSize(getHeader(getPrevBlock(ptr))) + getSize(getHeader(getNextBlock(ptr)));
        put(getHeader(getPrevBlock(ptr)), pack(size, 0));
        put(getFooter(getNextBlock(ptr)), pack(size, 0));
        ptr = getPrevBlock(ptr);
    }
    insert_segregated_list(ptr, size); // insert the coalesced free blk to the segregated list
    
    mm_checkheap(__LINE__);
    return ptr;
}

static void *extend_heap(size_t words)
{
    
    // We want to maintain our alignment, so we only allocate an even number here
    size_t size = align(words);
    char *bp= mem_sbrk(size);
    
    // if extension to rounded up size has failed
    if (bp == (void*)(-1)) {
        return NULL;
    }

    // Begin the header,footer, and the epilogue of our blocks
    put(getHeader(bp), pack(size, 0)); //header initialization
    put(getFooter(bp), pack(size, 0)); //foot initialization
    put(getHeader(getNextBlock(bp)), pack(0, 1)); //epilogue initialization

    //We insert this block at the end of our blockpointer, extending our heap.
    insert_segregated_list(bp,size);
    //If necessary, we'll have to coalesce to keep heap more efficient
    return coalesce(bp);

}

static void *place(void *bp, size_t asize) {
    size_t block_size = getSize(getHeader(bp));
    delete_segregarted_list(bp); // delete the free blk at ptr
  
    // If the remaining size after allocation is big enough for a new block
    if ((block_size - asize) >= (2 * ALIGNMENT)) {
        // Set the header/footer for the allocated block
        put(getHeader(bp), pack(asize, 1)); // Set allocated bit to 1
        put(getFooter(bp), pack(asize, 1)); // Set footer

        // Set header/footer for the free block
        put(getHeader(getNextBlock(bp)), pack(block_size - asize, 0)); // Set new free block header
        put(getFooter(getNextBlock(bp)), pack(block_size - asize, 0)); // Set new free block footer
        insert_segregated_list(getNextBlock(bp), (block_size - asize));

    } else {
        // Not enough space to split the block, allocate the entire block
        put(getHeader(bp), pack(block_size, 1)); // Set header
        put(getFooter(bp), pack(block_size, 1)); // Set footer
    }
    return bp;
}

// checks if a free pointer blk is inside the free seg list
static bool inSegList(char* bp) {
    for (int i = 0; i < 16; i++) {
        char* curr = segregated_list[i];
        if (bp == curr) {
            printf("arrived true\n");
            return true;
        }
    }
    printf("arrived false\n");
    return false;
}

/**
 * from CSAPP
 * prints the header and footer of the pointer blk, and if it is allocated or freed
 */
static void printblock(void *bp){
    size_t hsize, halloc, fsize, falloc;

    mm_checkheap(0);
    hsize = getSize(getHeader(bp));
    halloc = getAllocation(getHeader(bp));  
    fsize = getSize(getFooter(bp));
    falloc = getAllocation(getFooter(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void printSegList() {
    for (int i = 0; i < 16; i++) {
        if (segregated_list[i] == NULL) {
            printf("free blk %d: NULL\n", i);
        } else {
            printf("free blk %d: %p\n", i, segregated_list[i]);
        }
    }
}

/**
 * from CSAPP - altered
 * checks if the blk is aligned by double words
 * checks if the pointer blk's header/footer sizes match
 * checks if the blk is free, then if it is well coalesced
 */ 
static bool checkblock(char *bp) {
    bool factor = true;

    if ((size_t)bp % ALIGNMENT) {
        printf("Err: %p not aligned as a double-word\n", bp);
        factor = false;
    }
    if (get(getHeader(bp)) != get(getFooter(bp))) {
        printf("Err: the size of header/footer of the blk does not match\n");
        factor = false;
    }
    if (!getAllocation(getHeader(bp))) {
        if (!getAllocation(getHeader(getPrevBlock(bp))) || !getAllocation(getHeader(getNextBlock(bp)))) {
            printf("Err: free blk coalescing is not well done for this blk\n");
            factor = false;
        }
    }
    return factor;
}

/* end of helper functions */

/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    dbg_printf("arrived init\n");

    // if debugging, use the static heap_pointer variable instead
    #ifdef DEBUG

    //Sets first 16 positions of the segregated_list to NULL
    for (int i = 0; i < 16; i++) {
        segregated_list[i] = NULL;
    }

    // initializing an empty heap for 4 words
    heap_pointer = mem_sbrk(4 * WORDSIZE);
    if (heap_pointer == (void*)(-1)) {
        return false;
    }

    // put values in each word
    put(heap_pointer, 0); /* Alignment padding */
    put((heap_pointer + (1 * WORDSIZE)), pack(ALIGNMENT, 1)); /* Prologue header */
    put((heap_pointer + (2 * WORDSIZE)), pack(ALIGNMENT, 1)); /* Prologue footer */
    put((heap_pointer + (3 * WORDSIZE)), pack(0, 1)); /* Epilogue header */

    if (extend_heap(CHUNKSIZE/WORDSIZE) == NULL) { //Heap extension not working means that mem_sbrk had an issue, likely due to the size of the allocation, so we have to fail the init here.
        return false;
    }
    
    dbg_printf("finishing init\n");
    return true; //Need this so we can check through the heap
    
    // if not debugging, create a seperate static heap_pointer
    #else

    static char* heap_pointer;

    //Sets first 16 positions of the segregated_list to NULL
    for (int i = 0; i < 16; i++) {
        segregated_list[i] = NULL;
    }

    // initializing an empty heap for 4 words
    if ((heap_pointer = mem_sbrk(4 * WORDSIZE)) == (void*)(-1)) {
        return false;
    }

    // put values in each word
    put(heap_pointer, 0); /* Alignment padding */
    put((heap_pointer + (1 * WORDSIZE)), pack(ALIGNMENT, 1)); /* Prologue header */
    put((heap_pointer + (2 * WORDSIZE)), pack(ALIGNMENT, 1)); /* Prologue footer */
    put((heap_pointer + (3 * WORDSIZE)), pack(0, 1)); /* Epilogue header */

    if (extend_heap(CHUNKSIZE/WORDSIZE) == NULL) { //Heap extension not working means that mem_sbrk had an issue, likely due to the size of the allocation, so we have to fail the init here.
        return false;
    }
    return true;
    #endif
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    dbg_printf("calling malloc with size: %zu\n", size);
    
    // from CSAPP
    size_t asize; // Adjusted block size 
    size_t extendsize; // Amount to extend heap if no fit 
    void *ptr = NULL;

    // Ignore spurious requests 
    if (size == 0)
        return NULL;

    // Adjust block size to include overhead and alignment reqs. 
    if (size <= ALIGNMENT) {
        asize = 2 * ALIGNMENT;
    } else {
        asize = align(size + ALIGNMENT);
    }

    int index = list_index(asize);
    // Search the free list for a fit 
    for (int i = index; i < 16; i++) {
        ptr = segregated_list[i];
        while (ptr != NULL) {
            if (getSize(getHeader(ptr)) >= asize) { 
                place(ptr, asize);
                return ptr;
            }
            ptr = getPrevFree(ptr);
        }
    }

    // from CSAPP, we need to get more memory to place the block since no fit was found 
    //ptr being null here means there was no place found to fit the block
    if (ptr == NULL) {
        extendsize = asize;
        if ((ptr = extend_heap(extendsize)) == NULL) //extend the heap for the new placement.
         {
            return NULL;
        }
    }
    ptr = place(ptr, asize); //NOw that we have more memory, we can place the blck.
    
    dbg_printf("finished malloc\n");
    return ptr;
}

/*
 * free
 */
void free(void* ptr)
{
    dbg_printf("arrived free\n");

    // free does not perform on an empty pointer
    if (ptr == 0) {
        return; 
    }

    // get block size from pointer's header address
    size_t size = getSize(getHeader(ptr));

    // freeing - sets allocation to 0 in both header and footer
    put(getHeader(ptr), pack(size, 0));
    put(getFooter(ptr), pack(size, 0));
    insert_segregated_list(ptr, size);

    // coalescing
    coalesce(ptr);

    dbg_printf("finished free\n");
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    // dbg_printf("arrived realloc\n");
    
    // if new size is 0, free the memory instead
    if (size == 0) {
        free(oldptr);
        return 0;
    }
    
    // if the pointer did not exist before, perform malloc() instead
    if (oldptr == (void*)0) {
        return malloc(size);
    }

    // if none of the cases above, instantiate variables
    size_t oldSize = getSize(getHeader(oldptr)); /* size of the old pointer (from header) */
    size_t newSize; /* a new size of the pointer */
    char* newPtr = malloc(size);

    // align the new size based on its characteristic
    if (size <= ALIGNMENT) {
        newSize = 2 * ALIGNMENT;
    }
    else {
        newSize = align(size + ALIGNMENT);
    }

    // case1 - if the old pointer's size is as same as the new size, no need to perform furthur memory allocation
    if (oldSize == newSize) {
        return oldptr;
    }

    // case 2 - if the new size is smaller than the current size, use the same pointer address and update only its header and footer
    else if (oldSize > newSize) {
        size_t remainderSize = oldSize - newSize;

        // if the gap between the old size and the new size is large enough
        if (remainderSize > (2 * ALIGNMENT)) {
            
            // allocate the old pointer memory block
            put(getHeader(oldptr), pack(newSize, 1));
            put(getFooter(oldptr), pack(newSize, 1));
            
            // then deallocate the rest of the old block (cut down after the new size)
            put(getHeader(getNextBlock(oldptr)), pack(remainderSize, 0));
            put(getFooter(getNextBlock(oldptr)), pack(remainderSize, 0));
            insert_segregated_list(getNextBlock(oldptr), remainderSize);
        }
        // else if the gap is too tiny
        else {
            put(getHeader(oldptr), pack(oldSize, 1));
            put(getFooter(oldptr), pack(oldSize, 1));
        }
        return oldptr;
    }

    // case 3 - if the new size is bigger than the current size
    else {
        
        // allocate a new block with the new (bigger) size to move the old block size into
        newPtr = malloc(newSize);

        // if additionall malloc was not successful, kill the realloc process
        if (newPtr == NULL) {
            return NULL;
        }

        // copy the old pointer block's information to the new pointer block, then free the old block
        memcpy(newPtr, oldptr, oldSize - ALIGNMENT);
        free(oldptr);
        return newPtr;
    }

    // dbg_printf("finished realloc\n");
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
 * THE FOLLOWING CODE IS HEAVILY BASED OFF OF CSAPP'S OFFICIAL STUFF. I may have changed some lines to be more straightforward, so I actually know what I'm reading in the future.
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    // printf("header: %p\n", getHeader(heap_pointer));
    // printf("header size: %ld\n", getSize(getHeader(heap_pointer)));
    // printf("footer: %p\n", getFooter(heap_pointer));
    // printf("footer size: %ld\n", getSize(getFooter(heap_pointer)));
    if (lineno) {
        dbg_printf("Heap check called at line %d\n", lineno);
        printf("Heap: %p\n", heap_pointer);
    }
    
    // 1 - check if heap_pointer is NULL
    if (heap_pointer == NULL) {
        printf("heap is NULL\n");
        return false;
    }

    heap_pointer = mem_heap_lo() + ALIGNMENT;
    bool factor = true;
    // size_t size = 0;

    /**
     * 2 - validate the entire heap and individual blks in the heap
     * we check this with multiple processes
     */
    char* ptr;

    // 2.1 - validate that the beginning blk of the heap is a prologue blk
    if ((getSize(getHeader(heap_pointer)) != ALIGNMENT) || (!getAllocation(getHeader(heap_pointer)))) {
        printf("Err in prologue header\n");
        factor = false;
    }

    // 2.2 - loop thruough the entire heap by each blk and check each blk's status
    for (ptr = heap_pointer; getSize(getHeader(ptr)) > 0; ptr = getNextBlock(ptr)) {
        if (lineno) {
            printblock(ptr);
            printSegList();
        }

        // validate each blk
        factor = checkblock(ptr);
    } 
    
    // 2.3 - if looping is successfully done through the heap, it should print "EOL" 
    if (lineno) {
        printblock(ptr);
    }

    // 2.4 - assuming we have reached the epilogue address of the heap, validate the epilogue status
    if ((getSize(getHeader(ptr)) != 0) || !(getAllocation(getHeader(ptr)))) {
        printf("EPILOGUE HEADER ERROR\n");
        factor = false;
    }

    /**
     * 3 - check if the blks in the seg list are really free
     */
    // char* free_list = segregated_list;


    // If all checks pass, return success
    return factor;

#endif /* DEBUG */
    return true;
}
