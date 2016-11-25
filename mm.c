/*
    Name: Aayush Karki
    Andrew id : aayushka
*/
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

#define dbg_printline(s, l) printf("%s : line %d\n", s, l)


#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */


/****************************************************************************/

#define ALIGNMENT 8

#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


#define WSIZE       4    
#define DSIZE       8   
#define CHUNKSIZE   (240)  /*Initial heap size( bytes)*/
#define MIN_BLKsize    24  /*minimum size(24 bytes) of any allocated block*/

#define FB 0 /*free block tag*/
#define AL 1 /*allocated block tag*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, bit)  ((size) | (bit))

#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))


#define GET_SIZE(p)  (GET(p) & ~0x7)
#define IS_ALLOC(p)  (GET(p) & 0x1)  /*get allocation bit*/


 #define HDR(pp) ((char *)(pp) - WSIZE)
 #define FTR(bp) ((char *)bp + GET_SIZE(HDR(bp)) - DSIZE)

/*get physically neigbbouring blocks*/
 #define NEXTBLK(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
 #define PREVBLK(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*get predecessor and successor free blocks*/
#define PAREN(p)        ( *(char **) (p) )
#define CHILD(p)        (*(char **) (p + DSIZE))
/*store address to a free block pointer bp in a free block at p*/
#define STORE_PTR(p, bp)    ((p) = (bp) )

static char *heap_listp; 
static char *free_list;/* Doubly Linked list of free blocks*/

static void *epilogue /*points to the end of the epilogue header*/;



static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void makeNode(void *bp); 
static void removeNode(void *bp); 
static void *find_firstFit(size_t asize);
static void *find_bestFit(size_t asize);
static void *find_Fit(size_t asize);

/*
	Initial heap:
	....|prologue hdr 4/1| prologue ftr 4/1 | epilogue 0/1 | ...
						 ^ heap_listp


	Allocated block:
	| hdr = 4bytes | size>=16 bytes + padding |ftr = 4bytes |
				   ^bp

	Free block:
	|hdr = 4bytes | parent=8 bytes | child =8 bytes + paddding |ftr = 4bytes |
				  ^bp


*/


/*
* Adds bp(block pointer to a free block) to the free list.
* Adds bp to the beginning of free_list
* Each free block in the free_list are doubly linked
*/
static void makeNode(void *bp){

    PAREN(bp) = NULL;
    STORE_PTR(CHILD(bp) , free_list);
    
    if(free_list != NULL)
       STORE_PTR( PAREN(free_list), bp);

    STORE_PTR(free_list , bp);
}




/*
* Gets initial heap from the memory.
* Initializes the prologue and epilogue header
* Initizlizes the epilogue header
*/
int mm_init(void) 
{
    /*return -1 if unable to get heap space*/
    if ((heap_listp = mem_sbrk(2*DSIZE)) == NULL) 
        return -1;

    PUT(heap_listp, FB); /*Alignment padding*/

    PUT(heap_listp +   WSIZE, PACK(DSIZE, AL)); /*prologue header*/
    PUT(heap_listp + 2*WSIZE, PACK(DSIZE, AL)); /*prologue footer*/
    PUT(heap_listp + 3*WSIZE, PACK(0, AL)); /*epilogue header*/
 
    epilogue = heap_listp + 3*WSIZE; /*create the intial epilogue*/
    /*fix heap_listp to point to the start of prologue footer*/
    heap_listp = heap_listp + DSIZE;

    
    free_list = NULL; 

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;

    mm_checkheap(__LINE__);
    return 0; /*on success*/
}

/*
* Allocates a pointer to heap of size.
* The allocated block is the Max of aligned size and min block size
* Any extra space is treated as padding.
*/
void *malloc(size_t size) 
{
    if (size<=0) return NULL;

    size_t asize = MAX(ALIGN(size) + DSIZE, MIN_BLKsize);

    void *bp =find_Fit(asize);


    if (bp != NULL){
        place(bp, asize);
    }
    else {
        bp = extend_heap(MAX(asize, CHUNKSIZE)/WSIZE);
        if (bp == NULL) return NULL;
        place(bp, asize);
    }
   
    return bp;
} 

/* 
 * frees an allocated block pointed by ptr
 * coalesces the newly freed block
 */
void free (void *ptr) {
    if (ptr == NULL) return;

    PUT(HDR(ptr), PACK(GET_SIZE(HDR(ptr)) , FB) );
    PUT(FTR(ptr), PACK(GET_SIZE(FTR(ptr)), FB ) );
    coalesce(ptr);
    return;
}

/*
 * Increases or decreases the size of an allocated block.
 * If nsize is smaller than the current block size, it shrinks the
 * block size only if the new free space is big enough to hold a minimum
 * block. If new free space is large enough, then splits the block
 * and adds this new space to the free_list.
 * If nsize is larger than the current block size, given adjacent
 * block is free and large enough, it increases the block size and
 * thus returns the same pointer.
 * Else, it frees the old pointer, mallocs a new block and copies the old data
 * to new block and return a new pointer to this new block.
 */
void *realloc(void *oldptr, size_t nsize)
{
    
    if (nsize<=0){
        free(oldptr);
        return NULL;
    }
    if (oldptr == NULL) return malloc(nsize);

    size_t oldsize = (size_t)GET_SIZE(HDR(oldptr));
    size_t newsize = MAX(ALIGN(nsize)+DSIZE, MIN_BLKsize);

    if (newsize == oldsize) return oldptr;
    if (oldsize - newsize<=MIN_BLKsize) return oldptr;

    /*If newsize is smaller, split and return same pointer*/
    if(newsize < oldsize){
        PUT(HDR(oldptr), PACK(newsize, AL));
        PUT(FTR(oldptr), PACK(newsize, AL));
        PUT(HDR(NEXTBLK(oldptr)), PACK(oldsize-newsize, AL));
        free(NEXTBLK(oldptr));
        return oldptr;
    }


    void *nxt = NEXTBLK(oldptr);
    int nxtsixe = GET_SIZE(HDR( nxt ));
    /*If new block is larger, check if the old
    ptr has sufficiently large free block physically next
    to it*/
    if ((IS_ALLOC(HDR(nxt))==FB)
        && (oldsize + nxtsixe >= newsize + MIN_BLKsize)
        ){

        removeNode(NEXTBLK(oldptr));
        PUT(HDR(oldptr), PACK(newsize, AL));
        PUT(FTR(oldptr), PACK(newsize, AL));

        PUT(HDR(NEXTBLK(oldptr)), PACK(nxtsixe - (newsize-oldsize), FB));
        PUT(FTR(NEXTBLK(oldptr)), PACK(nxtsixe - (newsize-oldsize), FB));

        makeNode(NEXTBLK(oldptr));
        
        return oldptr;
    }


    void *newptr = (void *)malloc(nsize);
    if (newptr == NULL) return oldptr;

    /*copy old items to new address*/
    memcpy(newptr, oldptr, oldsize);
    free(oldptr);

    return newptr;
}

/*
 * Mallocs a usable block of size nmemb * size bytes.
 * Initializes this space with zeros.
*/
void *calloc (size_t nmemb, size_t size)
{
    size_t mallocSize = nmemb*size;
    void *ptr = malloc(mallocSize);
    if (ptr == NULL) return NULL;

    memset(ptr, 0, mallocSize);
    return ptr;
}

/* 
* Checks for inconsistency in the heap invariants.
* Inspects the prologues and the epilogue invariants.
* Inspects if information in header and footer is identical.
* Checks if phyically adjacent blocks are able to traverse
  between one another (both directions).
* Checks if any two free blocks in free_list are correctly doubly linked
 */
void mm_checkheap(int lineno) 
{
    if (GET_SIZE(heap_listp) != 8) dbg_printline("Epi footer size error", lineno);

    if (GET_SIZE(heap_listp - WSIZE) != 8) 
        dbg_printline("Epi header size error", lineno);

    if (IS_ALLOC(heap_listp) != 1) dbg_printline("Epi footer alloc error", lineno);

    if (IS_ALLOC(heap_listp - WSIZE) != 1) 
        dbg_printline("Epi header alloc error", lineno);

    if (GET_SIZE(HDR(epilogue)) != 0) 
        dbg_printline("epilogue header size mismatch", lineno);

    if (IS_ALLOC(HDR(epilogue)) != 1) 
        dbg_printline("epilogue header alloc mismatch", lineno);

    return;

}

/*
* Aks for more space for heap from the memory.
* Reinitizes the epilogue header.
*/
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t asize;

    /* Allocate an even number of words to maintain alignment */
    asize = words * WSIZE;
    
    asize = MAX(ALIGN(words*WSIZE), MIN_BLKsize);
    if ((bp = mem_sbrk(asize)) == (void *) -1) return NULL;

    PUT(HDR(bp), PACK(asize, FB));
    PUT(FTR(bp), PACK(asize, FB));
    PUT(HDR(NEXTBLK(bp)), PACK(0, AL));

    epilogue = NEXTBLK(bp);

    void* ptr = coalesce(bp);
    mm_checkheap(__LINE__);
    return ptr;
}

/* 
* changes a pointer to a free block into an allocated block
* of asize
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDR(bp));
    assert(IS_ALLOC(HDR(bp)) == 0);

    size_t newblock_size = asize;

    removeNode(bp);

    if (csize - newblock_size >= MIN_BLKsize){
        PUT(HDR(bp), PACK(newblock_size, AL));
        PUT(FTR(bp), PACK(newblock_size, AL));
        PUT(HDR(NEXTBLK(bp)), PACK(csize - newblock_size, FB));
        PUT(FTR(NEXTBLK(bp)), PACK(csize - newblock_size, FB));
        coalesce(NEXTBLK(bp));
    }
    else{
        PUT(HDR(bp), PACK(csize, AL));
        PUT(FTR(bp), PACK(csize, AL)); 
    }
}




/*
* Give a free block bp, if one or both physically adjacent blocks are free,
 it merges them into one and updates the header and footer information.
* Also removes any merged block from free list and adds newly coalesced
  block into the free_list.
*/
static void *coalesce(void *bp)
{
    size_t prev_alloc, next_alloc;

    prev_alloc = IS_ALLOC(HDR(PREVBLK(bp)));
    next_alloc = IS_ALLOC(HDR(NEXTBLK(bp)));
  
    size_t freesize=0;

    /*left and right blocks are both allocated*/
    if (prev_alloc && next_alloc){
        ;
    }
    /*left block allocated, right block is free*/
    else if (prev_alloc && !next_alloc) 
    {           
        freesize = GET_SIZE(HDR(bp))
                + GET_SIZE(HDR(NEXTBLK(bp)));
        removeNode(NEXTBLK(bp));
        PUT(HDR(bp), PACK(freesize, FB));
        PUT(FTR(bp), PACK(freesize, FB));
    }

    /*left block free, right block is allocated*/
    else if (!prev_alloc && next_alloc) 
    {       
        bp = PREVBLK(bp);
        freesize = GET_SIZE(HDR(bp))
                + GET_SIZE(HDR(NEXTBLK(bp)));
        removeNode(bp);
        PUT(HDR(bp), PACK(freesize, FB));
        PUT(FTR(bp), PACK(freesize, FB));
    }

    /*left and right blocks both are free.*/
    else if (!prev_alloc && !next_alloc) 
    {       
        freesize = GET_SIZE(HDR(bp))
                + GET_SIZE(HDR(PREVBLK(bp)))
                + GET_SIZE(HDR(NEXTBLK(bp)));

        removeNode(PREVBLK(bp));
        removeNode(NEXTBLK(bp));

        bp = PREVBLK(bp);
        PUT(HDR(bp), PACK(freesize, FB));
        PUT(FTR(bp), PACK(freesize, FB)); 
    }
    /*add the newly coalesced free block to the free_list*/
    makeNode(bp);
    
    return bp;
}


/*
* unlinks bp (a free block) from the free_list
* Doubly links the two free blocks that were previously
* doubly linked to bp.
*
*/
static void removeNode(void *bp)
{
    if (free_list==NULL) return;

    if (PAREN(bp) != NULL) {
       STORE_PTR( CHILD(PAREN(bp)) , CHILD(bp) );
    }
    else {
        STORE_PTR( free_list , CHILD(bp) );
    }

    if (CHILD(bp) != NULL) 
        STORE_PTR( PAREN(CHILD(bp)) , PAREN(bp) ) ;
}



/* 
 * Using best-fit method, returns a free block from the free_list
 * that is closest to the size we are looking for
 */
static void *find_bestFit(size_t asize)
{
    void *bp = free_list;
    unsigned int size, tsize ;
    void *tbp = NULL;
    tsize  = 0x7fffffff;

    while(bp !=NULL){
        size = GET_SIZE(HDR(bp));

        if ((unsigned int)asize <= size){
            assert(IS_ALLOC(HDR(bp)) == FB);
            
            if (size <=tsize) {
                tsize = size;
                tbp = bp;
            }
        }
        bp = CHILD(bp);

    }//while
    return tbp;
}


/* 
 * Using first-fit method, returns a free block from the free_list
 * that fits the requested (aligned) size.
 */
static void *find_firstFit(size_t asize)
{
    void *bp = free_list;
    unsigned int size ;


    while(bp !=NULL){
        size = GET_SIZE(HDR(bp));


        if ((unsigned int)asize <= size){
            assert(IS_ALLOC(HDR(bp)) == FB);
            

            return bp;
        }
        bp = CHILD(bp);
    }
    return NULL;
}


/* 
 * Returns a free block from the free_list
 * that fits the requested (aligned) size.
 */
static void *find_Fit(size_t asize){
    void *bp;
  
    bp = find_firstFit( asize);

    unsigned int size = ((int) asize);

    /*If first fit return very large block, do a best fit*/
    if ((bp !=NULL) && (20*size <= GET_SIZE(HDR(bp)) ) ){
        return find_bestFit(asize);
    }
    else{
      
        return bp;
    }

}

