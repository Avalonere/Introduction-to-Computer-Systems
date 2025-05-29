/*
 * Implementation with segregated free list and first-fit policy
 */
#include <stdio.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
        /* Team name */
        "Segmentation Fault",
        /* First member's full name */
        "",
        /* First member's email address */
        "",
        /* Second member's full name (leave blank if none) */
        "",
        /* Second member's email address (leave blank if none) */
        ""
};

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define CLASSNUM    20      /* Number of classes in the segregated linked list */ //line:vm:mm:endconst

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and an allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp

/* Given block ptr bp, compute address of predecessor and successor blocks in the linked list */
#define GET_PRED(bp) ((unsigned int *)GET(bp))                       //line:vm:mm:getpred
#define GET_SUCC(bp) ((unsigned int *)(GET((unsigned int *)bp + 1))) //line:vm:mm:getsucc

/* Given index, compute address of the corresponding segregated linked list */
#define GET_LIST(index) ((unsigned int *)(GET(heap_listp + WSIZE * index))) //line:vm:mm:getlist
/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);

static int locate(size_t size);

static void push(void *bp);

static void delete(void *bp);

static void place(void *bp, size_t asize);

static void *find_fit(size_t asize);

static void *coalesce(void *bp);

static void printblock(void *bp);

static void checkheap(int verbose);

static void checkblock(void *bp);

static void printlist(void);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk((4 + CLASSNUM) * WSIZE)) == (void *) -1) //line:vm:mm:begininit
        return -1;
    for (int i = 0; i < CLASSNUM; i++)
    {
        PUT(heap_listp + i * WSIZE, 0);
    }
    PUT(heap_listp + CLASSNUM * WSIZE, 0);                      /* Alignment padding */
    PUT(heap_listp + ((1 + CLASSNUM) * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + ((2 + CLASSNUM) * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + ((3 + CLASSNUM) * WSIZE), PACK(0, 1));     /* Epilogue header */ //line:vm:mm:endinit
    /* $end mminit */

    /* $begin mminit */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* $end mmmalloc */
    if (heap_listp == 0)
    {
        mm_init();
    }
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                            //line:vm:mm:sizeadjust1
        asize = 2 * DSIZE;                                        //line:vm:mm:sizeadjust2
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); //line:vm:mm:sizeadjust3

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {                                                             //line:vm:mm:findfitcall
        place(bp, asize);                                         //line:vm:mm:findfitplace
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);               //line:vm:mm:growheap1
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;                                  //line:vm:mm:growheap2
    place(bp, asize);                                 //line:vm:mm:growheap3
    return bp;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    /* $end mmfree */
    if (bp == 0)
        return;

    /* $begin mmfree */
    size_t size = GET_SIZE(HDRP(bp));
    /* $end mmfree */
    if (heap_listp == 0)
    {
        mm_init();
    }
    /* $begin mmfree */

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* $end mmfree */
/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
/* $begin mmfree */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1 */
    if (prev_alloc && next_alloc)
    {
        push(bp);
        return bp;
    }

    /* Case 2 */
    else if (prev_alloc && !next_alloc)
    {
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    /* Case 3 */
    else if (!prev_alloc && next_alloc)
    {
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* Case 4 */
    else
    {
        delete(NEXT_BLKP(bp));
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* $end mmfree */

    /* $begin mmfree */
    push(bp);
    return bp;
}
/* $end mmfree */

/*
 * mm_realloc - Straightforward implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if (size == 0)
    {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if (!newptr)
    {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * mm_checkheap - Check the heap for correctness
 */
void mm_checkheap(int verbose)
{
    printlist();
    checkheap(verbose);
}

/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; //line:vm:mm:beginextend
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;                                        //line:vm:mm:endextend

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   //line:vm:mm:freeblockhdr
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   //line:vm:mm:freeblockftr
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ //line:vm:mm:newepihdr

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                            //line:vm:mm:returnblock
}
/* $end mmextendheap */

/*
 * locate - Find a suitable class in the segregated linked list
 */
static int locate(size_t size)
{
    int i = 4;
    for (; i <= 22; i++)
    {
        if (size <= (1 << i))
            return i - 4;
    }
    return i - 4;
}

/*
 * push - Insert the block into the segregated linked list
 */
static void push(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = locate(size);

    /* Case 1: Empty list */
    if (GET_LIST(index) == NULL)
    {
        PUT(heap_listp + WSIZE * index, (unsigned int) bp); /* bp as head */
        PUT(bp, 0);                                         /* No predecessor for bp */
        PUT((unsigned int *) bp + 1, 0);                    /* No successor for bp */
    }

    /* Case 2: Already existent list, add to the head */
    else
    {
        PUT((unsigned int *) bp + 1, (unsigned int) GET_LIST(index)); /* Original head as bp's successor */
        PUT(GET_LIST(index), (unsigned int) bp);                      /* bp as the original head's predecessor */
        PUT(bp, 0);                                                   /* No predecessor for bp */
        PUT(heap_listp + WSIZE * index, (unsigned int) bp);           /* bp as new head */
    }
}

/*
 * delete - Delete the block from the segregated linked list
 */
static void delete(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    int index = locate(size);

    /* Case 1: Only bp in the list */
    if (GET_PRED(bp) == NULL && GET_SUCC(bp) == NULL)
    {
        PUT(heap_listp + WSIZE * index, 0); /* Set head to null */
    }

    /* Case 2: bp as the last one */
    else if (GET_PRED(bp) != NULL && GET_SUCC(bp) == NULL)
    {
        PUT(GET_PRED(bp) + 1, 0); /* Set the successor of bp's predecessor to null */
    }

    /* Case 3: bp as the first one */
    else if (GET_SUCC(bp) != NULL && GET_PRED(bp) == NULL)
    {
        PUT(heap_listp + WSIZE * index, (unsigned int) GET_SUCC(bp)); /* Change head to bp's successor */
        PUT(GET_SUCC(bp), 0); /* Set bp's successor to null */
    }

    /* Case 4: bp in the middle */
    else if (GET_SUCC(bp) != NULL && GET_PRED(bp) != NULL)
    {
        PUT(GET_PRED(bp) + 1, (unsigned int) GET_SUCC(bp)); /* Set bp's predecessor's successor to bp's successor */
        PUT(GET_SUCC(bp), (unsigned int) GET_PRED(bp)); /* Set bp's successor's predecessor to bp's predecessor */
    }
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));
    delete(bp);
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        push(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
    /* $end mmfirstfit */

    /* $begin mmfirstfit */
    /* First-fit locate */
    int index = locate(asize);
    unsigned int *bp;
    while (index < CLASSNUM)
    {
        bp = GET_LIST(index);
        /* First-fit */
        while (bp)
        {
            if (GET_SIZE(HDRP(bp)) >= asize)
            {
                return (void *) bp;
            }
            bp = GET_SUCC(bp);
        }
        /* Check a bigger class */
        index++;
    }
    return NULL; /* No fit */
}

/* $end mmfirstfit */

/*
 * printblock - Print out the information of a block
 */
static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0)
    {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%zd:%c] footer: [%zd:%c]\n", bp,
           hsize, (halloc ? 'a' : 'f'),
           fsize, (falloc ? 'a' : 'f'));
}

/*
 * checkblock - Check the legitimacy of a block
 */
static void checkblock(void *bp)
{
    if ((size_t) bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
 * checkheap - Minimal check of the heap for consistency
 */
static void checkheap(int verbose)
{
    char *bp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp + CLASSNUM * WSIZE);

    if ((GET_SIZE(HDRP(heap_listp + CLASSNUM * WSIZE)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp + CLASSNUM * WSIZE)))
        printf("Bad prologue header\n");
    checkblock(heap_listp + CLASSNUM * WSIZE);

    for (bp = heap_listp + CLASSNUM * WSIZE; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

/*
 * checklist - Print out the segregated linked list
 */
static void printlist(void)
{
    for (int i = 0; i < CLASSNUM; ++i)
    {
        printf("%p:%p\n", heap_listp + WSIZE * i, GET_LIST(i));
    }
}
