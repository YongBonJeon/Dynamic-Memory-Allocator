/* 
 * Project Name : Dyanamic Memoty Allocator
 * Author : Yongjae Kim
 * developer : YongBon Jeon
 * term : 2022/05/31 ~ 2022/06/28
 *
 * mm.c - The fastest, least memory-efficient malloc package.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/ 
team_t team = {
	"20181683",
	/* First member's full name */
	"YongBon Joen",
	/* First member's email address */
	"bon0057@naver.com",
};

/* 기본 상수, 매크로  */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

/* 최댓값 함수 매크로 */
#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Double-word alignment이므로 header, footer에서 size의 오른쪽 3자리 비트는 사용되지 않음 */
/* size의 가장 오른쪽 비트를 allocated / free flag 로 사용 */
#define PACK(size, alloc)  ((size) | (alloc))

/* 주소 p에 해당하는 word를 읽거나 삼입하는 함수 매크로  */
#define GET(p)       (*(unsigned int*)(p))
#define PUT(p, val)  (*(unsigned int*)(p) = (val))

/* header, footer에서 block의 size, allocated bit을 반환하는 함수 매크로 */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* block pointer로 block의 header, footer의 주소를 반환하는 함수 매크로 */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* block pointer로 previous, next block의 주소를 반환하는 함수 매크로 */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Free list 상에서 next, previous block pointer를 반환하는 함수 매크로 */
#define NEXT_FREE_BLKP(bp) GET(bp)
#define PREV_FREE_BLKP(bp) GET((char *)(bp)+WSIZE)

/* Free list 에 next, previous block pointer를 설정하는 함수 매크로 */
#define SET_NEXT_FREE_BLKP(bp, next_block_ptr) PUT(bp, next_block_ptr)
#define SET_PREV_FREE_BLKP(bp, prev_block_ptr) PUT((char *)(bp)+WSIZE, prev_block_ptr) 


/* 전역 변수 */
static char *heap_listp;          /* Pointer to first prologue block */  
size_t segregated_lists = 10;     /* segregated free list 는 10가지 size class를 갖고 있음 */
static char **seg_listp;          /* segregated free list pointer */

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static int index_list(size_t size);
static void delete_list (void *bp);
static void insert_list (void *bp);
static void *find_fit(size_t asize);
static void *extend_heap(size_t words);
static void place(void* bp, size_t asize, bool extend);

/* Function prototypes for heap consistency checker routines: */
int mm_check();
static int checkfreeblock(void *bp);

/* 
 *  mm_init
 *	 - initialize the malloc package.
 */
int mm_init(void) 
{
	int i;

	/* Create the initial heap space for segregated free list */
	if ((seg_listp = mem_sbrk(segregated_lists * WSIZE)) == (void *)-1)
		return -1;

	/* Create the initial empty heap. */ 
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return -1;

	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header  */
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer  */
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);
    
	for (i = 0; i < segregated_lists; i++)
		seg_listp[i] = NULL;                /* segregated free list 초기화*/

	return 0; 
}

/*
 *	mm_malloc
 *	- Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize, false);	/* allocate */
		return bp;
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return NULL;
	place(bp, asize, true); /* allocate */
	
	/* Heap checker */
	/*if(mm_check() == 0){
		printf("Heap checker error\n");
	}*/

	return bp;
} 

/* 
 *	mm_free
 *	 - Free a block
 */
void mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));		/* 해제 요청 block의 size */
	PUT(HDRP(bp), PACK(size, 0));	/* header, footer 수정 */
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);				/* 가능하다면 coalesce */
}

/*
 *	mm_realloc
 *	 - Naive implementation of realloc 
 */
void *mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return NULL;
	}

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return NULL;

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return newptr; 
}

/*
 *	coalesce
 *	 - Boundary tag coalescing.  Return ptr to  coalesced block.
 */
static void *coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {				/* Case 1 */
		insert_list(bp);						/* current free block segregated list에 추가 */
		return bp;
	} else if (prev_alloc && !next_alloc) {     /* Case 2 */
		void *next = NEXT_BLKP(bp);
		delete_list(next);						/* next free block segregated list에 삭제 */ 
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		insert_list(bp);						/* coalesced block segregated list에 추가 */
	} else if (!prev_alloc && next_alloc) {     /* Case 3 */
		void *prev = PREV_BLKP(bp);
		delete_list(prev);						/* previous free block segregated list에 삭제*/
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		insert_list(bp);						/* coalesced block segregated list에 추가 */
	} else {                                    /* Case 4 */
		void *prev = PREV_BLKP(bp);
		void *next = NEXT_BLKP(bp);
		delete_list(prev);						/* previous free block segregated list에 삭제*/
		delete_list(next);						/* next free block segregated list에 삭제*/
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));;
		bp = PREV_BLKP(bp);
		insert_list(bp);						/* coalesced block segregated list에 추가 */
	}
	return bp;
}

/* 
 *	index_list
 *	 - Returns the segregated free list index.
 */
static int index_list(size_t size) {
    if(size <= 64)
		return 0;
	else if(size <= 128)
		return 1;
	else if(size <= 256)
		return 2;
	else if(size <= 512)
		return 3;
	else if(size <= 1024)
		return 4;
	else if(size <= 2048)
		return 5;
	else if(size <= 4096)
		return 6;
	else if(size <= 8192)
		return 7;	
	else if(size <= 16384)
		return 8;
	else
		return 9;
}

/*
 *	delete_list
 *	 - Delete this block from the segregated free list.
 */
static void delete_list (void *bp){
	int index = index_list(GET_SIZE(HDRP(bp))); /* size로 free list의 index 획득 */

	/* link next, previous block  */
    if (PREV_FREE_BLKP(bp) != NULL) 
		SET_NEXT_FREE_BLKP(PREV_FREE_BLKP(bp),NEXT_FREE_BLKP(bp));
    else 
		seg_listp[index] = NEXT_FREE_BLKP(bp); 
    if (NEXT_FREE_BLKP(bp) != NULL)
		SET_PREV_FREE_BLKP(NEXT_FREE_BLKP(bp), PREV_FREE_BLKP(bp));
    return;
}

/*
 *	insert_list
 *	 -  Insert block pointer bp to segregated free list.
 */
static void insert_list (void *bp){
    int index = index_list(GET_SIZE(HDRP(bp)));  /* size로 free list의 index 획득 */
    
	/* free list의 첫번째 free block으로 삽입 */
	SET_NEXT_FREE_BLKP(bp, seg_listp[index]);  
    SET_PREV_FREE_BLKP(bp, NULL); 
    
	if (seg_listp[index] != NULL)   
		SET_PREV_FREE_BLKP(seg_listp[index], bp);	 
    seg_listp[index] = bp; 

    return; 
}

/*
 *	find_fit
 *	 - Find a first fit for a block with asize bytes at segregated list.
 *   - Returns that block's address or NULL if no suitable block was found. 
 */
static void *find_fit(size_t asize) {

    size_t best_fit_size = 9999999;
    void *best_fit_block = NULL;
    int index = index_list(asize);
	void *cur_bp;
	size_t cur_bs;
	/* 할당하기에 충분한 크기의 block을 찾기 위해 free list 순회 */
	for (int i = index; i < segregated_lists; i++) {
           cur_bp = seg_listp[i];                      
           while (cur_bp) {									 
			   cur_bs = GET_SIZE(HDRP(cur_bp));	
			   if(asize <= cur_bs){			/* 할당 가능한가 */			
				   size_t fit_size = cur_bs;
				   if (fit_size < best_fit_size) { 
					   best_fit_size = fit_size;
					   best_fit_block = cur_bp; 
				   }
			   }
			   cur_bp  = NEXT_FREE_BLKP(cur_bp);
           }
           if(best_fit_block!= NULL)
			   return best_fit_block;	/* best(first) fit block return */
    }

    /* No fit was found. */
    return NULL;
}

/* 
 *	extend_heap
 *	 - Extend the heap with free block and return its block pointer.
 */
static void *extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return NULL;

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	return bp;
}

/* 
 *	place
 *	 - Place asize block in segregated explicit free list
 *	 - split that block if the remainder would be at least the minimum block 
 */
static void place(void* bp, size_t asize, bool extend)
{
    /* Get the current block size */
    size_t csize = GET_SIZE(HDRP(bp));

    if (extend == true) {						/* extend heap으로 생성된 heap space */
		if ((csize - asize) >= (2 * DSIZE)){	/* 할당하고 남은 블록이 분할이 가능한가 */
			PUT(HDRP(bp), PACK(asize, 1));
			PUT(FTRP(bp), PACK(asize, 1));
			void *new = NEXT_BLKP(bp);			/* 분할 */
			PUT(HDRP(new), PACK(csize-asize, 0));
			PUT(FTRP(new), PACK(csize-asize, 0)); 
			insert_list(new);					/* 분할한 new block free list에 삽입 */
		}
		else {								
			PUT(HDRP(bp), PACK(csize, 1));
			PUT(FTRP(bp), PACK(csize, 1));
		} 
    }
    else {										/* heap space의 기존의 free block */
		if ((csize - asize) >= (2 * DSIZE)) {	/* 할당하고 남은 블록이 분할이 가능한가 */
			delete_list(bp);					/* segregated free list에서 삭제 */
			PUT(HDRP(bp), PACK(asize, 1));
			PUT(FTRP(bp), PACK(asize, 1));
			void *new = NEXT_BLKP(bp);			/* 분할 */
			PUT(HDRP(new), PACK(csize-asize, 0));
			PUT(FTRP(new), PACK(csize-asize, 0)); 
			insert_list(new);					/* 분할한 new block free list에 삽입 */
		}
		else {
            PUT(HDRP(bp), PACK(csize, 1));
			PUT(FTRP(bp), PACK(csize, 1));
			delete_list(bp);					/* segregated free list에서 삭제 */
		}
	}
}

/*
 *	mm_check
 *	 - Check consistency of heap.
 */
int mm_check(void)
{
	void *bp;
	int free_list_num = 0, free_heap_num = 0;
	
	for(int i = 0; i < segregated_lists; i++){
		if(seg_listp[i]!=NULL){
			for(bp = seg_listp[i]; bp!=NULL; bp = NEXT_FREE_BLKP(bp)){
				/* Is every block in the free list marked as free ? */
				if(GET_ALLOC(bp)){
					printf("Error1 : Allocated block exists in free_list\n");
					return 0;
				}
				/* Do the pointers in the free list point to valid free blocks */
				if(checkfreeblock(bp) == 0)
					return 0;
				free_list_num++;
			}
		}
	}

	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		/* Is every block in the heap Double-word aligned ? */
		if((unsigned int)bp % DSIZE){
			printf("Error2 : Not Double-word aligned\n");
			return 0;
		}
		/* Is every block in the hep matched Header and footer */
		if(GET(HDRP(bp)) != GET(FTRP(bp))){
			printf("Error3 : Header does not match footer\n");
			return 0;
		}
		/* Are there any contiguous free blocks that somehow escpaed coalescing? */
		if(!(GET_ALLOC(HDRP(bp))) && !(GET_ALLOC(FTRP(PREV_BLKP(bp))) && GET_ALLOC(HDRP(NEXT_BLKP(bp))))){
			printf("Error4 : consecutive free blocks\n");
			return 0;
		}
		if(!GET_ALLOC(HDRP(bp)))
			free_heap_num++;
	}
	
	/* Is every free block actually in the free list */
	if(free_heap_num != free_list_num){
		printf("Error5 : some free blocks are not in free_list\n");
		return 0;
	}
	return 1;
}

/*
 *	checkfreeblock
 *	 - Perform a minimal check on the free block.
 */
static int checkfreeblock(void *bp)
{
	/*Checks if the pointers in the free list point to valid free blocks*/

	/* previous free block이 next free block으로 current block을 가리키고 있는가 */ 
	if(PREV_FREE_BLKP(bp))  
	{
		if(NEXT_FREE_BLKP(PREV_FREE_BLKP(bp)) != bp)
		{
			printf("Error 6: Free list inconsistent");
			return 0;
		}
	}
	
	/* next free block이 previous free block으로 current block을 가리키고 있는가 */
	if(NEXT_FREE_BLKP(bp) && NEXT_FREE_BLKP(bp) != heap_listp)
	{
		if(PREV_FREE_BLKP(NEXT_FREE_BLKP(bp)) != bp)
		{
			printf("Error 6:Free list inconsistent");
			return 0;
		}
	}
	return 1;
}
