/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
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
    /* Team name */
    "1",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* Basic constants and macros */
#define WSIZE 4 /* 워드 그리고 헤더/풋터 사이즈 (bytes) */
#define DSIZE 8 /* 더블 워드 사이즈 (bytes) */
#define CHUNKSIZE (1<<12) /* 이 양만큼 힙을 확징한다. (bytes) = 0b 00001 0000 0000 0000 0000 */
#define MAX(x, y) ((x) > (y)? (x) : (y)) /* max 기능 구현 */

/* 크기와 할당된 비트를 단어로 묶는다. */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에서 단어를 읽고 쓴다. */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에서 크기와 할당된 필드를 읽는다. */
/* 
p가 가리키는 위치에 저장된 4바이트 값을 가져오는 함수/메크로로 ~0x7은 하위 3비트를 제외한 나머지를 모두 1로 만든 비트마스크
이를 & 연산을 이용해 블록의 사이즈를 구한다.
*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 주어진 블록 ptr bp에 대해 헤더와 푸터의 주소를 계산한다. */ 
/* 블록 포인터 bp는 페이로드의 시작점으로 해당 주소에서 WSIZE를 빼면 헤더의 값을 얻을 수 있다. */
#define HDRP(bp) ((char *)(bp) - WSIZE)
 /* 블록 포인터 bp는 페이로드의 시작점으로 해당 주소에서 헤더에 서 블록의 주소를 추출해 더한 뒤 DSIZE 만큼 빼면 풋터의 시작 값이 된다. */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 주어진 블록 ptr bp에 대해 다음 블록과 이전 블록의 주소를 계산한다*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* single word (4) or double word (8) alignment 
    정렬기준이 8바이트임을 나타낸다.
*/
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT 
    메모리 정렬 요구사항을 맞추기 위해 8단위로 반올림한다
*/
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* 정렬을 위해 8바이트 단위로 반올림한다. */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 전역 변수 힙 리스트 선언 */
void* heap_listp;

/* 함수 선언 부 */

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 힙의 크기를 확장하는 함수 */
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    /* 정렬을 유지하기 위해 짝수 개의 단어를 할당한다. */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    bp = mem_sbrk(size);
    if (bp == (void *)-1)
        return NULL;
    
    /* free블록 헤더/푸터 및 에필로그 헤더를 초기화한다. */
    PUT(HDRP(bp), PACK(size, 0)); /* free 블럭 헤더 */
    PUT(FTRP(bp), PACK(size, 0)); /* free 블럭 풋터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* 새 에필로그 헤더 */

    /* 이전 블록이 비어 있으면 병합한다. */
    return coalesce(bp);
}


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); /* 정렬 패딩 생성 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* 프롤로그 헤더 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* 프롤로그 풋터 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* 에필로그 헤더 */
    heap_listp += (2*WSIZE);

    /* CHUNKSIZE 바이트 크기의 자유 블록으로 빈 힙을 확장한다. */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}


/*
 * mm_malloc - brk 포인터를 증가시켜 블록을 할당합니다.
 * 항상 정렬의 배수 크기의 블록을 할당하세요.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* 조정된 블록 크기 */
    size_t extendsize; /* 맞지 않으면 힙을 확장할 양 */
    char *bp;

    /* 허위 요청 무시 */
    if (size == 0){
        return NULL;
    }

    /* 오버헤드 및 정렬 요구 사항을 포함하도록 블록 크기를 조정합니다. */
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    /* 해제된 블록 목록에서 적합한 것을 검색하세요 */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    /* 적합한 것을 찾을 수 없는경우. 더 많은 메모리를 확보하고 블록을 배치하세요. */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;

    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

static void *find_fit(size_t asize){
    void *bp = heap_listp;

    while (GET_SIZE(HDRP(bp)) > 0){ // 에필로그 블록에 도달하기 까지
        /*
            헤더 블록 정보를 토대로 할당 되어 있지 않으며
            블록의 사이즈가 asize 보다 크거나 같은 블럭을 찾는다.
        */
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)){ 
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp)); /* 현재 가용 블록의 크기 */

    if ((csize - asize ) >= (2 * DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } 
    else {
        /* 분할 불가능 -> 그냥 전체 블록을 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); /* ptr이 가리키는 블록의 헤더에서 블록 전체 크기를 읽어온다 */

    PUT(HDRP(ptr), PACK(size, 0)); /* 헤더에 블록 크기와 할당 상태 0(free)을 기록한다 */
    PUT(FTRP(ptr), PACK(size, 0)); /* 풋터에도 동일하게 블록 크기와 할당 상태 0(free)을 기록한다 */
    coalesce(ptr); /* 인접한 가용 블록들과 병합(coalescing)을 시도한다 */
}

static void *coalesce(void *bp){

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); /* 이전 블록이 할당 되어있는지 정보를 가져온다. */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); /* 다음 블록이 할당 되어있는지 정보를 가져온다. */
    size_t size = GET_SIZE(HDRP(bp)); /* 현재 블럭을 사이즈를 계산한다. */

    if (prev_alloc && next_alloc){      /* Case 1: 이전, 다음 블록이 할당 되어있는 상태 */
        return bp;
    }
    
    else if (prev_alloc && !next_alloc){   /* Case 2: 이전 블록이 할당 되어 있고 다음 블럭이 해제 된 상태 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); /* 블럭 헤더에 새로 계산된 size 크기를 기록 */
        PUT(FTRP(bp), PACK(size, 0)); /* 블럭 풋터에 새로 계산된 size 크기를 기록 */
    }

    else if (!prev_alloc && next_alloc){   /* Case 3: 이전 블록이 해제 되어 있고 다음 블럭이 할당 된 상태 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));       /* 이전 블럭을 사이즈를 가져온다. */
        PUT(FTRP(bp), PACK(size, 0));                /* 풋터에 새로 계산된 사이즈 정보를 기록 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));     /* 이전 블록의 헤더에 새로 계산된 사이즈 정보 기록 */
        bp = PREV_BLKP(bp);                          /* 블럭 포인터를 이전 블록의 bp로 갱신 */
    }

    else {             /* Case 4: 이전 및 다음 블록이 전부 해제 된 상태 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  /* 이전 블럭과 다음 블럭의 사이즈 추가 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  /* 이전 블럭의 헤더에 새로 계산된 사이즈 기록 */
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));  /* 다음 블럭의 풋터에 새로 계산된 사이즈 기록 */
        bp = PREV_BLKP(bp);
    }
    return bp;
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}