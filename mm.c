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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*Basic constants and macros */
#define WSIZE 4 //워드 크기
#define DSIZE 8 //더블 워드
#define CHUNKSIZE (1<<12) //초기 가용 블록, 힙ㅘ장을 위한 기본 크기

#define MAX(x,y) ((x) > (y) ? (x): (y)) 

// 헤더와 푸터에 저장할 수 있는 값 리턴
#define PACK(size, alloc) ((size) | (alloc)) //or 연산

/* 크기와 할당 비트를 통합해서 헤더와 푸터에 저장할 수 있는 값을 리턴*/
#define GET(p)      (*(unsigned int *)(p)) //p가 가리키는 메모리 주소에 있는 데이터를 읽어온다.
#define PUT(p, val) (*(unsigned int *)(p) = (val)) //p가 가리키고 있는 곳에 value를 넣는다.

/* 주소 p의 헤더 또는 푸터의 SIZE와 할당 비트를 리턴한다.*/
#define GET_SIZE(p)   (GET(p) & ~0x7) // 뒤에 3비트를 제외하고 읽어옴 and연산, 0x7 이진수 111을 not으로 000으로.
#define GET_ALLOC(p)  (GET(p) & 0x1) // 할당 가용 확인 둘다 1이면 할당됐다는 뜻

/* 각각 블록 헤더와 풋터를 가리키는 포인터를 리턴한다.*/
#define HDRP(bp)    ((char *)(bp) - WSIZE) //헤더블록 다음을 가리키니까 그 전을 가리키면 헤더를 가리킨다는 뜻 bp-4
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp))- DSIZE) //bp + size - 8

/* 다음과 이전 블록 포인터를 각각 리턴한다.*/
#define NEXT_BLKP(bp)   (((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)))//bp + size
#define PREV_BLKP(bp)   (((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)))//(bp - 8)footer 사이즈 만큼 빼주면댐
/*Read and write*/

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);


//전역 힙변수 및 함수 선언
static char* heap_listp;
static char *last_bp;
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) //할당기를 초기화하고 성공이면 0 아니면 -1
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); //초기 가리키는 값
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0,1));
    heap_listp += (2*WSIZE); //프롤로그랑 에필로그를 정했으니 heap_listp는 8만큼씩 더해진다.

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    last_bp = heap_listp;
    return 0;
}

//extend_heap
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; //words가 짝수면 size = words * 4 
    if((long)(bp=mem_sbrk(size)) == -1){
        return NULL;
    } 

    /* Initialize free block header/footer and the epilogue header*/
    PUT(HDRP(bp), PACK(size, 0)); //새로운 블록에 헤더를 만듬
    PUT(FTRP(bp), PACK(size, 0)); //새로운 블록에 풋터 만듬
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); //다음 bp가 가리키는 곳에 0/1 할당 (에필로그)

    /* coalesce if the previous block was free*/
    return coalesce(bp);
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0){
        return NULL;
    }

    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);
    }

    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        last_bp = bp;
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    last_bp = bp;
    return bp;
}

/*find fit --> next fit*/
static void *find_fit(size_t asize){

    char *bp = last_bp;

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp;
            return bp;
        }
    }

    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp;
            return bp;
        }
    }

    return NULL;
    // void *bp;
    // void *old_point = heap_listp;
    // for(bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //bp사이즈가 0보다 클때까지 계속 반복
    //     if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ //할당된 블록이 아니고, 할당할 사이즈가 블록사이즈보다 크거나 같으면
    //         //heap_listp = NEXT_BLKP(bp);
    //         return bp;
    //     }
    // }
    // return NULL;
}

/*place*/
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp)); //csize = 현재bp의 사이즈

    if((csize - asize) >= (2*DSIZE)){ //현재bp사이즈 - 할당할사이즈 가 최소할당사이즈 16보다 크면
        PUT(HDRP(bp), PACK(asize, 1)); //헤더에 asize만큼 1할당
        PUT(FTRP(bp), PACK(asize, 1)); //푸터도 할당
        bp = NEXT_BLKP(bp); //bp는 다음블록을 가리킴
        PUT(HDRP(bp), PACK(csize-asize, 0)); //다음 헤더bp에 csize - asize 만큼에 0할당
        PUT(FTRP(bp), PACK(csize-asize, 0)); //푸터도 마찬가지
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1)); //csize만큼 1할당
        PUT(FTRP(bp), PACK(csize, 1)); //푸터에도.
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); //헤더가 가리키는 블록의 사이즈 = size

    PUT(HDRP(bp), PACK(size, 0)); //헤더에 size 넣음
    PUT(FTRP(bp), PACK(size, 0)); //풋터에도 size를 할당 0 넣음
    coalesce(bp);
}

//할당되지 않은 블록들 병합하는 함수 coalesce
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //이전 블록의 푸터 할당여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //다음 블록의 헤더 할당여부
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 이전 블록과 다음 블록이 모두 할당된 상태 -> 병합할 필요가 없음
    if (prev_alloc && next_alloc){
        last_bp = bp;
        return bp;
    }
    //Case 2 이전블록 할당 상태, 다음 블록 free
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    //Case 3 이전 블록 free, 다음 블록 alloc
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    // Case 4 이전블록 , 다음블록 모두 free
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    last_bp = bp;
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    if (size == 0) {
        mm_free(ptr);
        return;
    } 

    void *new_ptr = mm_malloc(size);
    if (new_ptr == NULL) {
        return NULL;
    }
    size_t csize = GET_SIZE(HDRP(ptr));
    if (size < csize) { // 재할당 요청에 들어온 크기보다, 기존 블록의 크기가 크다면
        csize = size; // 기존 블록의 크기를 요청에 들어온 크기 만큼으로 줄인다.
    }
    memcpy(new_ptr, ptr, csize); // ptr 위치에서 csize만큼의 크기를 new_ptr의 위치에 복사함
    mm_free(ptr); // 기존 ptr의 메모리는 할당 해제해줌
    return new_ptr;
}














