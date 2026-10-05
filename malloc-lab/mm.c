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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// 8의 배수로 만드는 매크로
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// define
static char *heap_listp = 0;        // allocator가 관리하는 첫 블록을 가리키는 기준 포인터

#define WSIZE           4           // WORD
#define DSIZE           8           // DOUBLE WORD
#define CHUNKSIZE       (1<<6)     // 힙 확장시 4096바이트 한번에 확장

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)   ((size) | (alloc))          // 블록 크기와 할당여부를 동시에 저장

#define GET(p)          (*(unsigned int *)(p))          // 헤더, 푸터 값 읽기
#define PUT(p, val)     (*(unsigned int *)(p) = (val))  // 헤더, 푸터 값 쓰기

#define GET_SIZE(p)     (GET(p) & ~0x7)                 // 헤더에서 블록 크기 얻기
#define GET_ALLOC(p)    (GET(p) & 0x1)                  // 헤더에서 이전블록 할당여부 플래그 확인

#define HDRP(bp)        ((char *)(bp) - WSIZE)          // 헤더 포인터 주소
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 푸터 포인터 주소

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   // 다음 블록주소
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   // 이전 블록주소

// explicit
#define UNSORTED_BIN_LENGTH 10

#define MAX_SMALL_BIN       1024
#define SMALL_BIN_LENGTH    129
#define SMALL_BIN_UNIT      8

#define LARGE_BIN_UNIT(i)   ((128ULL) * (1ULL << (i)))
#define LARGE_BIN_LENGTH    11

#define NEXT_FREE_PTR(bp)   ((char *)(bp))              // 다음 빈 블록 주소의 위치
#define PREV_FREE_PTR(bp)   ((char *)(bp) + DSIZE)      // 이전 빈 블록 주소의 위치

#define GET_PTR(p)          (*(char **)(p))             // 포인터가 저장된 포인터 읽기
#define PUT_PTR(p, val)     (*(char **)(p) = (val))     // 포인터가 저장된 포인터 쓰기


static void *extend_heap(size_t words);
static char *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void classify_block(void * bp, size_t size);
static void insert_linked_list(char *prev, char* cur);
static void del_linked_list(char *prev, char* cur);
static void del_from_bin(char *bp, size_t size);
static char **find_head(char *bp, size_t size);
static void block_split(char *bp, size_t asize, size_t remain_size);
static void write_end_of_heap_block(char *bp, size_t asize);

static void print_fragmentation(size_t request_size)
{
    char *bp = NEXT_BLKP(heap_listp);

    size_t total_free = 0;
    size_t largest_free = 0;
    size_t free_count = 0;
    size_t total_alloc = 0;

    printf("\n========== HEAP FRAGMENTATION ==========\n");
    printf("request size : %zu\n", request_size);

    while (GET_SIZE(HDRP(bp)) != 0)   // epilogue까지
    {
        size_t block_size = GET_SIZE(HDRP(bp));
        int alloc = GET_ALLOC(HDRP(bp));

        if (alloc)
        {
            total_alloc += block_size;
        }
        else
        {
            total_free += block_size;
            free_count++;

            if (block_size > largest_free)
                largest_free = block_size;

            printf(
                "[FREE] bp=%p size=%zu\n",
                bp,
                block_size
            );
        }

        bp = NEXT_BLKP(bp);
    }

    printf("----------------------------------------\n");
    printf("total allocated : %zu\n", total_alloc);
    printf("total free      : %zu\n", total_free);
    printf("largest free    : %zu\n", largest_free);
    printf("free blocks     : %zu\n", free_count);

    if (total_free > 0)
    {
        double fragmentation =
            1.0 - ((double)largest_free / (double)total_free);

        printf(
            "external fragmentation : %.2f %%\n",
            fragmentation * 100.0
        );
    }

    if (largest_free >= request_size)
    {
        printf(
            ">>> WARNING: 충분한 free block이 존재함.\n"
            ">>> 그런데 find_fit이 실패했다면 bin/find_fit 문제 가능성 큼.\n"
        );
    }
    else if (total_free >= request_size)
    {
        printf(
            ">>> FRAGMENTATION: 전체 free 메모리는 충분하지만\n"
            ">>> 연속된 free block이 부족함.\n"
        );
    }
    else
    {
        printf(
            ">>> 실제 free 메모리 자체가 부족함.\n"
        );
    }

    printf("========================================\n\n");
}

static void print_heap_blocks(void)
{
    char *bp = NEXT_BLKP(heap_listp);

    printf("\n========== HEAP BLOCKS ==========\n");

    int index = 0;

    while (GET_SIZE(HDRP(bp)) != 0)
    {
        printf(
            "[%d] bp=%p size=%zu %s\n",
            index,
            bp,
            GET_SIZE(HDRP(bp)),
            GET_ALLOC(HDRP(bp)) ? "ALLOC" : "FREE"
        );

        bp = NEXT_BLKP(bp);
        index++;
    }

    printf("[EPILOGUE]\n");
    printf("=================================\n\n");
}

typedef struct arena
{
    char * unsorted_bin;                    // tcache
    char * small_bin[SMALL_BIN_LENGTH];     // 24 ~ 1024
    char * large_bin[LARGE_BIN_LENGTH];     // 1024 ~ 10240 이상
} Arena;

static Arena arena;                   // NULL

static void insert_linked_list(char *prev, char* cur)
{
    // a -> c 에 b를 삽입
    PUT_PTR(NEXT_FREE_PTR(cur), GET_PTR(NEXT_FREE_PTR(prev)));   // b -> c
    PUT_PTR(NEXT_FREE_PTR(prev), cur);                  // a -> b
    PUT_PTR(PREV_FREE_PTR(cur), prev);                  // pb -> a
    //PUT_PTR(PREV_FREE_PTR(NEXT_FREE_PTR(cur)), cur);    // pc -> b
    char *next = GET_PTR(NEXT_FREE_PTR(cur));
    if (next != NULL)
    {
        PUT_PTR(PREV_FREE_PTR(next), cur);
    }
}

static void del_linked_list(char *prev, char* cur)
{
    // a -> b -> c 에서 b를 제거
    PUT_PTR(NEXT_FREE_PTR(prev), GET_PTR(NEXT_FREE_PTR(cur)));   // a -> c
    char *next = GET_PTR(NEXT_FREE_PTR(cur));
    if (next != NULL)
    {
        PUT_PTR(PREV_FREE_PTR(next), prev);   // pc -> a
    }
    
    // 연결 해제
    PUT_PTR(PREV_FREE_PTR(cur), NULL);                
    PUT_PTR(NEXT_FREE_PTR(cur), NULL);  
}

static void insert_head(char *head, char* bp)
{
    PUT_PTR(NEXT_FREE_PTR(bp), head);
    PUT_PTR(PREV_FREE_PTR(bp), NULL);
    if (head != NULL)
    {
        PUT_PTR(PREV_FREE_PTR(head), bp);
    }
}

/**
 * @brief 경계처리를 위한 할당 블록 초기화
 * @return 정상 실행시 0, 오류발생시 -1
 */
int mm_init(void)
{
    arena = (Arena){0};

    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1) return -1;

    // 경계처리를 위한 가짜 할당 블록 만들기
    // 첫 블록, 마지막 블록일 때의 특수처리를 없앤다.
    PUT(heap_listp, 0);                             // 8바이트 정렬을 위한 4바이트
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));  // 4바이트 크기 prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));  // 4바이트 크기 prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));      // 4바이트 크기 epilogue header
    heap_listp += (2 * WSIZE);                      // 시작 포인터를 payload위치로

    // 큰 free block 만들기 
    char *bp;
    if ((bp = extend_heap(CHUNKSIZE / WSIZE)) == NULL) return -1;
    classify_block(bp, GET_SIZE(HDRP(bp)));
    return 0;
}

/**
 * @brief free block을 실제로 만드는 함수
 * @param words 워드 개수
 * @return 병합한 결과 블록
 */
static void *extend_heap(size_t words)
{
    char *block_pointer;    // 새 free 블록의 첫 주소를 가리키는 포인터
    size_t size;            // 블록의 사이즈

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;   // size를 짝수로 → 8바이트 정렬
    // mem_sbrk는 확장하기 전 힙의 끝 주소를 반환한다.
    if ((long)(block_pointer = mem_sbrk(size)) == -1)  return NULL; // 힙 확장 실패시 NULL

    write_end_of_heap_block(block_pointer, size);

    // 포인터 초기화
    PUT_PTR(PREV_FREE_PTR(block_pointer), NULL);
    PUT_PTR(NEXT_FREE_PTR(block_pointer), NULL);

    return coalesce(block_pointer);

    //return block_pointer;
}

static void del_from_bin(char *bp, size_t size)
{
    if (bp == NULL) return;

    if (GET_PTR(PREV_FREE_PTR(bp)) == NULL && GET_PTR(NEXT_FREE_PTR(bp)) == NULL)
    {
        char **head = find_head(bp, size);
        //if (**head == NULL) return;
        if (*head != NULL)  *head = NULL;
        return;
    }
    else if (GET_PTR(PREV_FREE_PTR(bp)) == NULL && GET_PTR(NEXT_FREE_PTR(bp)) != NULL)
    {
        char **head = find_head(bp, size);
        *head = GET_PTR(NEXT_FREE_PTR(bp));
        PUT_PTR(PREV_FREE_PTR(*head), NULL);
    }
    else
    {
        del_linked_list(GET_PTR(PREV_FREE_PTR(bp)), bp);
    }
}

/**
 * @brief bin에서 블록 찾기
 * @param bp 찾는 블록 포인터
 * @param size 찾는 블록 사이즈
 */
static char **find_head(char *bp, size_t size)
{
    if (arena.unsorted_bin == bp)   return &arena.unsorted_bin;
    
    for (int i = 0; i < SMALL_BIN_LENGTH; i++)
    {
        if (arena.small_bin[i] == bp)   return &arena.small_bin[i];
    }

    for (int i = 0; i < LARGE_BIN_LENGTH; i++)
    {
        if (arena.large_bin[i] == bp)   return &arena.large_bin[i];
    }

    return NULL;
}
/**
 * @brief free 블록이면서 bin에 없는 블록 병합
 * @param words sbrk로 할당받은 블록 포인터 주소
 */
static char* coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 빈 블록 할당 플래그
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 빈 블록 할당 플래그
    size_t size = GET_SIZE(HDRP(bp));                   // 블록의 크기

    char *prev_bp = PREV_BLKP(bp);
    char *next_bp = NEXT_BLKP(bp);

    if (prev_alloc && next_alloc)   
    {// 양쪽 모두 할당

    }
    else if (prev_alloc && !next_alloc)
    {// 오른쪽만 빈 블록

        // 현재 빈 블록이 bin에 있다면 해제
        // 헤드 포인터일경우

        // 오른쪽 빈 블록이 bin에 있다면 해제
        del_from_bin(next_bp, GET_SIZE(HDRP(NEXT_BLKP(bp))));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));          // 오른쪽 블록의 크기를 가져와 합침
        PUT(HDRP(bp), PACK(size, 0));                   // 블록 포인터는 중간으로
        PUT(FTRP(bp), PACK(size, 0));                   // 블록 포인터는 중간으로
    }
    else if (!prev_alloc && next_alloc)
    {// 왼쪽만 빈 블록

        // 현재 빈 블록이 bin에 있다면 해제
        // 헤드 포인터일경우

        // 왼쪽 빈 블록이 bin에 있다면 해제
        del_from_bin(prev_bp, GET_SIZE(HDRP(PREV_BLKP(bp))));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));          // 왼쪽 블록의 크기를 가져와 합침
        PUT(FTRP(bp), PACK(size, 0));                   // 블록 포인터는 중간으로
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));        // 블록 포인터는 왼쪽으로
        bp = PREV_BLKP(bp); 
    }
    else
    {// 둘다 빈 블록

        // 현재 빈 블록이 bin에 있다면 해제
        // 헤드 포인터일경우

        // 왼쪽 빈 블록이 bin에 있다면 해제
        del_from_bin(prev_bp, GET_SIZE(HDRP(PREV_BLKP(bp))));

        // 오른쪽 빈 블록이 bin에 있다면 해제
        del_from_bin(next_bp, GET_SIZE(HDRP(NEXT_BLKP(bp))));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    //classify_block(bp, size);

    return bp;
}

/**
 * @brief 블록을 bin에 넣기
 * @param size 블록의 크기
 * @param bp bin에 넣을 블록
 */
static void classify_block(void * bp, size_t size)
{
    // 여기에 이전, 다음 빈 블록 포인터 작성
    // small bin
    if (size <= MAX_SMALL_BIN)
    {
        // 헤드 인덱스 계산
        size_t i = 3;
        for (; i < SMALL_BIN_LENGTH - 1; i++)
        {
            if(size <= SMALL_BIN_UNIT * i)  break;
        }
        char *small_bin_head = arena.small_bin[i];

        // 헤드가 NULL
        if(small_bin_head == NULL)   
        {
            arena.small_bin[i] = bp;
            PUT_PTR(NEXT_FREE_PTR(bp), NULL);
            PUT_PTR(PREV_FREE_PTR(bp), NULL);
            return;
        }

        // 헤드보다 bp의 주소값이 작을 때
        if (small_bin_head > bp)
        {
            arena.small_bin[i] = bp;
            insert_head(small_bin_head, bp);
            return;
        }

        // 헤드보다 bp의 주소값이 클 때
        char *cur = GET_PTR(NEXT_FREE_PTR(small_bin_head));
        char *prev = small_bin_head;
        while(cur != NULL && cur < bp)
        {
            prev = cur;
            cur = GET_PTR(NEXT_FREE_PTR(cur));
        }

        insert_linked_list(prev, bp);
    }
    // large bin
    else
    {
        // large bin 범위에 해당하는지 검사
        // large_bin[0] : 1024 ~ 2048
        // large_bin[1] : 2048 ~ 3072
        // large_bin[10] : 
        size_t i = 1;
        for (; i < LARGE_BIN_LENGTH; i++)
        {
            if(size < 1024 + LARGE_BIN_UNIT(i))  break;
        }
        i--;
        char *large_bin_head = arena.large_bin[i];

        // 헤드가 NULL
        if(large_bin_head == NULL)   
        {
            arena.large_bin[i] = bp;
            PUT_PTR(NEXT_FREE_PTR(bp), NULL);
            PUT_PTR(PREV_FREE_PTR(bp), NULL);
            return;
        }

        // 헤드보다 bp의 크기가 작을때
        if (GET_SIZE(HDRP(large_bin_head)) > size)
        {
            arena.large_bin[i] = bp;
            insert_head(large_bin_head, bp);
            return;
        }

        // 오름차순 정렬
        char *cur = GET_PTR(NEXT_FREE_PTR(large_bin_head));
        char *prev = large_bin_head;
        while(cur != NULL && GET_SIZE(HDRP(cur)) < size)
        {
            prev = cur;
            cur = GET_PTR(NEXT_FREE_PTR(cur));
        }

        insert_linked_list(prev, bp);
    }

    return;
}

/**
 * @brief 요청받은 크기만큼 블록 할당
 * @param size 요청 크기
 * @return 할당받은 블록 포인터 주소
 */
void *mm_malloc(size_t size)
{
    size_t asize;       // 정렬에 맞춰진 크기
    size_t extendsize;  // 더 큰 확장된 힙 영역
    char *bp;           // payload 주소

    if (size == 0)  return NULL;    // 요청 크기가 0

    if (size <= 2 * DSIZE)  asize = 3 * DSIZE;  // 최소 크기(24) 할당
    else  asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);   // 헤더와 푸터를 더하고 DSIZE 배수로

    // asize 이상 크기의 free block을 찾고 할당
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        // print_fragmentation(asize);
        // print_heap_blocks();
        return bp;
    }
    
    // free block을 못찾았을 때 힙을 늘림
    extendsize = MAX(asize, CHUNKSIZE);
    
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;

    place(bp, asize);
    // print_fragmentation(extendsize);
    // print_heap_blocks();
    return bp;
}

/**
 * @brief 적당한 크기의 free 블록 찾기
 * @param asize 요청 크기
 * @return 찾은 free 블록 포인터 주소
 */
static void *find_fit(size_t asize)
{
    // unsorted bin에서 찾기
    char *cur = arena.unsorted_bin;
    while(cur != NULL && asize > GET_SIZE(HDRP(cur)))
    {// 적절하지 못하면 즉시 small, large로 분류
        del_from_bin(cur, GET_SIZE(HDRP(cur)));
        classify_block(cur, GET_SIZE(HDRP(cur)));
        cur = arena.unsorted_bin;
    }

    if(cur)
    {
        arena.unsorted_bin = GET_PTR(NEXT_FREE_PTR(cur));
        if (arena.unsorted_bin != NULL)
        {
            PUT_PTR(PREV_FREE_PTR(arena.unsorted_bin), NULL);
        }
        return cur;
    }

    arena.unsorted_bin = NULL;

    // small bin에서 찾기
    size_t s_i = (size_t)(asize / SMALL_BIN_UNIT);
    for (; s_i < SMALL_BIN_LENGTH; s_i++)
    {
        if (arena.small_bin[s_i] != NULL)
        {
            char * p = arena.small_bin[s_i];
            char * new_head = GET_PTR(NEXT_FREE_PTR(p));
            if (new_head != NULL)
            {
                PUT_PTR(PREV_FREE_PTR(new_head), NULL);
            }
            arena.small_bin[s_i] = new_head;
            return p;
        }
    }
    // large bin에서 찾기

    for (size_t i = 0; i < LARGE_BIN_LENGTH; i++)
    {
        char *cur = arena.large_bin[i];
        while (cur != NULL && asize > GET_SIZE(HDRP(cur)))
        {
            cur = GET_PTR(NEXT_FREE_PTR(cur));
        }

        if (cur == NULL)    continue;

        del_from_bin(cur, GET_SIZE(HDRP(cur)));
        return cur;
    }
    
    // 찾지 못한 경우
    return NULL;
}

/**
 * @brief 찾은 free 블록을 적당히 잘라 할당해주는 함수
 * @param bp 요청받은 블록 주소
 * @param asize 요청 크기
 */
static void place(void *bp, size_t asize)
{
    size_t size = GET_SIZE(HDRP(bp));

    // 자르고 남는 블록 크기가 24Byte 미만일경우 분할하지 않음
    if (size - asize < 3 * DSIZE)
    {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));  
        return;
    }

    // 24 이상일경우 분할
    block_split(bp, asize, size - asize);


    // 분할하고 남은거 정리
    char *merged = coalesce(NEXT_BLKP(bp));
    classify_block(NEXT_BLKP(bp), GET_SIZE(HDRP(NEXT_BLKP(bp))));
    return;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // unsoretd bin에 넣기
    char *merged = coalesce(bp);
    char *unsorted_head = arena.unsorted_bin;

    insert_head(unsorted_head, merged);
    arena.unsorted_bin = merged;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (!ptr)
    {
        return mm_malloc(size);
    }

    if (size == 0)  
    {
        mm_free(ptr);
        return NULL;    // 요청 크기가 0
    }

    // 요청한 크기보다 이미 가지고 있는 크기가 더 크면 분할 후 리턴

    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t asize;                   // 정렬에 맞춰진 크기

    if (size <= 2 * DSIZE)  asize = 3 * DSIZE;  // 최소 크기(24) 할당
    else  asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);   // 헤더와 푸터를 더하고 DSIZE 배수로

    if (old_size >= asize)
    {
        place(ptr, asize);
        return ptr;
    }

    void *oldptr = ptr;
    void *newptr;

    size_t copySize;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)    copySize = size;    // 복사량을 기존 payload에 맞춘다.

    // 블록을 병합해야할 경우

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr))); // 이전 빈 블록 할당 플래그
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr))); // 다음 빈 블록 할당 플래그

    size_t prev_block_size = GET_SIZE(HDRP(PREV_BLKP(ptr)));
    size_t next_block_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

    if (prev_alloc && next_alloc)
    {

    }
    else if (prev_alloc && !next_alloc)
    {
        // 1. 제자리, 오른쪽 블록 병합
        if (old_size + next_block_size >= asize)
        {
            // 이제 사용할 블록이므로 bin에서 제거
            del_from_bin(NEXT_BLKP(ptr), next_block_size);
            
            // 적절히 잘라서 병합하고 남은건 분류
            size_t total_size = old_size + next_block_size;
            size_t remain_size = total_size - asize;
            // 최소 크기보다 작게 남으면 다 주기
            if (remain_size < 3 * DSIZE )
            {
                PUT(HDRP(ptr), PACK(total_size, 1));
                PUT(FTRP(ptr), PACK(total_size, 1));
                return ptr;
            }

            // 아니면 쓸만큼 쓰고 분할해서 분류
            block_split(ptr, asize, remain_size);
            classify_block(NEXT_BLKP(ptr), remain_size);
            return ptr;
        }
    }
    else if (!prev_alloc && next_alloc)
    {
        // 2. 블록을 왼쪽으로 옮겨야 할 경우
        // 2 - 1. 왼쪽이 비어있는데 병합하면 공간이 충분한 경우
        newptr =  PREV_BLKP(ptr);

        if (old_size + prev_block_size >= asize)
        {
            del_from_bin(PREV_BLKP(ptr), prev_block_size);

            // 적절히 잘라서 병합하고 남은건 분류
            size_t total_size = old_size + prev_block_size;
            size_t remain_size = total_size - asize;

            // 최소 크기보다 작게 남으면 다 주기
            if (remain_size < 3 * DSIZE )
            {
                memmove(newptr, oldptr, copySize);
                PUT(HDRP(newptr), PACK(total_size, 1));
                PUT(FTRP(newptr), PACK(total_size, 1));
                return newptr;
            }

            // 아니면 쓸만큼 쓰고 분할해서 분류
            memmove(newptr, oldptr, copySize);
            block_split(newptr, asize, remain_size);


            classify_block(NEXT_BLKP(newptr), remain_size);
            return newptr;
        }
    }
    else
    {
        // 2 - 1 - 3. 왼쪽과 오른쪽이 비어있는데 병합하면 공간이 충분한 경우
        if (old_size + prev_block_size + next_block_size >= asize)
        {
            newptr =  PREV_BLKP(ptr);

            del_from_bin(PREV_BLKP(ptr), prev_block_size);
            del_from_bin(NEXT_BLKP(ptr), next_block_size);

            // 적절히 잘라서 병합하고 남은건 분류
            size_t total_size = old_size + prev_block_size + next_block_size;
            size_t remain_size = total_size - asize;

            // 최소 크기보다 작게 남으면 다 주기
            if (remain_size < 3 * DSIZE )
            {
                memmove(newptr, oldptr, copySize);
                PUT(HDRP(newptr), PACK(total_size, 1));
                PUT(FTRP(newptr), PACK(total_size, 1));
                return newptr;
            }

            // 아니면 쓸만큼 쓰고 분할해서 분류
            memmove(newptr, oldptr, copySize);
            block_split(newptr, asize, remain_size);
            classify_block(NEXT_BLKP(newptr), remain_size);
            return newptr;
        }
    }

    // asize 이상 크기의 free block을 찾고 할당해야하는 경우
    if ((newptr = find_fit(asize)) != NULL)
    {
        // 완전히 다른곳으로 이동
        // 3 - 1. 적절한 블록이 있는지 탐색후 위치 옮기기
        // 3 - 2. 적절한 블록이 없으면 확장 후 할당(malloc)
        place(newptr, asize);
        memcpy(newptr, oldptr, copySize);
        mm_free(oldptr);
        return newptr;
    }
    
    // 블록을 확장해야할 경우
    // 1. 왼쪽은 할당, 요청받은 블록이 힙 끝이면 그대로 확장만
    if (prev_alloc && next_alloc && next_block_size == 0)
    {
        // mem_sbrk는 확장하기 전 힙의 끝 주소를 반환한다.
        // 필요한 payload만큼 요청
        if ((long)(mem_sbrk(asize - old_size)) == -1)  return NULL; // 힙 확장 실패시 NULL

        write_end_of_heap_block(ptr, asize);

        return ptr;
    }

    // 2. 왼쪽 병합했는데 공간이 부족, 그런데 힙의 끝이어서 제자리 확장이 가능한 경우
    if (!prev_alloc && (old_size + prev_block_size < asize) && 
        next_alloc && next_block_size == 0)
    {
        // mem_sbrk는 확장하기 전 힙의 끝 주소를 반환한다.
        // 필요한 payload만큼 요청
        if ((long)(mem_sbrk(asize - (old_size + prev_block_size))) == -1)  return NULL; // 힙 확장 실패시 NULL
        
        del_from_bin(PREV_BLKP(ptr), prev_block_size);

        memmove(newptr, oldptr, copySize);
        write_end_of_heap_block(newptr, asize);

        return newptr;
    }

    // 3. 제자리, 오른쪽 블록 병합 해도 부족한데, 힙 끝인 경우 확장
    if (prev_alloc && !next_alloc && old_size + next_block_size < asize && GET_SIZE(HDRP(NEXT_BLKP(NEXT_BLKP(oldptr)))) == 0)
    {
        // mem_sbrk는 확장하기 전 힙의 끝 주소를 반환한다.
        // 필요한 payload만큼 요청
        if ((long)(mem_sbrk(asize - (old_size + next_block_size))) == -1)  return NULL; // 힙 확장 실패시 NULL
        
        del_from_bin(NEXT_BLKP(oldptr), next_block_size);
        write_end_of_heap_block(oldptr, asize);

        return oldptr;
    }

    // 완전히 다른곳으로 확장
    // 1. 적절한 블록이 있는지 탐색후 위치 옮기기
    // 2. 적절한 블록이 없으면 확장 후 할당(malloc)
    newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;

    if (size < copySize)    copySize = size;    // 복사량을 기존 payload에 맞춘다.
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void write_end_of_heap_block(char *bp, size_t asize)
{
    PUT(HDRP(bp), PACK(asize, 1));            // 블록의 헤더 작성
    PUT(FTRP(bp), PACK(asize, 1));            // 블록의 푸터 작성
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));     // epilogue 주소 헤더 작성
}

static void block_split(char *bp, size_t asize, size_t remain_size)
{
    // 사용할 블록
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));

    // 남은 블록
    PUT(HDRP(NEXT_BLKP(bp)), PACK(remain_size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(remain_size, 0));
}