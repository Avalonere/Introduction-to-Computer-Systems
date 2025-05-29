#include "cachelab.h" // printSummary
#include <stdio.h> // printf
#include <stdlib.h> // malloc, free, exit
#include <getopt.h> // getopt
#include <unistd.h>


// 定义缓存行的结构体，包含有效位、标记位和LRU计数器
typedef struct
{
    int valid;
    unsigned long tag;
    unsigned long lru;
} cacheLine;

typedef cacheLine **cache; //定义缓存数组

// 定义全局变量，用于存储命令行参数和缓存统计信息
int s = -1, E, b = -1; // 缓存的组数的指数、每组的行数和每行的块数的指数
int S, B; // 缓存的组数、每行的块数
char *traceFile; // trace文件的路径
int verbose; // 是否打印详细信息
int hitCount, missCount, evictionCount; // 缓存的命中、失效和替换次数
unsigned long lruCount; // 缓存的LRU计数器，用于实现替换策略
cache simCache; // 模拟的缓存

// 初始化缓存，根据命令行参数分配内存空间，并将所有缓存行的有效位设为0，LRU计数器设为0
void initCache(void)
{
    // TODO: 在这里编写初始化缓存的代码
    // 分配数组的内存空间
    simCache = (cacheLine **) malloc(sizeof(cacheLine *) * S);
    for (int i = 0; i < S; i++)
    {
        simCache[i] = (cacheLine *) malloc(sizeof(cacheLine) * E);
    }
    // 将所有缓存行的有效位设为0，LRU计数器设为0
    for (int i = 0; i < S; i++)
    {
        for (int j = 0; j < E; j++)
        {
            simCache[i][j].valid = 0;
            simCache[i][j].lru = 0;
        }
    }
}

// 释放缓存，释放分配的内存空间
void freeCache(void)
{
    // TODO: 在这里编写释放缓存的代码
    // 释放数组的内存空间
    for (int i = 0; i < S; i++)
    {
        free(simCache[i]);
    }
    free(simCache);
}

// 访问缓存，根据给定的地址判断是否命中缓存，如果命中则更新LRU计数器，如果不命中则从内存中加载数据，并可能发生替换
void accessCache(unsigned long address)
{
    // TODO: 在这里编写访问缓存的代码
    // 计算地址的组索引和标记位
    unsigned long setIndex = (address >> b) & ((1 << s) - 1);
    unsigned long tag = address >> (s + b);
    // 遍历缓存中的每一行，查找是否有匹配的标记位和有效位
    int hit = 0; // 是否命中的标志
    int emptyLine = -1; // 空闲的缓存行的索引，初始为-1
    int lruLine = 0; // 最近最少使用的缓存行的索引，初始为0
    unsigned long minLRU = simCache[setIndex][0].lru; // 最小的LRU计数器的值，初始为第0行的值
    for (int i = 0; i < E; i++)
    {
        // 如果找到匹配的标记位和有效位，说明命中缓存
        if (simCache[setIndex][i].tag == tag && simCache[setIndex][i].valid == 1)
        {
            hit = 1;
            // 更新命中缓存行的LRU计数器
            simCache[setIndex][i].lru = ++lruCount;
            // 如果是详细模式，打印命中信息
            if (verbose)
            {
                printf("hit ");
            }
            // 增加命中次数
            hitCount++;
            // 结束循环
            break;
        }
            // 如果没有找到匹配的标记位和有效位，记录空闲的缓存行和最近最少使用的缓存行
        else
        {
            // 如果遇到有效位为0的缓存行，说明该行是空闲的
            if (simCache[setIndex][i].valid == 0)
            {
                // 记录第一个遇到的空闲缓存行的索引
                if (emptyLine == -1)
                {
                    emptyLine = i;
                }
            }
            // 如果遇到LRU计数器小于当前最小值的缓存行，说明该行是最近最少使用的
            if (simCache[setIndex][i].lru < minLRU)
            {
                // 记录最近最少使用的缓存行的索引和LRU计数器的值
                lruLine = i;
                minLRU = simCache[setIndex][i].lru;
            }
        }
    }
    // 如果没有命中缓存，说明缓存失效
    if (hit == 0)
    {
        // 如果是详细模式，打印失效信息
        if (verbose)
        {
            printf("miss ");
        }
        // 增加失效次数
        missCount++;
        // 如果有空闲的缓存行，将数据加载到该行
        if (emptyLine != -1)
        {
            // 设置有效位和标记位
            simCache[setIndex][emptyLine].valid = 1;
            simCache[setIndex][emptyLine].tag = tag;
            // 更新LRU计数器
            simCache[setIndex][emptyLine].lru = ++lruCount;
        }
            // 如果没有空闲的缓存行，说明需要替换最近最少使用的缓存行
        else
        {
            // 如果是详细模式，打印替换信息
            if (verbose)
            {
                printf("eviction ");
            }
            // 增加替换次数
            evictionCount++;
            // 设置标记位
            simCache[setIndex][lruLine].tag = tag;
            // 更新LRU计数器
            simCache[setIndex][lruLine].lru = ++lruCount;
        }
    }
}

// 回放trace文件，根据给定的trace文件模拟缓存的访问过程，并记录缓存的统计信息
void replayTrace(void)
{
    // TODO: 在这里编写回放trace文件的代码
    // 打开trace文件
    FILE *trace = fopen(traceFile, "r");
    // 检查文件是否打开成功
    if (trace == NULL)
    {
        fprintf(stderr, "%s: %s\n", traceFile, "No such file or directory");
        exit(1);
    }
    // 定义trace文件中的操作类型、地址和大小
    char operation;
    unsigned long address;
    int size;
    // 逐行读取trace文件中的内容
    while (fscanf(trace, " %c %lx,%d", &operation, &address, &size) == 3)
    {
        // 如果是详细模式，打印操作类型、地址和大小
        if (verbose)
        {
            printf("%c %lx,%d ", operation, address, size);
        }
        // 根据操作类型，执行相应的缓存访问
        switch (operation)
        {
            case 'L': // 数据加载
            case 'S': // 数据存储
                accessCache(address);
                break;
            case 'M': // 数据修改，相当于先加载后存储
                accessCache(address);
                accessCache(address);
                break;
            default: // 其他操作，忽略
                break;
        }
        // 如果是详细模式，换行
        if (verbose)
        {
            printf("\n");
        }
    }
    // 关闭trace文件
    fclose(trace);
}

// 打印帮助信息，显示程序的用法和选项
void printUsage(char *argv[])
{
    printf("Usage: %s [-hv] -s <s> -E <E> -b <b> -t <trace_file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/dave.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/dave.trace\n", argv[0]);
}

// 主函数，解析命令行参数，初始化缓存，回放trace文件，释放缓存，打印缓存的统计信息
int main(int argc, char *argv[])
{
    int option;
    while ((option = getopt(argc, argv, "s:E:b:t:hv")) != -1)
    {
        switch (option)
        {
            case 's':
                s = strtol(optarg, NULL, 10);
                break;
            case 'E':
                E = strtol(optarg, NULL, 10);
                break;
            case 'b':
                b = strtol(optarg, NULL, 10);
                break;
            case 't':
                traceFile = optarg;
                break;
            case 'v':
                verbose = 1;
                break;
            case 'h':
                printUsage(argv);
                exit(0);
            default:
                printUsage(argv);
                exit(1);
        }
    }

    // 检查命令行参数是否完整
    if (s == -1 || E == 0 || b == -1 || traceFile == NULL)
    {
        printf("%s: Missing required command line argument\n", argv[0]);
        printUsage(argv);
        exit(1);
    }

    // 计算S和B的值
    S = 1 << s;
    B = 1 << b;

    // 初始化缓存
    initCache();

    // 回放trace文件
    replayTrace();

    // 释放缓存
    freeCache();

    // 打印缓存的统计信息
    printSummary(hitCount, missCount, evictionCount);
    return 0;
}
