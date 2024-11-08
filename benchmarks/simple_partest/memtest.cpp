/*
This file implements a multi-threaded programmed IO write benchmark.  It is intended to be equivalent
to the `write_ints` test in the Rust benchmark

You can build it with:
    g++ memtest.cpp -march=native -fopenmp -O0 -DDO_MMAP -DTHREADS=64
*/

#include <cstdio>
#include <cstdlib>
#include <chrono>
#include "sys/mman.h"

const unsigned long long K = 10000000000ull;
volatile unsigned long long * array;

int main() {
//#define DO_MMAP
#ifdef DO_MMAP
    array = (unsigned long long *) mmap(nullptr, K*8, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS | MAP_POPULATE, -1, 0);
    if (array == MAP_FAILED) { perror("mmap"); exit(1); }
#else
    array = (volatile unsigned long long int *)(malloc(K * 8));
#endif

    auto t1 = std::chrono::system_clock::now();

    #pragma omp parallel for num_threads(THREADS)
    for (unsigned long long i = 0; i < K; ++i) { array[i] = i; }

    auto t2 = std::chrono::system_clock::now();

    printf("writing on %d threads took %ld millis\n", THREADS, std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count());

#ifdef DO_MMAP
    munmap((void*)array, K*8);
#else
    free((void*)array);
#endif
}
