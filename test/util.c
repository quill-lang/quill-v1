#include <stdint.h>
#include <stdio.h>

extern uint64_t sum(uint64_t, uint64_t, uint64_t);

int main()
{
    printf("1 + 2 + 3 = %lld\n", sum(1, 2, 3));
}