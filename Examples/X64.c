#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t sum_to_n(uint64_t n);

int main(void) {
    const uint64_t result = sum_to_n(100);
    if (result != 5050) return 1;
    printf("%" PRIu64 "\n", result);
    return 0;
}
