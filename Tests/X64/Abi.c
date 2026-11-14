#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern uint64_t sum_to_n(uint64_t n);
extern void copy_bytes(uint8_t *dst, const uint8_t *src, uint64_t size);
extern uint64_t add128(uint64_t *out, const uint64_t *a, const uint64_t *b);
extern uint64_t indirect(void);
extern uint64_t sum_six(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t constant(void);
extern uint64_t check_preserved(void);

static int should_copy_unaligned_buffers_without_touching_surrounding_bytes(void) {
    uint8_t source[80], output[80];
    for (unsigned i = 0; i < sizeof(source); ++i) source[i] = (uint8_t)(i * 17);
    for (unsigned size = 0; size < 64; ++size) {
        memset(output, 0xa5, sizeof(output));
        copy_bytes(output + 3, source + 1, size);
        if (memcmp(output + 3, source + 1, size)) return 1;
        if (output[2] != 0xa5 || output[3 + size] != 0xa5) return 1;
    }
    return 0;
}

static int should_propagate_carry_across_128_bit_limbs(void) {
    const uint64_t a[] = {UINT64_MAX, UINT64_MAX};
    const uint64_t b[] = {1, 0};
    uint64_t output[2] = {42, 42};
    if (add128(output, a, b) != 1 || output[0] != 0 || output[1] != 0) return 1;
    const uint64_t c[] = {UINT64_MAX, 2};
    const uint64_t d[] = {7, 3};
    return add128(output, c, d) != 0 || output[0] != 6 || output[1] != 6;
}

int main(void) {
    for (uint64_t n = 0; n < 100; ++n)
        if (sum_to_n(n) != n * (n + 1) / 2) return 1;
    if (should_copy_unaligned_buffers_without_touching_surrounding_bytes()) return 2;
    if (should_propagate_carry_across_128_bit_limbs()) return 3;
    if (indirect() != 73) return 4;
    if (sum_six(1, 2, 3, 4, 5, 6) != 21) return 5;
    if (constant() != UINT64_C(0x123456789abcdef0)) return 6;
    if (check_preserved() != 1) return 7;
    puts("PASS: C ABI, preserved registers, nested-call alignment, byte copy, and 128-bit carry");
    return 0;
}
