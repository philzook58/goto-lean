#include <stddef.h>
#include "checks.h"

/* Native C only. Slide exponents stay in the stated 0..15 test domain. */
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (!size) return 0;
    uint64_t packed = 0;
    for (size_t i = 1; i < size && i <= 8; ++i) packed |= (uint64_t)data[i] << (8*(i-1));
    switch (data[0] % 3) {
    case 0: (void)json_case(packed, size > 9 ? 8 : size-1, data[0] % 5); break;
    case 1: (void)slide_case((uint32_t)packed & 0x0f0f0f0fu); break;
    case 2: (void)lookup_case((unsigned)packed); break;
    }
    return 0;
}
