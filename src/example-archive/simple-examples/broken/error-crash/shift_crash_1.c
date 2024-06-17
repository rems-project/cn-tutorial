// Derived from the openSUT - see the full example here in the repo:
// src/example-archive/openSUT/broken/error-crash/instrumentation_impl.c

#include <stdint.h>
uint8_t a(uint32_t b, uint32_t c, uint8_t ch) { a(b, c, 1) << 1; }
