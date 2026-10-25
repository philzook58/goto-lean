#ifndef CASE_STUDY_CHECKS_H
#define CASE_STUDY_CHECKS_H
#include <assert.h>
#include <stdint.h>
#ifdef __CPROVER__
#define REQUIRE(p) __CPROVER_assume(p)
#define CHECK(p, message) __CPROVER_assert(p, message)
#else
#define REQUIRE(p) assert(p)
#define CHECK(p, message) assert(p)
#endif

typedef struct {
    int result;
    unsigned pos, next;
    int parent;
    int tokens[16];
} JsonReport;
JsonReport json_case(uint64_t text, unsigned length, unsigned capacity);
uint64_t slide_case(uint32_t input);
unsigned lookup_case(unsigned key);
#endif
