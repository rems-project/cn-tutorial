// Tags: main, bitwise operations
/** Source: SAW Exercises
 */

/*

import "Popcount.cry";

popmod <- llvm_load_module "popcount.bc";

let pop_cryptol_check = do {
     x <- llvm_fresh_var "x" (llvm_int 32);
     llvm_execute_func [llvm_term x];
     llvm_return ( llvm_term {{ popCount x }} );
};

// same verification against Cryptol spec
llvm_verify popmod "pop_count" [] true pop_cryptol_check (do {
     //unfolding ["popCount"];
     //simplify (cryptol_ss());
     //print_goal;
     z3;
});

// Begin Cryptol additional verifications
// another tricky implementation
llvm_verify popmod "pop_count_mul" [] true pop_cryptol_check yices;

// verify the while loop version
llvm_verify popmod "pop_count_sparse" [] true pop_cryptol_check yices;


 */

#include <stdint.h>

/*
 * Returns a count of the set bits in a word.
 * From Henry S. Warren Jr.'s Hacker's Delight
 */
int pop_count(uint32_t x) {
    x = x - ((x >> 1) & 0x55555555);
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
    x = (x + (x >> 4)) & 0x0F0F0F0F;
    x = x + (x >> 8);
    x = x + (x >> 16);
    return x & 0x0000003F;
}

/* A version of popcount that uses multiplication */
int pop_count_mul(uint32_t x) {
    x = x - ((x >> 1) & 0x55555555);
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
    x = ((x + (x >> 4)) & 0x0F0F0F0F);
    return (x * 0x01010101) >> 24;
}


/* A version of popcount that uses an indefinite while loop(!) */
int pop_count_sparse(uint32_t x)
{
    int n;
    n = 0;
    while (x != 0) 
      {
        n = n + 1;
        x = x & (x - 1);
    }
    return n;
}
