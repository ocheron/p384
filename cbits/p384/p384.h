/*
 * Copyright 2013 The Android Open Source Project
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of Google Inc. nor the names of its contributors may
 *       be used to endorse or promote products derived from this software
 *       without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY Google Inc. ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO
 * EVENT SHALL Google Inc. BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

// This implementation of P384 is derived from similar P256 implementation in
// libmincrypt.  Many parts of the source code are identical, after just a
// renaming.  Some differences are introduced related to the actual elliptic
// curve which is defined: field prime and element representation, coordinate
// size, scalar size and curve order.

#ifndef SYSTEM_CORE_INCLUDE_MINCRYPT_LITE_P384_H_
#define SYSTEM_CORE_INCLUDE_MINCRYPT_LITE_P384_H_

// Collection of routines manipulating 384 bit unsigned integers.
// Just enough to implement ecdsa-p384 and related algorithms.

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define P384_BITSPERDIGIT 32
#define P384_NDIGITS 12
#define P384_NBYTES 48

typedef int cryptonite_p384_err;
typedef uint32_t cryptonite_p384_digit;
typedef int32_t cryptonite_p384_sdigit;
typedef uint64_t cryptonite_p384_ddigit;
typedef int64_t cryptonite_p384_sddigit;

// Defining cryptonite_p384_int as struct to leverage struct assigment.
typedef struct {
  cryptonite_p384_digit a[P384_NDIGITS];
} cryptonite_p384_int;

extern const cryptonite_p384_int cryptonite_SECP384r1_n;  // Curve order
extern const cryptonite_p384_int cryptonite_SECP384r1_p;  // Curve prime
extern const cryptonite_p384_int cryptonite_SECP384r1_b;  // Curve param

// Initialize a cryptonite_p384_int to zero.
void cryptonite_p384_init(cryptonite_p384_int* a);

// Clear a cryptonite_p384_int to zero.
void cryptonite_p384_clear(cryptonite_p384_int* a);

// Return bit. Index 0 is least significant.
int cryptonite_p384_get_bit(const cryptonite_p384_int* a, int index);

// b := a % MOD
void cryptonite_p384_mod(
    const cryptonite_p384_int* MOD,
    const cryptonite_p384_int* a,
    cryptonite_p384_int* b);

// c := a * (top_b | b) % MOD
void cryptonite_p384_modmul(
    const cryptonite_p384_int* MOD,
    const cryptonite_p384_int* a,
    const cryptonite_p384_digit top_b,
    const cryptonite_p384_int* b,
    cryptonite_p384_int* c);

// b := 1 / a % MOD
// MOD best be SECP384r1_n
void cryptonite_p384_modinv(
    const cryptonite_p384_int* MOD,
    const cryptonite_p384_int* a,
    cryptonite_p384_int* b);

// b := 1 / a % MOD
// MOD best be SECP384r1_n
// Faster than cryptonite_p384_modinv()
void cryptonite_p384_modinv_vartime(
    const cryptonite_p384_int* MOD,
    const cryptonite_p384_int* a,
    cryptonite_p384_int* b);

// b := a << (n % P384_BITSPERDIGIT)
// Returns the bits shifted out of most significant digit.
cryptonite_p384_digit cryptonite_p384_shl(const cryptonite_p384_int* a, int n, cryptonite_p384_int* b);

// b := a >> (n % P384_BITSPERDIGIT)
void cryptonite_p384_shr(const cryptonite_p384_int* a, int n, cryptonite_p384_int* b);

int cryptonite_p384_is_zero(const cryptonite_p384_int* a);
int cryptonite_p384_is_odd(const cryptonite_p384_int* a);
int cryptonite_p384_is_even(const cryptonite_p384_int* a);

// Returns -1, 0 or 1.
int cryptonite_p384_cmp(const cryptonite_p384_int* a, const cryptonite_p384_int *b);

// c: = a - b
// Returns -1 on borrow.
int cryptonite_p384_sub(const cryptonite_p384_int* a, const cryptonite_p384_int* b, cryptonite_p384_int* c);

// c := a + b
// Returns 1 on carry.
int cryptonite_p384_add(const cryptonite_p384_int* a, const cryptonite_p384_int* b, cryptonite_p384_int* c);

// c := a + (single digit)b
// Returns carry 1 on carry.
int cryptonite_p384_add_d(const cryptonite_p384_int* a, cryptonite_p384_digit b, cryptonite_p384_int* c);

// ec routines.

// {out_x,out_y} := nG
void cryptonite_p384_base_point_mul(const cryptonite_p384_int *n,
                         cryptonite_p384_int *out_x,
                         cryptonite_p384_int *out_y);

// {out_x,out_y} := n{in_x,in_y}
void cryptonite_p384_point_mul(const cryptonite_p384_int *n,
                    const cryptonite_p384_int *in_x,
                    const cryptonite_p384_int *in_y,
                    cryptonite_p384_int *out_x,
                    cryptonite_p384_int *out_y);

// {out_x,out_y} := n1G + n2{in_x,in_y}
void cryptonite_p384_points_mul_vartime(
    const cryptonite_p384_int *n1, const cryptonite_p384_int *n2,
    const cryptonite_p384_int *in_x, const cryptonite_p384_int *in_y,
    cryptonite_p384_int *out_x, cryptonite_p384_int *out_y);

// Return whether point {x,y} is on curve.
int cryptonite_p384_is_valid_point(const cryptonite_p384_int* x, const cryptonite_p384_int* y);

// Outputs big-endian binary form. No leading zero skips.
void cryptonite_p384_to_bin(const cryptonite_p384_int* src, uint8_t dst[P384_NBYTES]);

// Reads from big-endian binary form,
// thus pre-pad with leading zeros if short.
void cryptonite_p384_from_bin(const uint8_t src[P384_NBYTES], cryptonite_p384_int* dst);

#define P384_DIGITS(x) ((x)->a)
#define P384_DIGIT(x,y) ((x)->a[y])

#define P384_ZERO {{0}}
#define P384_ONE {{1}}

#ifdef __cplusplus
}
#endif

#endif  // SYSTEM_CORE_INCLUDE_MINCRYPT_LITE_P384_H_
