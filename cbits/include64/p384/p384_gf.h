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

// This is an implementation of the P384 finite field. It's written to be
// portable and still constant-time.
//
// WARNING: Implementing these functions in a constant-time manner is far from
//          obvious. Be careful when touching this code.
//
// See http://www.imperialviolet.org/2010/12/04/ecc.html ([1]) for background.

#include <stdint.h>
#include <stdio.h>

#include <string.h>
#include <stdlib.h>

#include "p384/p384.h"

typedef uint8_t u8;
typedef uint32_t u32;
typedef int32_t s32;
typedef uint64_t u64;
typedef __uint128_t u128;

#define LIMB(lo,hi) (((u32) (lo)) + (((u64) (hi)) << 28))

/* Our field elements are represented as seven 64-bit limbs.
 *
 * The value of an felem (field element) is:
 *   x[0] + (x[1] << 1**55) + (x[2] << 1**110) + ... + (x[13] << 1**330)
 *
 * That is, each limb is 55-bits wide in little-endian order.
 *
 * This means that an felem hits 2**385, rather than 2**384 as we would like.
 *
 * Finally, the values stored in an felem are in Montgomery form. So the value
 * |y| is stored as (y*R) mod p, where p is the P-384 prime and R is 2**385.
 */
typedef u64 limb;
#define NLIMBS 7
typedef limb felem[NLIMBS];

static const limb kBottom55Bits = 0x7fffffffffffff;

/* kOne is the number 1 as an felem. It's 2**385 mod p split up into 55-bit
 * words. */
static const felem kOne = {
    0x7ffffe00000002, 0x3ffffffffff, 0x80000, 0, 0, 0, 0
};
static const felem kZero = {0};
static const felem kP = {
    0xffffffff, 0x7ffe0000000000, 0x7ffffffffbffff, 0x7fffffffffffff,
    0x7fffffffffffff, 0x7fffffffffffff, 0x3fffffffffffff
};
static const felem k2P = {
    0x1fffffffe, 0x7ffc0000000000, 0x7ffffffff7ffff, 0x7fffffffffffff,
    0x7fffffffffffff, 0x7fffffffffffff, 0x7fffffffffffff
};

/* Field element operations: */

/* NON_ZERO_TO_ALL_ONES returns:
 *   0xffffffffffffffff for 0 < x <= 2**63
 *   0 for x == 0 or x > 2**63.
 *
 * x must be a u64 or an equivalent type such as limb. */
#define NON_ZERO_TO_ALL_ONES(x) ((((u64)(x) - 1) >> 63) - 1)

/* felem_reduce_carry adds a multiple of p in order to cancel |carry|,
 * which is a term at 2**385.
 *
 * On entry: carry < 2**8, inout[0,1,...] < 2**55.
 * On exit: inout[0,1,..] < 2**56. */
static void felem_reduce_carry(felem inout, limb carry) {
  const u64 carry_mask = NON_ZERO_TO_ALL_ONES(carry);

  inout[0] += carry << 1;
  inout[0] += 0x80000000000000 & carry_mask;
  /* carry < 2**8 thus (carry << 33) < 2**41 and we added 2**55 in the
   * previous line therefore this doesn't underflow. */
  inout[0] -= carry << 33;
  inout[1] += ((carry << 42) - 1) & carry_mask;
  inout[2] += carry << 19;
}

/* felem_sum sets out = in+in2.
 *
 * On entry, in[i]+in2[i] must not overflow a 64-bit word.
 * On exit: out[0,1,...] < 2**56 */
static void felem_sum(felem out, const felem in, const felem in2) {
  limb carry = 0;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    out[i] = in[i] + in2[i];
    out[i] += carry;
    carry = out[i] >> 55;
    out[i] &= kBottom55Bits;
  }

  felem_reduce_carry(out, carry);
}

/* zero31 is 0 mod p. */
static const felem zero31 = {
  0x7f8001fffffffe00, 0x7ffbffffffffff01, 0x7ffffffff7ffff00,
  0x7fffffffffffff00, 0x7fffffffffffff00, 0x7fffffffffffff00,
  0x7fffffffffffff00
};

/* felem_diff sets out = in-in2.
 *
 * On entry: in[0,1,...] < 2**56 and in2[0,1,...] < 2**56.
 * On exit: out[0,1,...] < 2**56. */
static void felem_diff(felem out, const felem in, const felem in2) {
  limb carry = 0;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    out[i] = in[i] - in2[i];
    out[i] += zero31[i];
    out[i] += carry;
    carry = out[i] >> 55;
    out[i] &= kBottom55Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_reduce_degree sets out = tmp/R mod p where tmp contains 64-bit words
 * with the same 55 bit positions as an felem.
 *
 * The values in felems are in Montgomery form: x*R mod p where R = 2**385.
 * Since we just multiplied two Montgomery values together, the result is
 * x*y*R*R mod p. We wish to divide by R in order for the result also to be
 * in Montgomery form.
 *
 * On entry: tmp[i] < 2**128
 * On exit: out[0,1,...] < 2**56 */
static void felem_reduce_degree(felem out, u128 tmp[13]) {
   /* The following table may be helpful when reading this code:
    *
    * Limb number:   0 | 1 | 2 | 3 | 4 | 5 | 6
    * Width (bits):  55| 55| 55| 55| 55| 55| 55
    * Start bit:     0 | 55|110|165|220|275|330 */
  limb tmp2[15], carry, x, xMask;
  unsigned i;

  /* tmp contains 128-bit words with the same 55-bit positions as an
   * felem. So the top of an element of tmp might overlap with another
   * element two positions down. The following loop eliminates this
   * overlap. */
  tmp2[0] = (limb)(tmp[0] & kBottom55Bits);

  /* In the following we use "(limb) tmp[x]" and "(limb) (tmp[x]>>64)" to try
   * and hint to the compiler that it can do a single-word shift by selecting
   * the right register rather than doing a double-word shift and truncating
   * afterwards. */
  tmp2[1] = ((limb) tmp[0]) >> 55;
  tmp2[1] |= (((limb)(tmp[0] >> 64)) << 9) & kBottom55Bits;
  tmp2[1] += ((limb) tmp[1]) & kBottom55Bits;
  carry = tmp2[1] >> 55;
  tmp2[1] &= kBottom55Bits;

  for (i = 2; i < 13; i++) {
    tmp2[i] = ((limb)(tmp[i - 2] >> 64)) >> 46;
    tmp2[i] += ((limb)(tmp[i - 1])) >> 55;
    tmp2[i] += (((limb)(tmp[i - 1] >> 64)) << 9) & kBottom55Bits;
    tmp2[i] += ((limb) tmp[i]) & kBottom55Bits;
    tmp2[i] += carry;
    carry = tmp2[i] >> 55;
    tmp2[i] &= kBottom55Bits;
  }

  tmp2[13] = ((limb)(tmp[11] >> 64)) >> 46;
  tmp2[13] += ((limb)(tmp[12])) >> 55;
  tmp2[13] += (((limb)(tmp[12] >> 64)) << 9);
  tmp2[13] += carry;
  tmp2[14] = 0;

  /* Montgomery elimination of terms.
   *
   * Since R is 2**385, we can divide by R with a bitwise shift if we can
   * ensure that the right-most 385 bits are all zero. We can make that true by
   * adding multiplies of p without affecting the value.
   *
   * So we eliminate limbs from right to left. The bottom 55 bits of p are not
   * all ones, however this property will hold with multiple q = p.(1 + 2**32).
   * By adding tmp2[0]*q to tmp2 we'll make tmp2[0] == 0. We can do that for 13
   * further limbs and then right shift to eliminate the extra factor of R. */
  for (i = 0; i < NLIMBS; i++) {
    tmp2[i + 1] += tmp2[i] >> 55;
    x = tmp2[i] & kBottom55Bits;
    xMask = NON_ZERO_TO_ALL_ONES(x);
    tmp2[i] = 0;

    /* The bounds calculations for this loop are tricky. Each iteration of
     * the loop eliminates one word by adding values to words to its right.
     *
     * The following table contains the amounts added to each word (as an
     * offset from the value of i at the top of the loop). The amounts are
     * written as, for example, 55 to mean a value <2**55.
     *
     * Word:      1   2   3   4   5   6   7   8
     * Added:    56  57  55  55  55  55  56  31
     *
     * The value that is currently offset 3 will be offset 2 for the next
     * iteration and then offset 1 for the iteration after that. Therefore
     * the total value added will be the values added at 3, 2 and 1.
     *
     * The following table accumulates these values. The sums at the bottom
     * are written as, for example, 56+55, to mean a value < 2**56+2**55.
     *
     * Word:  1   2   3   4   5   6   7   8   9  10  11  12  13  14
     *       56  57  55  55  55  55  56  31
     *           56  57  55  55  55  55  56  31
     *               56  57  55  55  55  55  56  31
     *                   56  57  55  55  55  55  56  31
     *                       56  57  55  55  55  55  56  31
     *                           56  57  55  55  55  55  56  31
     *                               56  57  55  55  55  55  56  31
     *       ------------------------------------------------------
     *       56 57+ 57+  58  58+ 58+ 58+ 58+ 57+ 57+ 57+ 56+ 56+ 31
     *          56  56+      55  56  57  56+ 56+ 55+ 31+ 55+ 31
     *              55                   31  31  31+     31
     *
     * So the greatest amount is added to tmp2[7]. If tmp2[7] has an initial
     * value of <2**56, then the maximum value will be < 2**58 + 2**57 + 2**56,
     * which is < 2**64, as required. */
    tmp2[i + 1] += (x << 9) & kBottom55Bits;
    tmp2[i + 1] += (1ULL << 55) & xMask;
    tmp2[i + 1] -= (x << 41) & kBottom55Bits;
    tmp2[i + 2] += x >> 46;
    tmp2[i + 2] += ((3ULL << 55) - 1) & xMask;
    tmp2[i + 2] -= ((x << 18) & kBottom55Bits) << 1;
    tmp2[i + 2] -= x >> 14;
    tmp2[i + 2] -= (x << 50) & kBottom55Bits;
    tmp2[i + 3] += ((1ULL << 55) - 3) & xMask;
    tmp2[i + 3] -= x >> 5;
    tmp2[i + 3] -= (x >> 37) << 1;
    tmp2[i + 4] += ((1ULL << 55) - 1) & xMask;
    tmp2[i + 5] += ((1ULL << 55) - 1) & xMask;
    tmp2[i + 6] -= 1 & xMask;
    tmp2[i + 6] += (x << 54) & kBottom55Bits;
    tmp2[i + 7] += x >> 1;
    tmp2[i + 7] += (x << 31) & kBottom55Bits;
    tmp2[i + 8] += x >> 24;
  }

  x = tmp2[14];
  xMask = NON_ZERO_TO_ALL_ONES(x);
  tmp2[14] = 0;

  tmp2[0 + NLIMBS] += x << 1;
  tmp2[0 + NLIMBS] -= (x << 33) & kBottom55Bits;
  tmp2[1 + NLIMBS] -= x >> 22;
  tmp2[1 + NLIMBS] += (x << 42) & kBottom55Bits;
  tmp2[2 + NLIMBS] += x >> 13;
  tmp2[2 + NLIMBS] += (x << 19) & kBottom55Bits;
  tmp2[3 + NLIMBS] += x >> 36;

  /* We merge the right shift with a carry chain. The words above 2**385 have
   * widths of 55,... which we need to correct when copying them down.  */
  carry = 0;
  for (i = 0; i < NLIMBS; i++) {
    out[i] = tmp2[i + NLIMBS];
    out[i] += carry;
    carry = out[i] >> 55;
    out[i] &= kBottom55Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_square sets out=in*in.
 *
 * On entry: in[0,1,...] < 2**56.
 * On exit: out[0,1,...] < 2**56. */
static void felem_square(felem out, const felem in) {
  u128 tmp[13];

  tmp[ 0] = ((u128) in[0]) * (((u128) in[0]) << 0);
  tmp[ 1] = ((u128) in[0]) * (((u128) in[1]) << 1);
  tmp[ 2] = ((u128) in[0]) * (((u128) in[2]) << 1) +
            ((u128) in[1]) * (((u128) in[1]) << 0);
  tmp[ 3] = ((u128) in[0]) * (((u128) in[3]) << 1) +
            ((u128) in[1]) * (((u128) in[2]) << 1);
  tmp[ 4] = ((u128) in[0]) * (((u128) in[4]) << 1) +
            ((u128) in[1]) * (((u128) in[3]) << 1) +
            ((u128) in[2]) * (((u128) in[2]) << 0);
  tmp[ 5] = ((u128) in[0]) * (((u128) in[5]) << 1) +
            ((u128) in[1]) * (((u128) in[4]) << 1) +
            ((u128) in[2]) * (((u128) in[3]) << 1);
  /* tmp[6] has the greatest value of 2**113 + 2**113 + 2**113 + 2**112,
   * which is < 2**128 as required. */
  tmp[ 6] = ((u128) in[0]) * (((u128) in[6]) << 1) +
            ((u128) in[1]) * (((u128) in[5]) << 1) +
            ((u128) in[2]) * (((u128) in[4]) << 1) +
            ((u128) in[3]) * (((u128) in[3]) << 0);
  tmp[ 7] = ((u128) in[1]) * (((u128) in[6]) << 1) +
            ((u128) in[2]) * (((u128) in[5]) << 1) +
            ((u128) in[3]) * (((u128) in[4]) << 1);
  tmp[ 8] = ((u128) in[2]) * (((u128) in[6]) << 1) +
            ((u128) in[3]) * (((u128) in[5]) << 1) +
            ((u128) in[4]) * (((u128) in[4]) << 0);
  tmp[ 9] = ((u128) in[3]) * (((u128) in[6]) << 1) +
            ((u128) in[4]) * (((u128) in[5]) << 1);
  tmp[10] = ((u128) in[4]) * (((u128) in[6]) << 1) +
            ((u128) in[5]) * (((u128) in[5]) << 0);
  tmp[11] = ((u128) in[5]) * (((u128) in[6]) << 1);
  tmp[12] = ((u128) in[6]) * (((u128) in[6]) << 0);

  felem_reduce_degree(out, tmp);
}

/* felem_mul sets out=in*in2.
 *
 * On entry: in[0,1,...] < 2**56 and
 *           in2[0,1,...] < 2**56.
 * On exit: out[0,1,...] < 2**56. */
static void felem_mul(felem out, const felem in, const felem in2) {
  u128 tmp[13];

  tmp[ 0] = ((u128) in[0]) * ((u128) in2[0]);
  tmp[ 1] = ((u128) in[0]) * ((u128) in2[1]) +
            ((u128) in[1]) * ((u128) in2[0]);
  tmp[ 2] = ((u128) in[0]) * ((u128) in2[2]) +
            ((u128) in[1]) * ((u128) in2[1]) +
            ((u128) in[2]) * ((u128) in2[0]);
  tmp[ 3] = ((u128) in[0]) * ((u128) in2[3]) +
            ((u128) in[1]) * ((u128) in2[2]) +
            ((u128) in[2]) * ((u128) in2[1]) +
            ((u128) in[3]) * ((u128) in2[0]);
  tmp[ 4] = ((u128) in[0]) * ((u128) in2[4]) +
            ((u128) in[1]) * ((u128) in2[3]) +
            ((u128) in[2]) * ((u128) in2[2]) +
            ((u128) in[3]) * ((u128) in2[1]) +
            ((u128) in[4]) * ((u128) in2[0]);
  tmp[ 5] = ((u128) in[0]) * ((u128) in2[5]) +
            ((u128) in[1]) * ((u128) in2[4]) +
            ((u128) in[2]) * ((u128) in2[3]) +
            ((u128) in[3]) * ((u128) in2[2]) +
            ((u128) in[4]) * ((u128) in2[1]) +
            ((u128) in[5]) * ((u128) in2[0]);
  /* tmp[6] has the greatest value but doesn't overflow. See logic in
   * felem_square. */
  tmp[ 6] = ((u128) in[0]) * ((u128) in2[6]) +
            ((u128) in[1]) * ((u128) in2[5]) +
            ((u128) in[2]) * ((u128) in2[4]) +
            ((u128) in[3]) * ((u128) in2[3]) +
            ((u128) in[4]) * ((u128) in2[2]) +
            ((u128) in[5]) * ((u128) in2[1]) +
            ((u128) in[6]) * ((u128) in2[0]);
  tmp[ 7] = ((u128) in[1]) * ((u128) in2[6]) +
            ((u128) in[2]) * ((u128) in2[5]) +
            ((u128) in[3]) * ((u128) in2[4]) +
            ((u128) in[4]) * ((u128) in2[3]) +
            ((u128) in[5]) * ((u128) in2[2]) +
            ((u128) in[6]) * ((u128) in2[1]);
  tmp[ 8] = ((u128) in[2]) * ((u128) in2[6]) +
            ((u128) in[3]) * ((u128) in2[5]) +
            ((u128) in[4]) * ((u128) in2[4]) +
            ((u128) in[5]) * ((u128) in2[3]) +
            ((u128) in[6]) * ((u128) in2[2]);
  tmp[ 9] = ((u128) in[3]) * ((u128) in2[6]) +
            ((u128) in[4]) * ((u128) in2[5]) +
            ((u128) in[5]) * ((u128) in2[4]) +
            ((u128) in[6]) * ((u128) in2[3]);
  tmp[10] = ((u128) in[4]) * ((u128) in2[6]) +
            ((u128) in[5]) * ((u128) in2[5]) +
            ((u128) in[6]) * ((u128) in2[4]);
  tmp[11] = ((u128) in[5]) * ((u128) in2[6]) +
            ((u128) in[6]) * ((u128) in2[5]);
  tmp[12] = ((u128) in[6]) * ((u128) in2[6]);

  felem_reduce_degree(out, tmp);
}

static void felem_assign(felem out, const felem in) {
  memcpy(out, in, sizeof(felem));
}

/* felem_scalar_3 sets out=3*out.
 *
 * On entry: out[0,1,...] < 2**56.
 * On exit: out[0,1,...] < 2**56. */
static void felem_scalar_3(felem out) {
  limb carry = 0;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    out[i] *= 3;
    out[i] += carry;
    carry = out[i] >> 55;
    out[i] &= kBottom55Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_scalar_4 sets out=4*out.
 *
 * On entry: out[0,1,...] < 2**56.
 * On exit: out[0,1,...] < 2**56. */
static void felem_scalar_4(felem out) {
  limb carry = 0, next_carry;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    next_carry = out[i] >> 53;
    out[i] <<= 2;
    out[i] &= kBottom55Bits;
    out[i] += carry;
    carry = next_carry + (out[i] >> 55);
    out[i] &= kBottom55Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_scalar_8 sets out=8*out.
 *
 * On entry: out[0,1,...] < 2**56.
 * On exit: out[0,1,...] < 2**56. */
static void felem_scalar_8(felem out) {
  limb carry = 0, next_carry;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    next_carry = out[i] >> 52;
    out[i] <<= 3;
    out[i] &= kBottom55Bits;
    out[i] += carry;
    carry = next_carry + (out[i] >> 55);
    out[i] &= kBottom55Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_is_zero_vartime returns 1 iff |in| == 0. It takes a variable amount of
 * time depending on the value of |in|. */
static char felem_is_zero_vartime(const felem in) {
  limb carry;
  int i;
  limb tmp[NLIMBS];

  felem_assign(tmp, in);

  /* First, reduce tmp to a minimal form. */
  do {
    carry = 0;
    for (i = 0; i < NLIMBS; i++) {
      tmp[i] += carry;
      carry = tmp[i] >> 55;
      tmp[i] &= kBottom55Bits;
    }

    felem_reduce_carry(tmp, carry);
  } while (carry);

  /* tmp < 2**385, so the only possible zero values are 0, p and 2p. */
  return memcmp(tmp, kZero, sizeof(tmp)) == 0 ||
         memcmp(tmp, kP, sizeof(tmp)) == 0 ||
         memcmp(tmp, k2P, sizeof(tmp)) == 0;
}


/* Montgomery operations: */

#define kRDigits {0xfffffffe00000002, 0x1ffffffff, 2, 0, 0, 0} // 2^385 mod p384.p

#define kRInvDigits {0x7ffffff080000003, 0xfffffff5ffffffec, 0x7ffffffdfffffffe, 0x7ffffffe7ffffffd, 0x600000001, 0xa0000000a}  // 1 / 2^385 mod p384.p

static const cryptonite_p384_int kR = { kRDigits };
static const cryptonite_p384_int kRInv = { kRInvDigits };

/* to_montgomery sets out = R*in. */
static void to_montgomery(felem out, const cryptonite_p384_int* in) {
  cryptonite_p384_int in_shifted;
  int i;

  cryptonite_p384_init(&in_shifted);
  cryptonite_p384_modmul(&cryptonite_SECP384r1_p, in, 0, &kR, &in_shifted);

  for (i = 0; i < NLIMBS; i++) {
    out[i] = P384_DIGIT(&in_shifted, 0) & kBottom55Bits;
    cryptonite_p384_shr(&in_shifted, 55, &in_shifted);
  }

  cryptonite_p384_clear(&in_shifted);
}

/* from_montgomery sets out=in/R. */
static void from_montgomery(cryptonite_p384_int* out, const felem in) {
  cryptonite_p384_int result, tmp;
  int i, top;

  cryptonite_p384_init(&result);
  cryptonite_p384_init(&tmp);

  cryptonite_p384_add_d(&tmp, in[NLIMBS - 1], &result);
  for (i = NLIMBS - 2; i >= 0; i--) {
    top = cryptonite_p384_shl(&result, 55, &tmp);
    top += cryptonite_p384_add_d(&tmp, in[i], &result);
  }

  cryptonite_p384_modmul(&cryptonite_SECP384r1_p, &kRInv, top, &result, out);

  cryptonite_p384_clear(&result);
  cryptonite_p384_clear(&tmp);
}
