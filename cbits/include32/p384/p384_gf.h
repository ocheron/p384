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

#define LIMB(lo,hi) (lo), (hi)

/* Our field elements are represented as fourteen 32-bit limbs.
 *
 * The value of an felem (field element) is:
 *   x[0] + (x[1] << 1**28) + (x[2] << 1**55) + ... + (x[13] << 1**358)
 *
 * That is, each limb is alternately 28 or 27-bits wide in little-endian
 * order.
 *
 * This means that an felem hits 2**385, rather than 2**384 as we would like.
 *
 * Finally, the values stored in an felem are in Montgomery form. So the value
 * |y| is stored as (y*R) mod p, where p is the P-384 prime and R is 2**385.
 */
typedef u32 limb;
#define NLIMBS 14
typedef limb felem[NLIMBS];

static const limb kBottom27Bits = 0x7ffffff;
static const limb kBottom28Bits = 0xfffffff;

/* kOne is the number 1 as an felem. It's 2**385 mod p split up into 28 and
 * 27-bit words. */
static const felem kOne = {
    2, 0x7ffffe0, 0xfffffff, 0x3fff, 0x80000, 0, 0, 0,
    0, 0, 0, 0, 0, 0
};
static const felem kZero = {0};
static const felem kP = {
    0xfffffff, 0xf, 0, 0x7ffe000, 0xffbffff, 0x7ffffff, 0xfffffff,
    0x7ffffff, 0xfffffff, 0x7ffffff, 0xfffffff, 0x7ffffff, 0xfffffff, 0x3ffffff
};
static const felem k2P = {
    0xffffffe, 0x1f, 0, 0x7ffc000, 0xff7ffff, 0x7ffffff, 0xfffffff,
    0x7ffffff, 0xfffffff, 0x7ffffff, 0xfffffff, 0x7ffffff, 0xfffffff, 0x7ffffff
};

/* Field element operations: */

/* NON_ZERO_TO_ALL_ONES returns:
 *   0xffffffff for 0 < x <= 2**31
 *   0 for x == 0 or x > 2**31.
 *
 * x must be a u32 or an equivalent type such as limb. */
#define NON_ZERO_TO_ALL_ONES(x) ((((u32)(x) - 1) >> 31) - 1)

/* felem_reduce_carry adds a multiple of p in order to cancel |carry|,
 * which is a term at 2**385.
 *
 * On entry: carry < 2**4, inout[0,2,...] < 2**28, inout[1,3,...] < 2**27.
 * On exit: inout[0,2,..] < 2**29, inout[1,3,...] < 2**28. */
static void felem_reduce_carry(felem inout, limb carry) {
  const u32 carry_mask = NON_ZERO_TO_ALL_ONES(carry);

  inout[0] += carry << 1;
  inout[1] += 0x08000000 & carry_mask;
  /* carry < 2**4 thus (carry << 5) < 2**9 and we added 2**27 in the
   * previous line therefore this doesn't underflow. */
  inout[1] -= carry << 5;
  inout[2] += (0x10000000 - 1) & carry_mask;
  inout[3] += ((carry << 14) - 1) & carry_mask;
  inout[4] += carry << 19;
}

/* felem_sum sets out = in+in2.
 *
 * On entry, in[i]+in2[i] must not overflow a 32-bit word.
 * On exit: out[0,2,...] < 2**29, out[1,3,...] < 2**28 */
static void felem_sum(felem out, const felem in, const felem in2) {
  limb carry = 0;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    out[i] = in[i] + in2[i];
    out[i] += carry;
    carry = out[i] >> 28;
    out[i] &= kBottom28Bits;

    i++;

    out[i] = in[i] + in2[i];
    out[i] += carry;
    carry = out[i] >> 27;
    out[i] &= kBottom27Bits;
  }

  felem_reduce_carry(out, carry);
}

/* zero31 is 0 mod p. */
static const felem zero31 = {
  0x7ffffff0, 0x380000f8, 0x7ffffff9, 0x3ffdfff8, 0x7fbffff8, 0x3ffffff8,
  0x7ffffff8, 0x3ffffff8, 0x7ffffff8, 0x3ffffff8, 0x7ffffff8, 0x3ffffff8,
  0x7ffffff8, 0x3ffffff8
};

/* felem_diff sets out = in-in2.
 *
 * On entry: in[0,2,...] < 2**29, in[1,3,...] < 2**28 and
 *           in2[0,2,...] < 2**29, in2[1,3,...] < 2**28.
 * On exit: out[0,2,...] < 2**29, out[1,3,...] < 2**28. */
static void felem_diff(felem out, const felem in, const felem in2) {
  limb carry = 0;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    out[i] = in[i] - in2[i];
    out[i] += zero31[i];
    out[i] += carry;
    carry = out[i] >> 28;
    out[i] &= kBottom28Bits;

    i++;

    out[i] = in[i] - in2[i];
    out[i] += zero31[i];
    out[i] += carry;
    carry = out[i] >> 27;
    out[i] &= kBottom27Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_reduce_degree sets out = tmp/R mod p where tmp contains 64-bit words
 * with the same 28,27,... bit positions as an felem.
 *
 * The values in felems are in Montgomery form: x*R mod p where R = 2**385.
 * Since we just multiplied two Montgomery values together, the result is
 * x*y*R*R mod p. We wish to divide by R in order for the result also to be
 * in Montgomery form.
 *
 * On entry: tmp[i] < 2**64
 * On exit: out[0,2,...] < 2**29, out[1,3,...] < 2**28 */
static void felem_reduce_degree(felem out, u64 tmp[27]) {
   /* The following table may be helpful when reading this code:
    *
    * Limb number:   0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10...
    * Width (bits):  28| 27| 28| 27| 28| 27| 28| 27| 28| 27| 28
    * Start bit:     0 | 28| 55| 53|110|138|165|193|220|248|275
    *   (odd phase): 0 | 27| 55| 52|110|137|165|192|220|247|275 */
  limb tmp2[28], carry, x, xMask;
  unsigned i;

  /* tmp contains 64-bit words with the same 28,27,28-bit positions as an
   * felem. So the top of an element of tmp might overlap with another
   * element two positions down. The following loop eliminates this
   * overlap. */
  tmp2[0] = (limb)(tmp[0] & kBottom28Bits);

  /* In the following we use "(limb) tmp[x]" and "(limb) (tmp[x]>>32)" to try
   * and hint to the compiler that it can do a single-word shift by selecting
   * the right register rather than doing a double-word shift and truncating
   * afterwards. */
  tmp2[1] = ((limb) tmp[0]) >> 28;
  tmp2[1] |= (((limb)(tmp[0] >> 32)) << 4) & kBottom27Bits;
  tmp2[1] += ((limb) tmp[1]) & kBottom27Bits;
  carry = tmp2[1] >> 27;
  tmp2[1] &= kBottom27Bits;

  for (i = 2; i < 27; i++) {
    tmp2[i] = ((limb)(tmp[i - 2] >> 32)) >> 23;
    tmp2[i] += ((limb)(tmp[i - 1])) >> 27;
    tmp2[i] += (((limb)(tmp[i - 1] >> 32)) << 5) & kBottom28Bits;
    tmp2[i] += ((limb) tmp[i]) & kBottom28Bits;
    tmp2[i] += carry;
    carry = tmp2[i] >> 28;
    tmp2[i] &= kBottom28Bits;

    i++;
    if (i == 27)
      break;
    tmp2[i] = ((limb)(tmp[i - 2] >> 32)) >> 23;
    tmp2[i] += ((limb)(tmp[i - 1])) >> 28;
    tmp2[i] += (((limb)(tmp[i - 1] >> 32)) << 4) & kBottom27Bits;
    tmp2[i] += ((limb) tmp[i]) & kBottom27Bits;
    tmp2[i] += carry;
    carry = tmp2[i] >> 27;
    tmp2[i] &= kBottom27Bits;
  }

  tmp2[27] = ((limb)(tmp[25] >> 32)) >> 23;
  tmp2[27] += ((limb)(tmp[26])) >> 28;
  tmp2[27] += (((limb)(tmp[26] >> 32)) << 4);
  tmp2[27] += carry;

  /* Montgomery elimination of terms.
   *
   * Since R is 2**385, we can divide by R with a bitwise shift if we can
   * ensure that the right-most 385 bits are all zero. We can make that true by
   * adding multiplies of p without affecting the value.
   *
   * So we eliminate limbs from right to left. Since the bottom 28 bits of p
   * are all ones, then by adding tmp2[0]*p to tmp2 we'll make tmp2[0] == 0.
   * We can do that for 13 further limbs and then right shift to eliminate the
   * extra factor of R. */
  for (i = 0; i < NLIMBS; i += 2) {
    tmp2[i + 1] += tmp2[i] >> 28;
    x = tmp2[i] & kBottom28Bits;
    xMask = NON_ZERO_TO_ALL_ONES(x);
    tmp2[i] = 0;

    /* The bounds calculations for this loop are tricky. Each iteration of
     * the loop eliminates two words by adding values to words to their
     * right.
     *
     * The following table contains the amounts added to each word (as an
     * offset from the value of i at the top of the loop). The amounts are
     * accounted for from the first and second half of the loop separately
     * and are written as, for example, 28 to mean a value <2**28.
     *
     * Word:                  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
     * Added in top half:    27  5 27 28 27 28 27 28 27 28 27 28 28 27
     * Added in bottom half:    28  4 28 27 28 27 28 27 28 27 28 27 28 26
     *
     * The value that is currently offset 7 will be offset 5 for the next
     * iteration and then offset 3 for the iteration after that. Therefore
     * the total value added will be the values added at 7, 5 and 3.
     *
     * The following table accumulates these values. The sums at the bottom
     * are written as, for example, 29+28, to mean a value < 2**29+2**28.
     *
     * Word:  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 ..
     *       27  5 27 28 27 28 27 28 27 28 27 28 28 27 26 27 26 27 26 27 26 ..
     *          28  4 28 27 28 27 28 27 28 27 28 27 28 28 28 28 28 28 28 28 ..
     *             27  5 27 28 27 28 27 28 27 28 27 28 27 28 27 28 27 28 27 ..
     *                28  4 28 27 28 27 28 27 28 27 28 27 28 27 28 27 28 27 ..
     *                   27  5 27 28 27 28 27 28 27 28 27 28 27 28 27 28 27 ..
     *                      28  4 28 27 28 27 28 27 28 27 28 27 28 27 28 27 ..
     *                         27  5 27 28 27 28 27 28 27 28 27 28 27 28 27 ..
     *                            28  4 28 27 28 27 28 27 28 27 28 27 28 27 ..
     *                               27  5 27 28 27 28 27 28 27 28 27 28 27 ..
     *                                  28  4 28 27 28 27 28 27 28 27 28 27 ..
     *                                     27  5 27 28 27 28 27 28 27 28 27 ..
     *                                        28  4 28 27 28 27 28 27 28 27 ..
     *                                           27  5  4  5  4  5  4  5  4 ..
     *                                              28 27 28 27 28 27 28 27 ..
     *
     * So the greatest amount is added to tmp2[14], tmp2[16], tmp2[18], etc. If
     * tmp2[14/16/18/..] has an initial value of <2**28, then the maximum value
     * will be < 2**27 + 13 * 2**28 + 5**5, which is < 2**32 as required. */
    tmp2[i +  1] += (x << 4) & kBottom27Bits;
    tmp2[i +  2] += x >> 23;
    tmp2[i +  3] += (1 << 27) & xMask;
    tmp2[i +  3] -= (x << 13) & kBottom27Bits;
    tmp2[i +  4] += ((1 << 28) - 1) & xMask;
    tmp2[i +  4] -= (x << 18) & kBottom28Bits;
    tmp2[i +  4] -= x >> 14;
    tmp2[i +  5] += ((1 << 27) - 1) & xMask;
    tmp2[i +  5] -= x >> 10;

    tmp2[i +  6] += ((1 << 28) - 1) & xMask;
    tmp2[i +  7] += ((1 << 27) - 1) & xMask;
    tmp2[i +  8] += ((1 << 28) - 1) & xMask;
    tmp2[i +  9] += ((1 << 27) - 1) & xMask;
    tmp2[i + 10] += ((1 << 28) - 1) & xMask;
    tmp2[i + 11] += ((1 << 27) - 1) & xMask;
    tmp2[i + 12] += ((1 << 28) - 1) & xMask;

    tmp2[i + 13] += ((1 << 27) - 1) & xMask;
    tmp2[i + 13] += (x << 26) & kBottom27Bits;
    tmp2[i + 14] += ((x >> 1) - 1) & xMask;

    if (i+1 == NLIMBS)
      break;
    tmp2[i + 2] += tmp2[i + 1] >> 27;
    x = tmp2[i + 1] & kBottom27Bits;
    xMask = NON_ZERO_TO_ALL_ONES(x);
    tmp2[i + 1] = 0;

    tmp2[i +  2] += (x << 5) & kBottom28Bits;
    tmp2[i +  3] += x >> 23;
    tmp2[i +  4] += (1 << 28) & xMask;
    tmp2[i +  4] -= (x << 14) & kBottom28Bits;
    tmp2[i +  5] += ((1 << 27) - 1) & xMask;
    tmp2[i +  5] -= (x << 18) & kBottom27Bits;
    tmp2[i +  5] -= x >> 14;
    tmp2[i +  6] += ((1 << 28) - 1) & xMask;
    tmp2[i +  6] -= x >> 9;

    tmp2[i +  7] += ((1 << 27) - 1) & xMask;
    tmp2[i +  8] += ((1 << 28) - 1) & xMask;
    tmp2[i +  9] += ((1 << 27) - 1) & xMask;
    tmp2[i + 10] += ((1 << 28) - 1) & xMask;
    tmp2[i + 11] += ((1 << 27) - 1) & xMask;
    tmp2[i + 12] += ((1 << 28) - 1) & xMask;
    tmp2[i + 13] += ((1 << 27) - 1) & xMask;

    tmp2[i + 14] += ((1 << 28) - 1) & xMask;
    tmp2[i + 14] += (x << 27) & kBottom28Bits;
    tmp2[i + 15] += ((x >> 1) - 1) & xMask;
  }

  /* We merge the right shift with a carry chain. The words above 2**385 have
   * widths of 28,27,... which we need to correct when copying them down.  */
  carry = 0;
  for (i = 0; i < NLIMBS; i++) {
    out[i] = tmp2[i + NLIMBS];
    out[i] += carry;
    carry = out[i] >> 28;
    out[i] &= kBottom28Bits;

    i++;

    out[i] = tmp2[i + NLIMBS];
    out[i] += carry;
    carry = out[i] >> 27;
    out[i] &= kBottom27Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_square sets out=in*in.
 *
 * On entry: in[0,2,...] < 2**29, in[1,3,...] < 2**28.
 * On exit: out[0,2,...] < 2**29, out[1,3,...] < 2**28. */
static void felem_square(felem out, const felem in) {
  u64 tmp[27];

  tmp[ 0] = ((u64) in[ 0]) * (in[ 0] << 0);
  tmp[ 1] = ((u64) in[ 0]) * (in[ 1] << 1);
  tmp[ 2] = ((u64) in[ 0]) * (in[ 2] << 1) +
            ((u64) in[ 1]) * (in[ 1] << 1);
  tmp[ 3] = ((u64) in[ 0]) * (in[ 3] << 1) +
            ((u64) in[ 1]) * (in[ 2] << 1);
  tmp[ 4] = ((u64) in[ 0]) * (in[ 4] << 1) +
            ((u64) in[ 1]) * (in[ 3] << 2) +
            ((u64) in[ 2]) * (in[ 2] << 0);
  tmp[ 5] = ((u64) in[ 0]) * (in[ 5] << 1) +
            ((u64) in[ 1]) * (in[ 4] << 1) +
            ((u64) in[ 2]) * (in[ 3] << 1);
  tmp[ 6] = ((u64) in[ 0]) * (in[ 6] << 1) +
            ((u64) in[ 1]) * (in[ 5] << 2) +
            ((u64) in[ 2]) * (in[ 4] << 1) +
            ((u64) in[ 3]) * (in[ 3] << 1);
  tmp[ 7] = ((u64) in[ 0]) * (in[ 7] << 1) +
            ((u64) in[ 1]) * (in[ 6] << 1) +
            ((u64) in[ 2]) * (in[ 5] << 1) +
            ((u64) in[ 3]) * (in[ 4] << 1);
  tmp[ 8] = ((u64) in[ 0]) * (in[ 8] << 1) +
            ((u64) in[ 1]) * (in[ 7] << 2) +
            ((u64) in[ 2]) * (in[ 6] << 1) +
            ((u64) in[ 3]) * (in[ 5] << 2) +
            ((u64) in[ 4]) * (in[ 4] << 0);
  tmp[ 9] = ((u64) in[ 0]) * (in[ 9] << 1) +
            ((u64) in[ 1]) * (in[ 8] << 1) +
            ((u64) in[ 2]) * (in[ 7] << 1) +
            ((u64) in[ 3]) * (in[ 6] << 1) +
            ((u64) in[ 4]) * (in[ 5] << 1);
  tmp[10] = ((u64) in[ 0]) * (in[10] << 1) +
            ((u64) in[ 1]) * (in[ 9] << 2) +
            ((u64) in[ 2]) * (in[ 8] << 1) +
            ((u64) in[ 3]) * (in[ 7] << 2) +
            ((u64) in[ 4]) * (in[ 6] << 1) +
            ((u64) in[ 5]) * (in[ 5] << 1);
  tmp[11] = ((u64) in[ 0]) * (in[11] << 1) +
            ((u64) in[ 1]) * (in[10] << 1) +
            ((u64) in[ 2]) * (in[ 9] << 1) +
            ((u64) in[ 3]) * (in[ 8] << 1) +
            ((u64) in[ 4]) * (in[ 7] << 1) +
            ((u64) in[ 5]) * (in[ 6] << 1);
  /* tmp[12] has the greatest value of 2**59 + 2**58 + 2**59 + 2**58 + 2**59 +
   * 2**58 + 2**58, which is < 2**64 as required. */
  tmp[12] = ((u64) in[ 0]) * (in[12] << 1) +
            ((u64) in[ 1]) * (in[11] << 2) +
            ((u64) in[ 2]) * (in[10] << 1) +
            ((u64) in[ 3]) * (in[ 9] << 2) +
            ((u64) in[ 4]) * (in[ 8] << 1) +
            ((u64) in[ 5]) * (in[ 7] << 2) +
            ((u64) in[ 6]) * (in[ 6] << 0);
  tmp[13] = ((u64) in[ 0]) * (in[13] << 1) +
            ((u64) in[ 1]) * (in[12] << 1) +
            ((u64) in[ 2]) * (in[11] << 1) +
            ((u64) in[ 3]) * (in[10] << 1) +
            ((u64) in[ 4]) * (in[ 9] << 1) +
            ((u64) in[ 5]) * (in[ 8] << 1) +
            ((u64) in[ 6]) * (in[ 7] << 1);
  tmp[14] = ((u64) in[ 1]) * (in[13] << 2) +
            ((u64) in[ 2]) * (in[12] << 1) +
            ((u64) in[ 3]) * (in[11] << 2) +
            ((u64) in[ 4]) * (in[10] << 1) +
            ((u64) in[ 5]) * (in[ 9] << 2) +
            ((u64) in[ 6]) * (in[ 8] << 1) +
            ((u64) in[ 7]) * (in[ 7] << 1);
  tmp[15] = ((u64) in[ 2]) * (in[13] << 1) +
            ((u64) in[ 3]) * (in[12] << 1) +
            ((u64) in[ 4]) * (in[11] << 1) +
            ((u64) in[ 5]) * (in[10] << 1) +
            ((u64) in[ 6]) * (in[ 9] << 1) +
            ((u64) in[ 7]) * (in[ 8] << 1);
  tmp[16] = ((u64) in[ 3]) * (in[13] << 2) +
            ((u64) in[ 4]) * (in[12] << 1) +
            ((u64) in[ 5]) * (in[11] << 2) +
            ((u64) in[ 6]) * (in[10] << 1) +
            ((u64) in[ 7]) * (in[ 9] << 2) +
            ((u64) in[ 8]) * (in[ 8] << 0);
  tmp[17] = ((u64) in[ 4]) * (in[13] << 1) +
            ((u64) in[ 5]) * (in[12] << 1) +
            ((u64) in[ 6]) * (in[11] << 1) +
            ((u64) in[ 7]) * (in[10] << 1) +
            ((u64) in[ 8]) * (in[ 9] << 1);
  tmp[18] = ((u64) in[ 5]) * (in[13] << 2) +
            ((u64) in[ 6]) * (in[12] << 1) +
            ((u64) in[ 7]) * (in[11] << 2) +
            ((u64) in[ 8]) * (in[10] << 1) +
            ((u64) in[ 9]) * (in[ 9] << 1);
  tmp[19] = ((u64) in[ 6]) * (in[13] << 1) +
            ((u64) in[ 7]) * (in[12] << 1) +
            ((u64) in[ 8]) * (in[11] << 1) +
            ((u64) in[ 9]) * (in[10] << 1);
  tmp[20] = ((u64) in[ 7]) * (in[13] << 2) +
            ((u64) in[ 8]) * (in[12] << 1) +
            ((u64) in[ 9]) * (in[11] << 2) +
            ((u64) in[10]) * (in[10] << 0);
  tmp[21] = ((u64) in[ 8]) * (in[13] << 1) +
            ((u64) in[ 9]) * (in[12] << 1) +
            ((u64) in[10]) * (in[11] << 1);
  tmp[22] = ((u64) in[ 9]) * (in[13] << 2) +
            ((u64) in[10]) * (in[12] << 1) +
            ((u64) in[11]) * (in[11] << 1);
  tmp[23] = ((u64) in[10]) * (in[13] << 1) +
            ((u64) in[11]) * (in[12] << 1);
  tmp[24] = ((u64) in[11]) * (in[13] << 2) +
            ((u64) in[12]) * (in[12] << 0);
  tmp[25] = ((u64) in[12]) * (in[13] << 1);
  tmp[26] = ((u64) in[13]) * (in[13] << 1);

  felem_reduce_degree(out, tmp);
}

/* felem_mul sets out=in*in2.
 *
 * On entry: in[0,2,...] < 2**29, in[1,3,...] < 2**28 and
 *           in2[0,2,...] < 2**29, in2[1,3,...] < 2**28.
 * On exit: out[0,2,...] < 2**29, out[1,3,...] < 2**28. */
static void felem_mul(felem out, const felem in, const felem in2) {
  u64 tmp[27];

  tmp[ 0] = ((u64) in[ 0]) * (in2[ 0] << 0);
  tmp[ 1] = ((u64) in[ 0]) * (in2[ 1] << 0) +
            ((u64) in[ 1]) * (in2[ 0] << 0);
  tmp[ 2] = ((u64) in[ 0]) * (in2[ 2] << 0) +
            ((u64) in[ 1]) * (in2[ 1] << 1) +
            ((u64) in[ 2]) * (in2[ 0] << 0);
  tmp[ 3] = ((u64) in[ 0]) * (in2[ 3] << 0) +
            ((u64) in[ 1]) * (in2[ 2] << 0) +
            ((u64) in[ 2]) * (in2[ 1] << 0) +
            ((u64) in[ 3]) * (in2[ 0] << 0);
  tmp[ 4] = ((u64) in[ 0]) * (in2[ 4] << 0) +
            ((u64) in[ 1]) * (in2[ 3] << 1) +
            ((u64) in[ 2]) * (in2[ 2] << 0) +
            ((u64) in[ 3]) * (in2[ 1] << 1) +
            ((u64) in[ 4]) * (in2[ 0] << 0);
  tmp[ 5] = ((u64) in[ 0]) * (in2[ 5] << 0) +
            ((u64) in[ 1]) * (in2[ 4] << 0) +
            ((u64) in[ 2]) * (in2[ 3] << 0) +
            ((u64) in[ 3]) * (in2[ 2] << 0) +
            ((u64) in[ 4]) * (in2[ 1] << 0) +
            ((u64) in[ 5]) * (in2[ 0] << 0);
  tmp[ 6] = ((u64) in[ 0]) * (in2[ 6] << 0) +
            ((u64) in[ 1]) * (in2[ 5] << 1) +
            ((u64) in[ 2]) * (in2[ 4] << 0) +
            ((u64) in[ 3]) * (in2[ 3] << 1) +
            ((u64) in[ 4]) * (in2[ 2] << 0) +
            ((u64) in[ 5]) * (in2[ 1] << 1) +
            ((u64) in[ 6]) * (in2[ 0] << 0);
  tmp[ 7] = ((u64) in[ 0]) * (in2[ 7] << 0) +
            ((u64) in[ 1]) * (in2[ 6] << 0) +
            ((u64) in[ 2]) * (in2[ 5] << 0) +
            ((u64) in[ 3]) * (in2[ 4] << 0) +
            ((u64) in[ 4]) * (in2[ 3] << 0) +
            ((u64) in[ 5]) * (in2[ 2] << 0) +
            ((u64) in[ 6]) * (in2[ 1] << 0) +
            ((u64) in[ 7]) * (in2[ 0] << 0);
  tmp[ 8] = ((u64) in[ 0]) * (in2[ 8] << 0) +
            ((u64) in[ 1]) * (in2[ 7] << 1) +
            ((u64) in[ 2]) * (in2[ 6] << 0) +
            ((u64) in[ 3]) * (in2[ 5] << 1) +
            ((u64) in[ 4]) * (in2[ 4] << 0) +
            ((u64) in[ 5]) * (in2[ 3] << 1) +
            ((u64) in[ 6]) * (in2[ 2] << 0) +
            ((u64) in[ 7]) * (in2[ 1] << 1) +
            ((u64) in[ 8]) * (in2[ 0] << 0);
  tmp[ 9] = ((u64) in[ 0]) * (in2[ 9] << 0) +
            ((u64) in[ 1]) * (in2[ 8] << 0) +
            ((u64) in[ 2]) * (in2[ 7] << 0) +
            ((u64) in[ 3]) * (in2[ 6] << 0) +
            ((u64) in[ 4]) * (in2[ 5] << 0) +
            ((u64) in[ 5]) * (in2[ 4] << 0) +
            ((u64) in[ 6]) * (in2[ 3] << 0) +
            ((u64) in[ 7]) * (in2[ 2] << 0) +
            ((u64) in[ 8]) * (in2[ 1] << 0) +
            ((u64) in[ 9]) * (in2[ 0] << 0);
  tmp[10] = ((u64) in[ 0]) * (in2[10] << 0) +
            ((u64) in[ 1]) * (in2[ 9] << 1) +
            ((u64) in[ 2]) * (in2[ 8] << 0) +
            ((u64) in[ 3]) * (in2[ 7] << 1) +
            ((u64) in[ 4]) * (in2[ 6] << 0) +
            ((u64) in[ 5]) * (in2[ 5] << 1) +
            ((u64) in[ 6]) * (in2[ 4] << 0) +
            ((u64) in[ 7]) * (in2[ 3] << 1) +
            ((u64) in[ 8]) * (in2[ 2] << 0) +
            ((u64) in[ 9]) * (in2[ 1] << 1) +
            ((u64) in[10]) * (in2[ 0] << 0);
  tmp[11] = ((u64) in[ 0]) * (in2[11] << 0) +
            ((u64) in[ 1]) * (in2[10] << 0) +
            ((u64) in[ 2]) * (in2[ 9] << 0) +
            ((u64) in[ 3]) * (in2[ 8] << 0) +
            ((u64) in[ 4]) * (in2[ 7] << 0) +
            ((u64) in[ 5]) * (in2[ 6] << 0) +
            ((u64) in[ 6]) * (in2[ 5] << 0) +
            ((u64) in[ 7]) * (in2[ 4] << 0) +
            ((u64) in[ 8]) * (in2[ 3] << 0) +
            ((u64) in[ 9]) * (in2[ 2] << 0) +
            ((u64) in[10]) * (in2[ 1] << 0) +
            ((u64) in[11]) * (in2[ 0] << 0);
  /* tmp[12] has the greatest value but doesn't overflow. See logic in
   * felem_square. */
  tmp[12] = ((u64) in[ 0]) * (in2[12] << 0) +
            ((u64) in[ 1]) * (in2[11] << 1) +
            ((u64) in[ 2]) * (in2[10] << 0) +
            ((u64) in[ 3]) * (in2[ 9] << 1) +
            ((u64) in[ 4]) * (in2[ 8] << 0) +
            ((u64) in[ 5]) * (in2[ 7] << 1) +
            ((u64) in[ 6]) * (in2[ 6] << 0) +
            ((u64) in[ 7]) * (in2[ 5] << 1) +
            ((u64) in[ 8]) * (in2[ 4] << 0) +
            ((u64) in[ 9]) * (in2[ 3] << 1) +
            ((u64) in[10]) * (in2[ 2] << 0) +
            ((u64) in[11]) * (in2[ 1] << 1) +
            ((u64) in[12]) * (in2[ 0] << 0);
  tmp[13] = ((u64) in[ 0]) * (in2[13] << 0) +
            ((u64) in[ 1]) * (in2[12] << 0) +
            ((u64) in[ 2]) * (in2[11] << 0) +
            ((u64) in[ 3]) * (in2[10] << 0) +
            ((u64) in[ 4]) * (in2[ 9] << 0) +
            ((u64) in[ 5]) * (in2[ 8] << 0) +
            ((u64) in[ 6]) * (in2[ 7] << 0) +
            ((u64) in[ 7]) * (in2[ 6] << 0) +
            ((u64) in[ 8]) * (in2[ 5] << 0) +
            ((u64) in[ 9]) * (in2[ 4] << 0) +
            ((u64) in[10]) * (in2[ 3] << 0) +
            ((u64) in[11]) * (in2[ 2] << 0) +
            ((u64) in[12]) * (in2[ 1] << 0) +
            ((u64) in[13]) * (in2[ 0] << 0);
  tmp[14] = ((u64) in[ 1]) * (in2[13] << 1) +
            ((u64) in[ 2]) * (in2[12] << 0) +
            ((u64) in[ 3]) * (in2[11] << 1) +
            ((u64) in[ 4]) * (in2[10] << 0) +
            ((u64) in[ 5]) * (in2[ 9] << 1) +
            ((u64) in[ 6]) * (in2[ 8] << 0) +
            ((u64) in[ 7]) * (in2[ 7] << 1) +
            ((u64) in[ 8]) * (in2[ 6] << 0) +
            ((u64) in[ 9]) * (in2[ 5] << 1) +
            ((u64) in[10]) * (in2[ 4] << 0) +
            ((u64) in[11]) * (in2[ 3] << 1) +
            ((u64) in[12]) * (in2[ 2] << 0) +
            ((u64) in[13]) * (in2[ 1] << 1);
  tmp[15] = ((u64) in[ 2]) * (in2[13] << 0) +
            ((u64) in[ 3]) * (in2[12] << 0) +
            ((u64) in[ 4]) * (in2[11] << 0) +
            ((u64) in[ 5]) * (in2[10] << 0) +
            ((u64) in[ 6]) * (in2[ 9] << 0) +
            ((u64) in[ 7]) * (in2[ 8] << 0) +
            ((u64) in[ 8]) * (in2[ 7] << 0) +
            ((u64) in[ 9]) * (in2[ 6] << 0) +
            ((u64) in[10]) * (in2[ 5] << 0) +
            ((u64) in[11]) * (in2[ 4] << 0) +
            ((u64) in[12]) * (in2[ 3] << 0) +
            ((u64) in[13]) * (in2[ 2] << 0);
  tmp[16] = ((u64) in[ 3]) * (in2[13] << 1) +
            ((u64) in[ 4]) * (in2[12] << 0) +
            ((u64) in[ 5]) * (in2[11] << 1) +
            ((u64) in[ 6]) * (in2[10] << 0) +
            ((u64) in[ 7]) * (in2[ 9] << 1) +
            ((u64) in[ 8]) * (in2[ 8] << 0) +
            ((u64) in[ 9]) * (in2[ 7] << 1) +
            ((u64) in[10]) * (in2[ 6] << 0) +
            ((u64) in[11]) * (in2[ 5] << 1) +
            ((u64) in[12]) * (in2[ 4] << 0) +
            ((u64) in[13]) * (in2[ 3] << 1);
  tmp[17] = ((u64) in[ 4]) * (in2[13] << 0) +
            ((u64) in[ 5]) * (in2[12] << 0) +
            ((u64) in[ 6]) * (in2[11] << 0) +
            ((u64) in[ 7]) * (in2[10] << 0) +
            ((u64) in[ 8]) * (in2[ 9] << 0) +
            ((u64) in[ 9]) * (in2[ 8] << 0) +
            ((u64) in[10]) * (in2[ 7] << 0) +
            ((u64) in[11]) * (in2[ 6] << 0) +
            ((u64) in[12]) * (in2[ 5] << 0) +
            ((u64) in[13]) * (in2[ 4] << 0);
  tmp[18] = ((u64) in[ 5]) * (in2[13] << 1) +
            ((u64) in[ 6]) * (in2[12] << 0) +
            ((u64) in[ 7]) * (in2[11] << 1) +
            ((u64) in[ 8]) * (in2[10] << 0) +
            ((u64) in[ 9]) * (in2[ 9] << 1) +
            ((u64) in[10]) * (in2[ 8] << 0) +
            ((u64) in[11]) * (in2[ 7] << 1) +
            ((u64) in[12]) * (in2[ 6] << 0) +
            ((u64) in[13]) * (in2[ 5] << 1);
  tmp[19] = ((u64) in[ 6]) * (in2[13] << 0) +
            ((u64) in[ 7]) * (in2[12] << 0) +
            ((u64) in[ 8]) * (in2[11] << 0) +
            ((u64) in[ 9]) * (in2[10] << 0) +
            ((u64) in[10]) * (in2[ 9] << 0) +
            ((u64) in[11]) * (in2[ 8] << 0) +
            ((u64) in[12]) * (in2[ 7] << 0) +
            ((u64) in[13]) * (in2[ 6] << 0);
  tmp[20] = ((u64) in[ 7]) * (in2[13] << 1) +
            ((u64) in[ 8]) * (in2[12] << 0) +
            ((u64) in[ 9]) * (in2[11] << 1) +
            ((u64) in[10]) * (in2[10] << 0) +
            ((u64) in[11]) * (in2[ 9] << 1) +
            ((u64) in[12]) * (in2[ 8] << 0) +
            ((u64) in[13]) * (in2[ 7] << 1);
  tmp[21] = ((u64) in[ 8]) * (in2[13] << 0) +
            ((u64) in[ 9]) * (in2[12] << 0) +
            ((u64) in[10]) * (in2[11] << 0) +
            ((u64) in[11]) * (in2[10] << 0) +
            ((u64) in[12]) * (in2[ 9] << 0) +
            ((u64) in[13]) * (in2[ 8] << 0);
  tmp[22] = ((u64) in[ 9]) * (in2[13] << 1) +
            ((u64) in[10]) * (in2[12] << 0) +
            ((u64) in[11]) * (in2[11] << 1) +
            ((u64) in[12]) * (in2[10] << 0) +
            ((u64) in[13]) * (in2[ 9] << 1);
  tmp[23] = ((u64) in[10]) * (in2[13] << 0) +
            ((u64) in[11]) * (in2[12] << 0) +
            ((u64) in[12]) * (in2[11] << 0) +
            ((u64) in[13]) * (in2[10] << 0);
  tmp[24] = ((u64) in[11]) * (in2[13] << 1) +
            ((u64) in[12]) * (in2[12] << 0) +
            ((u64) in[13]) * (in2[11] << 1);
  tmp[25] = ((u64) in[12]) * (in2[13] << 0) +
            ((u64) in[13]) * (in2[12] << 0);
  tmp[26] = ((u64) in[13]) * (in2[13] << 1);

  felem_reduce_degree(out, tmp);
}

static void felem_assign(felem out, const felem in) {
  memcpy(out, in, sizeof(felem));
}

/* felem_scalar_3 sets out=3*out.
 *
 * On entry: out[0,2,...] < 2**29, out[1,3,...] < 2**28.
 * On exit: out[0,2,...] < 2**29, out[1,3,...] < 2**28. */
static void felem_scalar_3(felem out) {
  limb carry = 0;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    out[i] *= 3;
    out[i] += carry;
    carry = out[i] >> 28;
    out[i] &= kBottom28Bits;

    i++;

    out[i] *= 3;
    out[i] += carry;
    carry = out[i] >> 27;
    out[i] &= kBottom27Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_scalar_4 sets out=4*out.
 *
 * On entry: out[0,2,...] < 2**29, out[1,3,...] < 2**28.
 * On exit: out[0,2,...] < 2**29, out[1,3,...] < 2**28. */
static void felem_scalar_4(felem out) {
  limb carry = 0, next_carry;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    next_carry = out[i] >> 26;
    out[i] <<= 2;
    out[i] &= kBottom28Bits;
    out[i] += carry;
    carry = next_carry + (out[i] >> 28);
    out[i] &= kBottom28Bits;

    i++;

    next_carry = out[i] >> 25;
    out[i] <<= 2;
    out[i] &= kBottom27Bits;
    out[i] += carry;
    carry = next_carry + (out[i] >> 27);
    out[i] &= kBottom27Bits;
  }

  felem_reduce_carry(out, carry);
}

/* felem_scalar_8 sets out=8*out.
 *
 * On entry: out[0,2,...] < 2**29, out[1,3,...] < 2**28.
 * On exit: out[0,2,...] < 2**29, out[1,3,...] < 2**28. */
static void felem_scalar_8(felem out) {
  limb carry = 0, next_carry;
  unsigned i;

  for (i = 0; i < NLIMBS; i++) {
    next_carry = out[i] >> 25;
    out[i] <<= 3;
    out[i] &= kBottom28Bits;
    out[i] += carry;
    carry = next_carry + (out[i] >> 28);
    out[i] &= kBottom28Bits;

    i++;

    next_carry = out[i] >> 24;
    out[i] <<= 3;
    out[i] &= kBottom27Bits;
    out[i] += carry;
    carry = next_carry + (out[i] >> 27);
    out[i] &= kBottom27Bits;
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
      carry = tmp[i] >> 28;
      tmp[i] &= kBottom28Bits;

      i++;

      tmp[i] += carry;
      carry = tmp[i] >> 27;
      tmp[i] &= kBottom27Bits;
    }

    felem_reduce_carry(tmp, carry);
  } while (carry);

  /* tmp < 2**385, so the only possible zero values are 0, p and 2p. */
  return memcmp(tmp, kZero, sizeof(tmp)) == 0 ||
         memcmp(tmp, kP, sizeof(tmp)) == 0 ||
         memcmp(tmp, k2P, sizeof(tmp)) == 0;
}


/* Montgomery operations: */

#define kRDigits {2, 0xfffffffe, 0xffffffff, 1, 2, 0, 0, 0, 0, 0, 0, 0} // 2^385 mod p384.p

#define kRInvDigits {0x80000003, 0x7ffffff0, 0xffffffec, 0xfffffff5, 0xfffffffe, 0x7ffffffd, 0x7ffffffd, 0x7ffffffe, 1, 6, 10, 10}  // 1 / 2^385 mod p384.p

static const cryptonite_p384_int kR = { kRDigits };
static const cryptonite_p384_int kRInv = { kRInvDigits };

/* to_montgomery sets out = R*in. */
static void to_montgomery(felem out, const cryptonite_p384_int* in) {
  cryptonite_p384_int in_shifted;
  int i;

  cryptonite_p384_init(&in_shifted);
  cryptonite_p384_modmul(&cryptonite_SECP384r1_p, in, 0, &kR, &in_shifted);

  for (i = 0; i < NLIMBS; i++) {
    if ((i & 1) == 0) {
      out[i] = P384_DIGIT(&in_shifted, 0) & kBottom28Bits;
      cryptonite_p384_shr(&in_shifted, 28, &in_shifted);
    } else {
      out[i] = P384_DIGIT(&in_shifted, 0) & kBottom27Bits;
      cryptonite_p384_shr(&in_shifted, 27, &in_shifted);
    }
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
    if ((i & 1) == 0) {
      top = cryptonite_p384_shl(&result, 28, &tmp);
    } else {
      top = cryptonite_p384_shl(&result, 27, &tmp);
    }
    top += cryptonite_p384_add_d(&tmp, in[i], &result);
  }

  cryptonite_p384_modmul(&cryptonite_SECP384r1_p, &kRInv, top, &result, out);

  cryptonite_p384_clear(&result);
  cryptonite_p384_clear(&tmp);
}
