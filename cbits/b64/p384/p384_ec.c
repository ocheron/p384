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

// This is an implementation of the P384 elliptic curve group with 64-bit
// words.
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
/* kPrecomputed contains precomputed values to aid the calculation of scalar
 * multiples of the base point, G. It's actually two, equal length, tables
 * concatenated.
 *
 * The first table contains (x,y) felem pairs for 16 multiples of the base
 * point, G.
 *
 *   Index  |  Index (binary) | Value
 *       0  |           0000  | 0G (all zeros, omitted)
 *       1  |           0001  | G
 *       2  |           0010  | 2**96G
 *       3  |           0011  | 2**96G + G
 *       4  |           0100  | 2**192G
 *       5  |           0101  | 2**192G + G
 *       6  |           0110  | 2**192G + 2**96G
 *       7  |           0111  | 2**192G + 2**96G + G
 *       8  |           1000  | 2**288G
 *       9  |           1001  | 2**288G + G
 *      10  |           1010  | 2**288G + 2**96G
 *      11  |           1011  | 2**288G + 2**96G + G
 *      12  |           1100  | 2**288G + 2**192G
 *      13  |           1101  | 2**288G + 2**192G + G
 *      14  |           1110  | 2**288G + 2**192G + 2**96G
 *      15  |           1111  | 2**288G + 2**192G + 2**96G + G
 *
 * The second table follows the same style, but the terms are 2**48G,
 * 2**144G, 2**240G, 2**336G.
 *
 * This is ~3KB of data. */
static const limb kPrecomputed[NLIMBS * 2 * 15 * 2] = {
  0x20eacc93816a50, 0x638a835b38e0f7, 0x62a0da6b71071b, 0x1a30eff879c3af,
  0x5bc56c8a90d08b, 0x44e04bfdc8d853, 0x269d56e114cf0a, 0x87b5a960749fc,
  0x22fdeed2a6b08c, 0x31741d82850dfd, 0xf4ffd98bade75, 0x350818d86a432d,
  0x7a776000898e5a, 0x15bc55e12d0ae2, 0x1018afe4dfddf2, 0x1a50e838490091,
  0x1939f15e3e18d1, 0x6f1ed4c735002c, 0x291d11885d38a7, 0xc80a2eafd9fd2,
  0x352817a1c54bc3, 0x62748c6e8a6dfd, 0x2eb162a7c3afd7, 0x61b9193b44e90c,
  0x76e8c1830f36bc, 0x16ecd8a62f662a, 0x373bc755e9a6ef, 0x8be249859f1ea,
  0x4dc5cc693bba1, 0x7be86cbf094045, 0x7600ba538f88b, 0x458466ff36b48,
  0xc0929e97bcec3, 0x248bcbb6db4160, 0x56e3ae88cefe5, 0x33a12f6fab4f9c,
  0x57968d1047a698, 0x386d25a77c3a13, 0x7901d8f5403e04, 0x62e1e5d755fb2e,
  0xd9798faf3a9d1, 0x951b4a23fcec0, 0x40bbb5f3f7ccf, 0x2e0ffdca3910de,
  0x6341700792257e, 0x14d5423dbcec06, 0x48c7de5428b862, 0x42a807661d1e94,
  0x3e049ad8beb8bd, 0x27789ea9a03f2b, 0x7aa45582b4d259, 0x657c71fa00d541,
  0x6fe16ef77943d, 0x7fb9ee0ee9421d, 0x725ad8b9bc6fe7, 0x53979cf2c43a2,
  0x5bc9b446838684, 0x3953a9c11089ce, 0x41ba0e779ee993, 0x1e61549336c7d9,
  0x47dfa3d5f401ab, 0x79334fb624af66, 0x1fd793662e363, 0x7c5f9e608bf158,
  0x54c85d3c79cc21, 0x47f057cd38a532, 0x4dc935b2cf84f2, 0x3912bbbfaf5085,
  0x731303c45eda4a, 0x1ab2b96b2645e7, 0x610c0e7e7646de, 0x50760788876bea,
  0x71c93da140cf4e, 0x550f1f6f3f6571, 0x4c5e086915266e, 0x2fdc59ee65aa17,
  0x316a1bacbfaa29, 0x3fd73ce52ab24d, 0x587fb7de0d4f61, 0x64e51b5ace2052,
  0x22da016389668e, 0x264a80a57e3434, 0x7cef7effdcbd82, 0xa728794711104,
  0x65cb6660c5d15e, 0xdd7a28f4da642, 0x5900edbd8d42b9, 0x6651aa23fe1b00,
  0x215afd24dbde1d, 0x1d1950b26fae6c, 0x4c7184dd17e5f, 0x3bdd67ffe3ac7e,
  0x202882ff4dd1de, 0x5c3b47bcb91e87, 0x79528568452bb3, 0x47f559eeb769a3,
  0x14e3f9ad000a7a, 0x95e9f20409b9d, 0x1a69c22d2e79e8, 0x22df93cd3dc1c,
  0x4af5c569490577, 0x6a45dda269af9b, 0x683c1bbc1406d4, 0x4aa862d4a398f7,
  0x1e638d951306f, 0x4cee1440d63baf, 0x70487499d74c92, 0xcb4222196dfd4,
  0x31a6cf073c1e2a, 0x728a86cc0ab1a2, 0x736c0a2720cbb9, 0x13577d80e36c6e,
  0x28c9680356a48a, 0x2db712364ffee8, 0x649d693964dc68, 0x69fdc77939867d,
  0x5517b7d7c10bd5, 0x385ceb9440e253, 0x3a07e44d1cd611, 0x51614551c47647,
  0x48bd84c4134178, 0x458513206d1a93, 0x1bb37c3f4667a1, 0x4307558e94e5c9,
  0x3ade7dcd3c3a07, 0x1fff2db61fece0, 0x1e524400c47e76, 0x44457ca7affc0f,
  0x3c055341184ae3, 0x458c0b042d7224, 0x3d8400898f742e, 0x27f298bdfbc256,
  0x2057155bfc6549, 0xa6ef4524f6205, 0x1a85700c5dc6e3, 0x6e10b52035cc54,
  0x18d330004908f9, 0x28e7368474e752, 0x25d8d2c3fc782e, 0x314ef39296b4fb,
  0x1a2800086b5e09, 0x6c79fb064b69d1, 0x119b6e2a16f92a, 0x36a68a81f17dc1,
  0x1943cb921854ec, 0x16a58327adddc1, 0xef4678f37d9eb, 0x1fdc19a23a7a0d,
  0xc51e7ad4b1f18, 0x79035848a63371, 0x191aa4d743c0f5, 0x7b78485eab7584,
  0x4733bf1f23fffa, 0x2a7d3040f37476, 0x7b6c7230d0630d, 0x509577313aa619,
  0x76a7873df3dae7, 0x2779f7ecc9a7ff, 0x4bde4f8afee38f, 0x20241dd01e75ac,
  0x8757481da040b, 0x555cbc1dc3f9d6, 0x6893a1b0687f7c, 0x3650c9f6f9ff8e,
  0x49b9d6a80f587d, 0x406074ad2aa47b, 0x7bdee102402164, 0xf7d26fe5d36de,
  0x3071f2c0a8002b, 0x651d0e41df73ef, 0x356b0c89256191, 0x4a62ea88b1fb9e,
  0x401ff2c2488181, 0x10e6b66d4b0b6f, 0x3a955d50d70cbb, 0x5131285958655a,
  0x79098aa63e4743, 0x793b7aae5efdbc, 0x2d23e1265452ec, 0x30de1b63581a4f,
  0x1f7da317dab792, 0x1c4d61bdc16719, 0x2d0cdb7153d192, 0xee16ee0247b36,
  0x1822d9e69508cb, 0xf36504c7f90d5, 0x6ea38eab4e56b0, 0x7791be2ce64874,
  0x25ffee48a9e0c9, 0x2b8092712aa9cf, 0x1d55de89af9b34, 0x5ea0ecb85a9e3,
  0x2b176c07960237, 0x1013bbc2c8e162, 0x4795ae845d5032, 0x316d9ae1f21afd,
  0x3c9556c651c67e, 0x60aebe04db475c, 0x7c36ab918aa433, 0x651a96807a4995,
  0x76dbe3e14b7a2, 0x4d697716c91da0, 0x2e2c3e5e216ed4, 0x59b66475d16981,
  0x6630c4cc44e0ad, 0x12ebf4b0a7368a, 0x4a8c05d4a23b2d, 0x1d05d27c8054ce,
  0x19516b2539b69f, 0x35cfc140f231ea, 0xc8ea65618a6b6, 0x254dc1418a58a6,
  0x210b55cd6486eb, 0x612d76a038cd6b, 0xf7b67bf36f6f7, 0x2244fd365e17cd,
  0x11162e4e09f4a2, 0x1cf2de4d01b8c8, 0x72dd60d4905d7e, 0x56883a05c09073,
  0x337dee6254b5d8, 0x448f87171df6a, 0x133da230b8653c, 0x3dae3af9b612de,
  0x997671277345a, 0x182c0214317556, 0x33ef96a1ec1063, 0x109e8014126d82,
  0x65e39bab777e00, 0x36616e4bb8ce05, 0x304ea7c9f98a18, 0xb340fd5b5f3ac,
  0x4db03c497ec078, 0xab079073b8732, 0x2af3a9ad622075, 0x5c29d4b29135cf,
  0x125edc38bd992e, 0x6e81b80bb6841, 0x6c23e8beb7bea7, 0x469f62c469b701,
  0x78e2771ca62e99, 0x25878d158965da, 0x2604b7517d7ceb, 0x62ebb3028620b7,
  0x27951c4cd491f5, 0x192502a49fa091, 0x6d682eec0977e6, 0x764d5ceaa020df,
  0x7ef044eb8ddf8c, 0x6ccc4a714996cf, 0x19424ab087c8c8, 0x148ce9c285b378,
  0x4d6edbc78c8f7, 0x64e833c14d2301, 0x18b96069f1fe5e, 0x675473731d312e,
  0x7dcc2be93fbcdd, 0x7ee2554c3c1b69, 0x27940d857459d2, 0x292e6983714a87,
  0x169ec20374c3f4, 0x3b29c8467e0d31, 0x202a278e2baae0, 0x371f187a0286d7,
  0x25e834088b9ec8, 0x3ee13874ebf609, 0x20861df8295690, 0x7d3c99c1a9d139,
  0x466440ffb0cadb, 0x145013d2fe8a22, 0x42c576372d1c5b, 0x52a4daa95e52e4,
  0x27dbb35b9b273a, 0x72779363c3feff, 0x572d393c9a444f, 0x451584f0174b75,
  0x58e3ff8ff754bf, 0x18160b1e27939c, 0x2cedd5cd1bc59e, 0x2aa1006dd43349,
  0x33eb50e46f9580, 0x56750d619e5173, 0x274a7b62749f85, 0x62782d34384a76,
  0xc02b0609da576, 0x43c2e36e2cf378, 0x219b6ea9aedf0c, 0x86aa625568e75,
  0x49d8f97b41195d, 0x610c84d52418e3, 0x1202ddb3e78678, 0x7cc6a956fc09f3,
  0x2f899234819a5d, 0x2a13e8c20498cc, 0x69b86af3dfb8b0, 0x4da53fda376e39,
  0x669904b52a2b5e, 0x6783d0724e74c, 0x1b149c839fe847, 0x68a8131fc85f1c,
  0x208cce97f30d0c, 0x1347c05380bba4, 0x29af9f8ff6a74e, 0x6be15a6fc29af9,
  0x674529426ecf72, 0x7ea32cf04ebe9f, 0x7118c672732748, 0xf02d016c40247,
  0xfbafa27366472, 0x939360ceeba1f, 0x44fff800ac5abc, 0x9eaf1abcbc487,
  0x74f11ff9df172, 0x7b66417d3bbc51, 0x106ea5170ae5f, 0x52d3d9460dad2a,
  0x32b6e4f2bd8328, 0x3c3f5371cefca0, 0x18c4fe567f7fab, 0x1723c1a1dc21ff,
  0x2d3191a1e6b067, 0x25a752863e8ebd, 0x335d8f47c8e259, 0x5db50f0663bb5b,
  0x398df5ec57e541, 0x8bfef3e6d8318, 0x1db8fdaaf5fe7b, 0x45dca9917bb3d1,
  0x2a731e85ae5d8a, 0x1cf4389ddc1d9f, 0x18cf4e0fba3a63, 0x4535a2af487809,
  0x7658c063b87907, 0x666d5979a7b2d8, 0x4d9c875bf9c1e0, 0x390d3931ad33b8,
  0x1059d9367ea068, 0x116b3679a3f461, 0x34aba3791cb16a, 0xc94a4b266fb1d,
  0x14b6d8cd5bcb4b, 0x2bb6ef6a09bb5a, 0x2b32526bd586b, 0x29fca204bc65f8,
  0x3afea5b7c94af3, 0x118ac9518b0d2d, 0x905517d88a07e, 0x81cebb3b29bd3,
  0x5325aed00417f5, 0xd8623d17403ed, 0x99fd8965c08b, 0x4db2c70175304,
  0x4452450408daf, 0x211bb1a53ae409, 0x749d4e7f6532bd, 0x17cc81215c0f64,
  0x26722ef41dfe45, 0x6952fc856620dd, 0x18c4da122d3ebf, 0x376bb120e8834e,
  0x4c3f6cfeda837a, 0x3151141b5e26d, 0x68c66741274f68, 0x3c33e358ec849d,
  0xba22c283a2c38, 0x383a4f13b45d4a, 0x23e1b0c3f33e69, 0x52584ca12c62a6,
  0x77ad3ea652a73d, 0x42b131ddf110be, 0x83ef3bb0defe2, 0x6db98ad2d7dd7b,
  0x7e58a196854665, 0xcec439581f157, 0x63c17cc0e0a9da, 0x18cf8bc6af47b4,
  0x3634c7f7f63857, 0x2225df7ebcb863, 0x41a2a45951e5fc, 0x2521246f507c69,
  0x2ac6ff01ab0b20, 0x78e48636dae29a, 0x791cb34c2b7d44, 0x3f2ef6d11de6b5,
  0xe383318167561, 0x56a98d32d33696, 0x29b48e785fa178, 0x775031d415a84e,
  0x6a22e02728165f, 0x5c3bed6bcc13b6, 0x7e84a04e416c9b, 0x3dcfb9121ca48,
  0x3b42ce702a753b, 0xeb47a0fb3c2aa, 0x70db309c2924ff, 0x434de114c18f8,
  0x35d2cc3849b567, 0x724f65cf0e8a0f, 0x24cdd500c13aa7, 0x7a331d984d63c7,
  0x61c9d4588091d, 0x31b156efd49747, 0x3962853386e52f, 0x5b6c063d1ed2b8,
  0x2b37b0abc4daab, 0x3e7eda6314e7ba, 0x434330fff414be, 0x40b18ff84278d,
  0x2b63a7088fa593, 0x7abebaf264acbc, 0x3b6ea95e88bf4e, 0x3a912313f74933,
  0x5898abea22837, 0x4d62b2e5d3327a, 0x5f921797b2f88a, 0x5fec1f0d0961e2,
  0x3b8c83ba673560, 0x7c71cd7c47f058, 0x66d02c4ea5902e, 0x33775019d68b9c
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

#define NTH_DOUBLE(out, n, in) \
  felem_square(out, in); \
  for (i = 0; i < n - 1; i++) \
    felem_square(out, out);

#define NTH_DOUBLE_ADD(out, n, a, in) \
  NTH_DOUBLE(out, n, in); \
  felem_mul(out, out, a);

/* felem_inv calculates |out| = |in|^{-1}
 *
 * Based on Fermat's Little Theorem:
 *   a^p = a (mod p)
 *   a^{p-1} = 1 (mod p)
 *   a^{p-2} = a^{-1} (mod p)
 */
static void felem_inv(felem out, const felem in) {
  felem x2, x3, x6, x12, x15, x30, x60, x120;
  int i;

  // https://briansmith.org/ecc-inversion-addition-chains-01#p384_field_inversion
  NTH_DOUBLE_ADD(x2,        1, in,   in);
  NTH_DOUBLE_ADD(x3,        1, in,   x2);
  NTH_DOUBLE_ADD(x6,        3, x3,   x3);
  NTH_DOUBLE_ADD(x12,       6, x6,   x6);
  NTH_DOUBLE_ADD(x15,       3, x3,   x12);
  NTH_DOUBLE_ADD(x30,      15, x15,  x15);
  NTH_DOUBLE_ADD(x60,      30, x30,  x30);
  NTH_DOUBLE_ADD(x120,     60, x60,  x60);
  NTH_DOUBLE_ADD(out,     120, x120, x120);
  NTH_DOUBLE_ADD(out,      15, x15,  out);
  NTH_DOUBLE_ADD(out,  1 + 30, x30,  out);
  NTH_DOUBLE_ADD(out,       2, x2,   out);
  NTH_DOUBLE_ADD(out, 64 + 30, x30,  out);
  NTH_DOUBLE    (out,       2,       out);

  //2^384 - 2^128 - 2^96 + 2^32 - 3
  felem_mul(out, out, in);
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


/* Group operations:
 *
 * Elements of the elliptic curve group are represented in Jacobian
 * coordinates: (x, y, z). An affine point (x', y') is x'=x/z**2, y'=y/z**3 in
 * Jacobian form. */

/* point_double sets {x_out,y_out,z_out} = 2*{x,y,z}.
 *
 * See http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l */
static void point_double(felem x_out, felem y_out, felem z_out, const felem x,
                         const felem y, const felem z) {
  felem delta, gamma, alpha, beta, tmp, tmp2;

  felem_square(delta, z);
  felem_square(gamma, y);
  felem_mul(beta, x, gamma);

  felem_sum(tmp, x, delta);
  felem_diff(tmp2, x, delta);
  felem_mul(alpha, tmp, tmp2);
  felem_scalar_3(alpha);

  felem_sum(tmp, y, z);
  felem_square(tmp, tmp);
  felem_diff(tmp, tmp, gamma);
  felem_diff(z_out, tmp, delta);

  felem_scalar_4(beta);
  felem_square(x_out, alpha);
  felem_diff(x_out, x_out, beta);
  felem_diff(x_out, x_out, beta);

  felem_diff(tmp, beta, x_out);
  felem_mul(tmp, alpha, tmp);
  felem_square(tmp2, gamma);
  felem_scalar_8(tmp2);
  felem_diff(y_out, tmp, tmp2);
}

/* point_add_mixed sets {x_out,y_out,z_out} = {x1,y1,z1} + {x2,y2,1}.
 * (i.e. the second point is affine.)
 *
 * See http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
 *
 * Note that this function does not handle P+P, infinity+P nor P+infinity
 * correctly. */
static void point_add_mixed(felem x_out, felem y_out, felem z_out,
                            const felem x1, const felem y1, const felem z1,
                            const felem x2, const felem y2) {
  felem z1z1, z1z1z1, s2, u2, h, i, j, r, rr, v, tmp;

  felem_square(z1z1, z1);
  felem_sum(tmp, z1, z1);

  felem_mul(u2, x2, z1z1);
  felem_mul(z1z1z1, z1, z1z1);
  felem_mul(s2, y2, z1z1z1);
  felem_diff(h, u2, x1);
  felem_sum(i, h, h);
  felem_square(i, i);
  felem_mul(j, h, i);
  felem_diff(r, s2, y1);
  felem_sum(r, r, r);
  felem_mul(v, x1, i);

  felem_mul(z_out, tmp, h);
  felem_square(rr, r);
  felem_diff(x_out, rr, j);
  felem_diff(x_out, x_out, v);
  felem_diff(x_out, x_out, v);

  felem_diff(tmp, v, x_out);
  felem_mul(y_out, tmp, r);
  felem_mul(tmp, y1, j);
  felem_diff(y_out, y_out, tmp);
  felem_diff(y_out, y_out, tmp);
}

/* point_add sets {x_out,y_out,z_out} = {x1,y1,z1} + {x2,y2,z2}.
 *
 * See http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
 *
 * Note that this function does not handle P+P, infinity+P nor P+infinity
 * correctly. */
static void point_add(felem x_out, felem y_out, felem z_out, const felem x1,
                      const felem y1, const felem z1, const felem x2,
                      const felem y2, const felem z2) {
  felem z1z1, z1z1z1, z2z2, z2z2z2, s1, s2, u1, u2, h, i, j, r, rr, v, tmp;

  felem_square(z1z1, z1);
  felem_square(z2z2, z2);
  felem_mul(u1, x1, z2z2);

  felem_sum(tmp, z1, z2);
  felem_square(tmp, tmp);
  felem_diff(tmp, tmp, z1z1);
  felem_diff(tmp, tmp, z2z2);

  felem_mul(z2z2z2, z2, z2z2);
  felem_mul(s1, y1, z2z2z2);

  felem_mul(u2, x2, z1z1);
  felem_mul(z1z1z1, z1, z1z1);
  felem_mul(s2, y2, z1z1z1);
  felem_diff(h, u2, u1);
  felem_sum(i, h, h);
  felem_square(i, i);
  felem_mul(j, h, i);
  felem_diff(r, s2, s1);
  felem_sum(r, r, r);
  felem_mul(v, u1, i);

  felem_mul(z_out, tmp, h);
  felem_square(rr, r);
  felem_diff(x_out, rr, j);
  felem_diff(x_out, x_out, v);
  felem_diff(x_out, x_out, v);

  felem_diff(tmp, v, x_out);
  felem_mul(y_out, tmp, r);
  felem_mul(tmp, s1, j);
  felem_diff(y_out, y_out, tmp);
  felem_diff(y_out, y_out, tmp);
}

/* point_add_or_double_vartime sets {x_out,y_out,z_out} = {x1,y1,z1} +
 *                                                        {x2,y2,z2}.
 *
 * See http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
 *
 * This function handles the case where {x1,y1,z1}={x2,y2,z2}. */
static void point_add_or_double_vartime(
    felem x_out, felem y_out, felem z_out, const felem x1, const felem y1,
    const felem z1, const felem x2, const felem y2, const felem z2) {
  felem z1z1, z1z1z1, z2z2, z2z2z2, s1, s2, u1, u2, h, i, j, r, rr, v, tmp;
  char x_equal, y_equal;

  felem_square(z1z1, z1);
  felem_square(z2z2, z2);
  felem_mul(u1, x1, z2z2);

  felem_sum(tmp, z1, z2);
  felem_square(tmp, tmp);
  felem_diff(tmp, tmp, z1z1);
  felem_diff(tmp, tmp, z2z2);

  felem_mul(z2z2z2, z2, z2z2);
  felem_mul(s1, y1, z2z2z2);

  felem_mul(u2, x2, z1z1);
  felem_mul(z1z1z1, z1, z1z1);
  felem_mul(s2, y2, z1z1z1);
  felem_diff(h, u2, u1);
  x_equal = felem_is_zero_vartime(h);
  felem_sum(i, h, h);
  felem_square(i, i);
  felem_mul(j, h, i);
  felem_diff(r, s2, s1);
  y_equal = felem_is_zero_vartime(r);
  if (x_equal && y_equal) {
    point_double(x_out, y_out, z_out, x1, y1, z1);
    return;
  }
  felem_sum(r, r, r);
  felem_mul(v, u1, i);

  felem_mul(z_out, tmp, h);
  felem_square(rr, r);
  felem_diff(x_out, rr, j);
  felem_diff(x_out, x_out, v);
  felem_diff(x_out, x_out, v);

  felem_diff(tmp, v, x_out);
  felem_mul(y_out, tmp, r);
  felem_mul(tmp, s1, j);
  felem_diff(y_out, y_out, tmp);
  felem_diff(y_out, y_out, tmp);
}

/* copy_conditional sets out=in if mask = 0xffffffffffffffff in constant time.
 *
 * On entry: mask is either 0 or 0xffffffffffffffff. */
static void copy_conditional(felem out, const felem in, limb mask) {
  int i;

  for (i = 0; i < NLIMBS; i++) {
    const limb tmp = mask & (in[i] ^ out[i]);
    out[i] ^= tmp;
  }
}

/* select_affine_point sets {out_x,out_y} to the index'th entry of table.
 * On entry: index < 16, table[0] must be zero. */
static void select_affine_point(felem out_x, felem out_y, const limb* table,
                                limb index) {
  limb i, j;

  memset(out_x, 0, sizeof(felem));
  memset(out_y, 0, sizeof(felem));

  for (i = 1; i < 16; i++) {
    limb mask = i ^ index;
    mask |= mask >> 2;
    mask |= mask >> 1;
    mask &= 1;
    mask--;
    for (j = 0; j < NLIMBS; j++, table++) {
      out_x[j] |= *table & mask;
    }
    for (j = 0; j < NLIMBS; j++, table++) {
      out_y[j] |= *table & mask;
    }
  }
}

/* select_jacobian_point sets {out_x,out_y,out_z} to the index'th entry of
 * table. On entry: index < 16, table[0] must be zero. */
static void select_jacobian_point(felem out_x, felem out_y, felem out_z,
                                  const limb* table, limb index) {
  limb i, j;

  memset(out_x, 0, sizeof(felem));
  memset(out_y, 0, sizeof(felem));
  memset(out_z, 0, sizeof(felem));

  /* The implicit value at index 0 is all zero. We don't need to perform that
   * iteration of the loop because we already set out_* to zero. */
  table += 3 * NLIMBS;

  // Hit all entries to obscure cache profiling.
  for (i = 1; i < 16; i++) {
    limb mask = i ^ index;
    mask |= mask >> 2;
    mask |= mask >> 1;
    mask &= 1;
    mask--;
    for (j = 0; j < NLIMBS; j++, table++) {
      out_x[j] |= *table & mask;
    }
    for (j = 0; j < NLIMBS; j++, table++) {
      out_y[j] |= *table & mask;
    }
    for (j = 0; j < NLIMBS; j++, table++) {
      out_z[j] |= *table & mask;
    }
  }
}

/* scalar_base_mult sets {nx,ny,nz} = scalar*G where scalar is a little-endian
 * number. Note that the value of scalar must be less than the order of the
 * group. */
static void scalar_base_mult(felem nx, felem ny, felem nz,
                             const cryptonite_p384_int* scalar) {
  int i, j;
  limb n_is_infinity_mask = -1, p_is_noninfinite_mask, mask;
  u32 table_offset;

  felem px, py;
  felem tx, ty, tz;

  memset(nx, 0, sizeof(felem));
  memset(ny, 0, sizeof(felem));
  memset(nz, 0, sizeof(felem));

  /* The loop adds bits at positions 0, 96, 192 and 288, followed by
   * positions 48,144,240 and 336 and does this 48 times. */
  for (i = 0; i < 48; i++) {
    if (i) {
      point_double(nx, ny, nz, nx, ny, nz);
    }
    table_offset = 0;
    for (j = 0; j <= 48; j += 48) {
      char bit0 = cryptonite_p384_get_bit(scalar, 47 - i + j);
      char bit1 = cryptonite_p384_get_bit(scalar, 143 - i + j);
      char bit2 = cryptonite_p384_get_bit(scalar, 239 - i + j);
      char bit3 = cryptonite_p384_get_bit(scalar, 335 - i + j);
      limb index = bit0 | (bit1 << 1) | (bit2 << 2) | (bit3 << 3);

      select_affine_point(px, py, kPrecomputed + table_offset, index);
      table_offset += 30 * NLIMBS;

      /* Since scalar is less than the order of the group, we know that
       * {nx,ny,nz} != {px,py,1}, unless both are zero, which we handle
       * below. */
      point_add_mixed(tx, ty, tz, nx, ny, nz, px, py);
      /* The result of point_add_mixed is incorrect if {nx,ny,nz} is zero
       * (a.k.a.  the point at infinity). We handle that situation by
       * copying the point from the table. */
      copy_conditional(nx, px, n_is_infinity_mask);
      copy_conditional(ny, py, n_is_infinity_mask);
      copy_conditional(nz, kOne, n_is_infinity_mask);

      /* Equally, the result is also wrong if the point from the table is
       * zero, which happens when the index is zero. We handle that by
       * only copying from {tx,ty,tz} to {nx,ny,nz} if index != 0. */
      p_is_noninfinite_mask = NON_ZERO_TO_ALL_ONES(index);
      mask = p_is_noninfinite_mask & ~n_is_infinity_mask;
      copy_conditional(nx, tx, mask);
      copy_conditional(ny, ty, mask);
      copy_conditional(nz, tz, mask);
      /* If p was not zero, then n is now non-zero. */
      n_is_infinity_mask &= ~p_is_noninfinite_mask;
    }
  }
}

/* point_to_affine converts a Jacobian point to an affine point. If the input
 * is the point at infinity then it returns (0, 0) in constant time. */
static void point_to_affine(felem x_out, felem y_out, const felem nx,
                            const felem ny, const felem nz) {
  felem z_inv, z_inv_sq;
  felem_inv(z_inv, nz);
  felem_square(z_inv_sq, z_inv);
  felem_mul(x_out, nx, z_inv_sq);
  felem_mul(z_inv, z_inv, z_inv_sq);
  felem_mul(y_out, ny, z_inv);
}

/* scalar_base_mult sets {nx,ny,nz} = scalar*{x,y}. */
static void scalar_mult(felem nx, felem ny, felem nz, const felem x,
                        const felem y, const cryptonite_p384_int* scalar) {
  int i;
  felem px, py, pz, tx, ty, tz;
  felem precomp[16][3];
  limb n_is_infinity_mask, index, p_is_noninfinite_mask, mask;

  /* We precompute 0,1,2,... times {x,y}. */
  memset(precomp, 0, sizeof(felem) * 3);
  memcpy(&precomp[1][0], x, sizeof(felem));
  memcpy(&precomp[1][1], y, sizeof(felem));
  memcpy(&precomp[1][2], kOne, sizeof(felem));

  for (i = 2; i < 16; i += 2) {
    point_double(precomp[i][0], precomp[i][1], precomp[i][2],
                 precomp[i / 2][0], precomp[i / 2][1], precomp[i / 2][2]);

    point_add_mixed(precomp[i + 1][0], precomp[i + 1][1], precomp[i + 1][2],
                    precomp[i][0], precomp[i][1], precomp[i][2], x, y);
  }

  memset(nx, 0, sizeof(felem));
  memset(ny, 0, sizeof(felem));
  memset(nz, 0, sizeof(felem));
  n_is_infinity_mask = -1;

  /* We add in a window of four bits each iteration and do this 64 times. */
  for (i = 0; i < 384; i += 4) {
    if (i) {
      point_double(nx, ny, nz, nx, ny, nz);
      point_double(nx, ny, nz, nx, ny, nz);
      point_double(nx, ny, nz, nx, ny, nz);
      point_double(nx, ny, nz, nx, ny, nz);
    }

    index = (cryptonite_p384_get_bit(scalar, 383 - i - 0) << 3) |
            (cryptonite_p384_get_bit(scalar, 383 - i - 1) << 2) |
            (cryptonite_p384_get_bit(scalar, 383 - i - 2) << 1) |
            cryptonite_p384_get_bit(scalar, 383 - i - 3);

    /* See the comments in scalar_base_mult about handling infinities. */
    select_jacobian_point(px, py, pz, precomp[0][0], index);
    point_add(tx, ty, tz, nx, ny, nz, px, py, pz);
    copy_conditional(nx, px, n_is_infinity_mask);
    copy_conditional(ny, py, n_is_infinity_mask);
    copy_conditional(nz, pz, n_is_infinity_mask);

    p_is_noninfinite_mask = NON_ZERO_TO_ALL_ONES(index);
    mask = p_is_noninfinite_mask & ~n_is_infinity_mask;

    copy_conditional(nx, tx, mask);
    copy_conditional(ny, ty, mask);
    copy_conditional(nz, tz, mask);
    n_is_infinity_mask &= ~p_is_noninfinite_mask;
  }
}

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

/* cryptonite_p384_base_point_mul sets {out_x,out_y} = nG, where n is < the
 * order of the group. */
void cryptonite_p384_base_point_mul(const cryptonite_p384_int* n, cryptonite_p384_int* out_x, cryptonite_p384_int* out_y) {
  felem x, y, z;

  scalar_base_mult(x, y, z, n);

  {
    felem x_affine, y_affine;

    point_to_affine(x_affine, y_affine, x, y, z);
    from_montgomery(out_x, x_affine);
    from_montgomery(out_y, y_affine);
  }
}

/* cryptonite_p384_points_mul_vartime sets {out_x,out_y} = n1*G + n2*{in_x,in_y}, where
 * n1 and n2 are < the order of the group.
 *
 * As indicated by the name, this function operates in variable time. This
 * is safe because it's used for signature validation which doesn't deal
 * with secrets. */
void cryptonite_p384_points_mul_vartime(
    const cryptonite_p384_int* n1, const cryptonite_p384_int* n2, const cryptonite_p384_int* in_x,
    const cryptonite_p384_int* in_y, cryptonite_p384_int* out_x, cryptonite_p384_int* out_y) {
  felem x1, y1, z1, x2, y2, z2, px, py;

  /* If both scalars are zero, then the result is the point at infinity. */
  if (cryptonite_p384_is_zero(n1) != 0 && cryptonite_p384_is_zero(n2) != 0) {
    cryptonite_p384_clear(out_x);
    cryptonite_p384_clear(out_y);
    return;
  }

  to_montgomery(px, in_x);
  to_montgomery(py, in_y);
  scalar_base_mult(x1, y1, z1, n1);
  scalar_mult(x2, y2, z2, px, py, n2);

  if (cryptonite_p384_is_zero(n2) != 0) {
    /* If n2 == 0, then {x2,y2,z2} is zero and the result is just
         * {x1,y1,z1}. */
  } else if (cryptonite_p384_is_zero(n1) != 0) {
    /* If n1 == 0, then {x1,y1,z1} is zero and the result is just
         * {x2,y2,z2}. */
    memcpy(x1, x2, sizeof(x2));
    memcpy(y1, y2, sizeof(y2));
    memcpy(z1, z2, sizeof(z2));
  } else {
    /* This function handles the case where {x1,y1,z1} == {x2,y2,z2}. */
    point_add_or_double_vartime(x1, y1, z1, x1, y1, z1, x2, y2, z2);
  }

  point_to_affine(px, py, x1, y1, z1);
  from_montgomery(out_x, px);
  from_montgomery(out_y, py);
}

/* this function is not part of the original source
   add 2 points together. so far untested.
   probably vartime, as it use point_add_or_double_vartime
 */
void cryptonite_p384e_point_add(
    const cryptonite_p384_int *in_x1, const cryptonite_p384_int *in_y1,
    const cryptonite_p384_int *in_x2, const cryptonite_p384_int *in_y2,
    cryptonite_p384_int *out_x, cryptonite_p384_int *out_y)
{
    felem x, y, z, px1, py1, px2, py2;

    to_montgomery(px1, in_x1);
    to_montgomery(py1, in_y1);
    to_montgomery(px2, in_x2);
    to_montgomery(py2, in_y2);

    point_add_or_double_vartime(x, y, z, px1, py1, kOne, px2, py2, kOne);

    point_to_affine(px1, py1, x, y, z);
    from_montgomery(out_x, px1);
    from_montgomery(out_y, py1);
}

/* this function is not part of the original source
   negate a point, i.e. (out_x, out_y) = (in_x, -in_y)
 */
void cryptonite_p384e_point_negate(
    const cryptonite_p384_int *in_x, const cryptonite_p384_int *in_y,
    cryptonite_p384_int *out_x, cryptonite_p384_int *out_y)
{
    memcpy(out_x, in_x, P384_NBYTES);
    cryptonite_p384_sub(&cryptonite_SECP384r1_p, in_y, out_y);
}
