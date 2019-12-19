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

// This is an implementation of the P384 elliptic curve group. It's written to
// be portable 32-bit, although it's still constant-time.
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
  0x3816a50, 0x20eacc9, 0xb38e0f7, 0x638a835, 0xb71071b, 0x62a0da6, 0x879c3af,
  0x1a30eff, 0xa90d08b, 0x5bc56c8, 0xdc8d853, 0x44e04bf, 0x114cf0a, 0x269d56e,
  0x60749fc, 0x87b5a9, 0x2a6b08c, 0x22fdeed, 0x2850dfd, 0x31741d8, 0x8bade75,
  0xf4ffd9, 0x86a432d, 0x350818d, 0x898e5a, 0x7a77600, 0x12d0ae2, 0x15bc55e,
  0x4dfddf2, 0x1018afe, 0x8490091, 0x1a50e83, 0xe3e18d1, 0x1939f15, 0x735002c,
  0x6f1ed4c, 0x85d38a7, 0x291d118, 0xafd9fd2, 0xc80a2e, 0x1c54bc3, 0x352817a,
  0xe8a6dfd, 0x62748c6, 0x7c3afd7, 0x2eb162a, 0xb44e90c, 0x61b9193, 0x30f36bc,
  0x76e8c18, 0x62f662a, 0x16ecd8a, 0x5e9a6ef, 0x373bc75, 0x859f1ea, 0x8be249,
  0x693bba1, 0x4dc5cc, 0xf094045, 0x7be86cb, 0x538f88b, 0x7600ba, 0xff36b48,
  0x458466, 0x97bcec3, 0xc0929e, 0x6db4160, 0x248bcbb, 0x88cefe5, 0x56e3ae,
  0xfab4f9c, 0x33a12f6, 0x47a698, 0x57968d1, 0x77c3a13, 0x386d25a, 0x5403e04,
  0x7901d8f, 0x755fb2e, 0x62e1e5d, 0xaf3a9d1, 0xd9798f, 0x23fcec0, 0x951b4a,
  0xf3f7ccf, 0x40bbb5, 0xa3910de, 0x2e0ffdc, 0x792257e, 0x6341700, 0xdbcec06,
  0x14d5423, 0x428b862, 0x48c7de5, 0x61d1e94, 0x42a8076, 0x8beb8bd, 0x3e049ad,
  0x9a03f2b, 0x27789ea, 0x2b4d259, 0x7aa4558, 0xa00d541, 0x657c71f, 0xf77943d,
  0x6fe16e, 0xee9421d, 0x7fb9ee0, 0x9bc6fe7, 0x725ad8b, 0xf2c43a2, 0x53979c,
  0x6838684, 0x5bc9b44, 0x11089ce, 0x3953a9c, 0x79ee993, 0x41ba0e7, 0x336c7d9,
  0x1e61549, 0x5f401ab, 0x47dfa3d, 0x624af66, 0x79334fb, 0x662e363, 0x1fd793,
  0x8bf158, 0x7c5f9e6, 0xc79cc21, 0x54c85d3, 0xd38a532, 0x47f057c, 0x2cf84f2,
  0x4dc935b, 0xfaf5085, 0x3912bbb, 0x45eda4a, 0x731303c, 0xb2645e7, 0x1ab2b96,
  0xe7646de, 0x610c0e7, 0x8876bea, 0x5076078, 0x140cf4e, 0x71c93da, 0xf3f6571,
  0x550f1f6, 0x915266e, 0x4c5e086, 0xe65aa17, 0x2fdc59e, 0xcbfaa29, 0x316a1ba,
  0x52ab24d, 0x3fd73ce, 0xe0d4f61, 0x587fb7d, 0xace2052, 0x64e51b5, 0x389668e,
  0x22da016, 0x57e3434, 0x264a80a, 0xfdcbd82, 0x7cef7ef, 0x4711104, 0xa72879,
  0xc5d15e, 0x65cb666, 0xf4da642, 0xdd7a28, 0xd8d42b9, 0x5900edb, 0x3fe1b00,
  0x6651aa2, 0x4dbde1d, 0x215afd2, 0x26fae6c, 0x1d1950b, 0xdd17e5f, 0x4c7184,
  0xfe3ac7e, 0x3bdd67f, 0xf4dd1de, 0x202882f, 0xcb91e87, 0x5c3b47b, 0x8452bb3,
  0x7952856, 0xeb769a3, 0x47f559e, 0xd000a7a, 0x14e3f9a, 0x409b9d, 0x95e9f2,
  0xd2e79e8, 0x1a69c22, 0xcd3dc1c, 0x22df93, 0x9490577, 0x4af5c56, 0x269af9b,
  0x6a45dda, 0xc1406d4, 0x683c1bb, 0x4a398f7, 0x4aa862d, 0x951306f, 0x1e638d,
  0xd63baf, 0x4cee144, 0x9d74c92, 0x7048749, 0x196dfd4, 0xcb4222, 0x73c1e2a,
  0x31a6cf0, 0xc0ab1a2, 0x728a86c, 0x720cbb9, 0x736c0a2, 0xe36c6e, 0x13577d8,
  0x356a48a, 0x28c9680, 0x64ffee8, 0x2db7123, 0x964dc68, 0x649d693, 0x939867d,
  0x69fdc77, 0x7c10bd5, 0x5517b7d, 0x440e253, 0x385ceb9, 0xd1cd611, 0x3a07e44,
  0x1c47647, 0x5161455, 0x4134178, 0x48bd84c, 0x6d1a93, 0x4585132, 0xf4667a1,
  0x1bb37c3, 0xe94e5c9, 0x4307558, 0xd3c3a07, 0x3ade7dc, 0x61fece0, 0x1fff2db,
  0xc47e76, 0x1e52440, 0x7affc0f, 0x44457ca, 0x1184ae3, 0x3c05534, 0x42d7224,
  0x458c0b0, 0x98f742e, 0x3d84008, 0xdfbc256, 0x27f298b, 0xbfc6549, 0x2057155,
  0x24f6205, 0xa6ef45, 0xc5dc6e3, 0x1a85700, 0x35cc54, 0x6e10b52, 0x4908f9,
  0x18d3300, 0x474e752, 0x28e7368, 0x3fc782e, 0x25d8d2c, 0x296b4fb, 0x314ef39,
  0x86b5e09, 0x1a28000, 0x64b69d1, 0x6c79fb0, 0xa16f92a, 0x119b6e2, 0x1f17dc1,
  0x36a68a8, 0x21854ec, 0x1943cb9, 0x7adddc1, 0x16a5832, 0xf37d9eb, 0xef4678,
  0x23a7a0d, 0x1fdc19a, 0xd4b1f18, 0xc51e7a, 0x8a63371, 0x7903584, 0x743c0f5,
  0x191aa4d, 0xeab7584, 0x7b78485, 0xf23fffa, 0x4733bf1, 0xf37476, 0x2a7d304,
  0xd0630d, 0x7b6c723, 0x13aa619, 0x5095773, 0xdf3dae7, 0x76a7873, 0xcc9a7ff,
  0x2779f7e, 0xafee38f, 0x4bde4f8, 0x1e75ac, 0x20241dd, 0x1da040b, 0x875748,
  0xdc3f9d6, 0x555cbc1, 0x687f7c, 0x6893a1b, 0x6f9ff8e, 0x3650c9f, 0x80f587d,
  0x49b9d6a, 0xd2aa47b, 0x406074a, 0x2402164, 0x7bdee10, 0xe5d36de, 0xf7d26f,
  0xa8002b, 0x3071f2c, 0x1df73ef, 0x651d0e4, 0x9256191, 0x356b0c8, 0x8b1fb9e,
  0x4a62ea8, 0x2488181, 0x401ff2c, 0xd4b0b6f, 0x10e6b66, 0xd70cbb, 0x3a955d5,
  0x958655a, 0x5131285, 0x63e4743, 0x79098aa, 0xe5efdbc, 0x793b7aa, 0x65452ec,
  0x2d23e12, 0x3581a4f, 0x30de1b6, 0x7dab792, 0x1f7da31, 0xdc16719, 0x1c4d61b,
  0x153d192, 0x2d0cdb7, 0x247b36, 0xee16ee, 0x69508cb, 0x1822d9e, 0xc7f90d5,
  0xf36504, 0xb4e56b0, 0x6ea38ea, 0xce64874, 0x7791be2, 0x8a9e0c9, 0x25ffee4,
  0x12aa9cf, 0x2b80927, 0x9af9b34, 0x1d55de8, 0xb85a9e3, 0x5ea0ec, 0x7960237,
  0x2b176c0, 0x2c8e162, 0x1013bbc, 0x45d5032, 0x4795ae8, 0x1f21afd, 0x316d9ae,
  0x651c67e, 0x3c9556c, 0x4db475c, 0x60aebe0, 0x18aa433, 0x7c36ab9, 0x7a4995,
  0x651a968, 0xe14b7a2, 0x76dbe3, 0x6c91da0, 0x4d69771, 0xe216ed4, 0x2e2c3e5,
  0x5d16981, 0x59b6647, 0xc44e0ad, 0x6630c4c, 0xa7368a, 0x12ebf4b, 0x4a23b2d,
  0x4a8c05d, 0xc8054ce, 0x1d05d27, 0x539b69f, 0x19516b2, 0xf231ea, 0x35cfc14,
  0x618a6b6, 0xc8ea65, 0x18a58a6, 0x254dc14, 0xd6486eb, 0x210b55c, 0x38cd6b,
  0x612d76a, 0xf36f6f7, 0xf7b67b, 0x65e17cd, 0x2244fd3, 0xe09f4a2, 0x11162e4,
  0xd01b8c8, 0x1cf2de4, 0x4905d7e, 0x72dd60d, 0x5c09073, 0x56883a0, 0x254b5d8,
  0x337dee6, 0x171df6a, 0x448f87, 0xb8653c, 0x133da23, 0x9b612de, 0x3dae3af,
  0x277345a, 0x997671, 0x4317556, 0x182c021, 0x1ec1063, 0x33ef96a, 0x4126d82,
  0x109e801, 0xb777e00, 0x65e39ba, 0xbb8ce05, 0x36616e4, 0x9f98a18, 0x304ea7c,
  0x5b5f3ac, 0xb340fd, 0x97ec078, 0x4db03c4, 0x73b8732, 0xab0790, 0xd622075,
  0x2af3a9a, 0x29135cf, 0x5c29d4b, 0x8bd992e, 0x125edc3, 0xbb6841, 0x6e81b8,
  0xeb7bea7, 0x6c23e8b, 0x469b701, 0x469f62c, 0xca62e99, 0x78e2771, 0x58965da,
  0x25878d1, 0x17d7ceb, 0x2604b75, 0x28620b7, 0x62ebb30, 0xcd491f5, 0x27951c4,
  0x49fa091, 0x192502a, 0xc0977e6, 0x6d682ee, 0xaa020df, 0x764d5ce, 0xb8ddf8c,
  0x7ef044e, 0x14996cf, 0x6ccc4a7, 0x87c8c8, 0x19424ab, 0x285b378, 0x148ce9c,
  0xc78c8f7, 0x4d6edb, 0x14d2301, 0x64e833c, 0x9f1fe5e, 0x18b9606, 0x31d312e,
  0x6754737, 0x93fbcdd, 0x7dcc2be, 0xc3c1b69, 0x7ee2554, 0x57459d2, 0x27940d8,
  0x3714a87, 0x292e698, 0x374c3f4, 0x169ec20, 0x67e0d31, 0x3b29c84, 0xe2baae0,
  0x202a278, 0xa0286d7, 0x371f187, 0x88b9ec8, 0x25e8340, 0x4ebf609, 0x3ee1387,
  0x8295690, 0x20861df, 0x1a9d139, 0x7d3c99c, 0xfb0cadb, 0x466440f, 0x2fe8a22,
  0x145013d, 0x72d1c5b, 0x42c5763, 0x95e52e4, 0x52a4daa, 0xb9b273a, 0x27dbb35,
  0x3c3feff, 0x7277936, 0xc9a444f, 0x572d393, 0x174b75, 0x451584f, 0xff754bf,
  0x58e3ff8, 0xe27939c, 0x18160b1, 0xd1bc59e, 0x2cedd5c, 0xdd43349, 0x2aa1006,
  0x46f9580, 0x33eb50e, 0x19e5173, 0x56750d6, 0x2749f85, 0x274a7b6, 0x4384a76,
  0x62782d3, 0x9da576, 0xc02b06, 0xe2cf378, 0x43c2e36, 0x9aedf0c, 0x219b6ea,
  0x5568e75, 0x86aa62, 0xb41195d, 0x49d8f97, 0x52418e3, 0x610c84d, 0x3e78678,
  0x1202ddb, 0x6fc09f3, 0x7cc6a95, 0x4819a5d, 0x2f89923, 0x20498cc, 0x2a13e8c,
  0x3dfb8b0, 0x69b86af, 0xa376e39, 0x4da53fd, 0x52a2b5e, 0x669904b, 0x724e74c,
  0x6783d0, 0x39fe847, 0x1b149c8, 0xfc85f1c, 0x68a8131, 0x7f30d0c, 0x208cce9,
  0x380bba4, 0x1347c05, 0xff6a74e, 0x29af9f8, 0xfc29af9, 0x6be15a6, 0x26ecf72,
  0x6745294, 0x4ebe9f, 0x7ea32cf, 0x2732748, 0x7118c67, 0x6c40247, 0xf02d01,
  0x7366472, 0xfbafa2, 0xceeba1f, 0x939360, 0xac5abc, 0x44fff80, 0xbcbc487,
  0x9eaf1a, 0xf9df172, 0x74f11f, 0xd3bbc51, 0x7b66417, 0x170ae5f, 0x106ea5,
  0x60dad2a, 0x52d3d94, 0x2bd8328, 0x32b6e4f, 0x1cefca0, 0x3c3f537, 0x67f7fab,
  0x18c4fe5, 0x1dc21ff, 0x1723c1a, 0x1e6b067, 0x2d3191a, 0x63e8ebd, 0x25a7528,
  0x7c8e259, 0x335d8f4, 0x663bb5b, 0x5db50f0, 0xc57e541, 0x398df5e, 0xe6d8318,
  0x8bfef3, 0xaf5fe7b, 0x1db8fda, 0x17bb3d1, 0x45dca99, 0x5ae5d8a, 0x2a731e8,
  0xddc1d9f, 0x1cf4389, 0xfba3a63, 0x18cf4e0, 0xf487809, 0x4535a2a, 0x3b87907,
  0x7658c06, 0x9a7b2d8, 0x666d597, 0xbf9c1e0, 0x4d9c875, 0x1ad33b8, 0x390d393,
  0x67ea068, 0x1059d93, 0x9a3f461, 0x116b367, 0x91cb16a, 0x34aba37, 0x266fb1d,
  0xc94a4b, 0xd5bcb4b, 0x14b6d8c, 0xa09bb5a, 0x2bb6ef6, 0x6bd586b, 0x2b3252,
  0x4bc65f8, 0x29fca20, 0x7c94af3, 0x3afea5b, 0x18b0d2d, 0x118ac95, 0xd88a07e,
  0x905517, 0x3b29bd3, 0x81cebb, 0x417f5, 0x5325aed, 0x17403ed, 0xd8623d,
  0x965c08b, 0x99fd8, 0x175304, 0x4db2c7, 0x408daf, 0x445245, 0x53ae409,
  0x211bb1a, 0xf6532bd, 0x749d4e7, 0x15c0f64, 0x17cc812, 0x41dfe45, 0x26722ef,
  0x56620dd, 0x6952fc8, 0x22d3ebf, 0x18c4da1, 0xe8834e, 0x376bb12, 0xeda837a,
  0x4c3f6cf, 0x1b5e26d, 0x315114, 0x1274f68, 0x68c6674, 0x8ec849d, 0x3c33e35,
  0x83a2c38, 0xba22c2, 0x3b45d4a, 0x383a4f1, 0x3f33e69, 0x23e1b0c, 0x12c62a6,
  0x52584ca, 0x652a73d, 0x77ad3ea, 0xdf110be, 0x42b131d, 0xb0defe2, 0x83ef3b,
  0x2d7dd7b, 0x6db98ad, 0x6854665, 0x7e58a19, 0x581f157, 0xcec439, 0xe0a9da,
  0x63c17cc, 0x6af47b4, 0x18cf8bc, 0x7f63857, 0x3634c7f, 0xebcb863, 0x2225df7,
  0x951e5fc, 0x41a2a45, 0xf507c69, 0x2521246, 0x1ab0b20, 0x2ac6ff0, 0x6dae29a,
  0x78e4863, 0xc2b7d44, 0x791cb34, 0x11de6b5, 0x3f2ef6d, 0x8167561, 0xe38331,
  0x2d33696, 0x56a98d3, 0x85fa178, 0x29b48e7, 0x415a84e, 0x775031d, 0x728165f,
  0x6a22e02, 0xbcc13b6, 0x5c3bed6, 0xe416c9b, 0x7e84a04, 0x121ca48, 0x3dcfb9,
  0x2a753b, 0x3b42ce7, 0xfb3c2aa, 0xeb47a0, 0xc2924ff, 0x70db309, 0x14c18f8,
  0x434de1, 0x849b567, 0x35d2cc3, 0xf0e8a0f, 0x724f65c, 0xc13aa7, 0x24cdd50,
  0x84d63c7, 0x7a331d9, 0x588091d, 0x61c9d4, 0xfd49747, 0x31b156e, 0x386e52f,
  0x3962853, 0xd1ed2b8, 0x5b6c063, 0xbc4daab, 0x2b37b0a, 0x314e7ba, 0x3e7eda6,
  0xff414be, 0x434330f, 0xf84278d, 0x40b18f, 0x88fa593, 0x2b63a70, 0x264acbc,
  0x7abebaf, 0xe88bf4e, 0x3b6ea95, 0x3f74933, 0x3a91231, 0xea22837, 0x5898ab,
  0x5d3327a, 0x4d62b2e, 0x7b2f88a, 0x5f92179, 0xd0961e2, 0x5fec1f0, 0xa673560,
  0x3b8c83b, 0xc47f058, 0x7c71cd7, 0xea5902e, 0x66d02c4, 0x9d68b9c, 0x3377501
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
    tmp2[i +  4] -= 1 & xMask;
    tmp2[i +  4] += (1 << 28) & xMask;
    tmp2[i +  4] -= (x << 18) & kBottom28Bits;
    tmp2[i +  4] -= x >> 14;
    tmp2[i +  5] -= 1 & xMask;
    tmp2[i +  5] += (1 << 27) & xMask;
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
    tmp2[i +  5] -= 1 & xMask;
    tmp2[i +  5] += (1 << 27) & xMask;
    tmp2[i +  5] -= (x << 18) & kBottom27Bits;
    tmp2[i +  5] -= x >> 14;
    tmp2[i +  6] -= 1 & xMask;
    tmp2[i +  6] += (1 << 28) & xMask;
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

/* copy_conditional sets out=in if mask = 0xffffffff in constant time.
 *
 * On entry: mask is either 0 or 0xffffffff. */
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
