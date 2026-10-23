/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog

/-!
# Transcendental fixtures

Named inputs of the transcendental functions with the correctly rounded nearest-even results of
MPFR 4.1.0, and the special-value and NaN matrices that MPFR cannot check: MPFR has a single NaN
without payloads, and FloatLib's NaN selection is its own policy.

`FloatLibTests.Regression.BinaryInterchange.ExecFloatTranscendentals` evaluates every row in
`lake -d tests exe check transcendentals`, except the rows of `slowTrigReduction`, which
`lake -d tests exe check reduction` evaluates. `tests/oracles/transcendental_test.py` reads the MPFR
rows from this file and recomputes each expected encoding with the oracle in
`tests/oracles/transcendental_mpfr.c`, so keep the layout of those rows: the `format`, `operation`,
`arguments` and `expected` fields in that order, with hexadecimal encodings.

A row that FloatLib does not meet yet records in `knownFailure` the encoding FloatLib returns
today and the design item that repairs it. The check requires exactly that encoding, so a
deterioration fails as well as a repair, and the repair deletes the field.

The special-value rows are grouped by the IEEE 754 exception their operation signals. FloatLib's
transcendental functions return no status flags yet, so the checks compare only the results.
-/

@[expose] public section

namespace FloatLibTests.Fixtures.Transcendentals

open FloatLib.Floats.Formats.BinaryInterchange

/-- Destination formats of the fixtures. `transcendental_test.py` maps the same names. -/
inductive FormatName where
  | binary16
  | bfloat16
  | binary32
  | binary64
  | binary128
  | binary256
  /-- `FloatFormat.ieee 20 37`, whose largest finite values need a `2^20`-bit level of `2 / pi`. -/
  | ieee20x37
  /-- `FloatFormat.ieee 31 23`, binary32's precision with a 31-bit exponent field. -/
  | ieee31x23
  /-- `FloatFormat.ieee 31 52`, binary64's precision with a 31-bit exponent field. -/
  | ieee31x52
  /-- binary32's layout with exponent bias 239: the largest exponent is 15, the smallest -238. -/
  | bias239
  deriving DecidableEq, Repr

/-- The descriptor a fixture format names. -/
def FormatName.descriptor : FormatName → FloatFormat
  | .binary16 => .binary16
  | .bfloat16 => .bfloat16
  | .binary32 => .binary32
  | .binary64 => .binary64
  | .binary128 => .binary128
  | .binary256 => .binary256
  | .ieee20x37 => .ieee 20 37
  | .ieee31x23 => .ieee 31 23
  | .ieee31x52 => .ieee 31 52
  | .bias239 => .custom 8 23 239 .ieee

/-- The compared functions. -/
inductive Operation where
  | exp
  | log
  | sin
  | cos
  | sinh
  | cosh
  | tanh
  | pow
  deriving DecidableEq, Repr

/-- The operations with one argument. -/
def unaryOperations : List Operation :=
  [.exp, .log, .sin, .cos, .sinh, .cosh, .tanh]

/-- A result FloatLib does not meet yet: the encoding it returns today and the repairing item. -/
structure KnownFailure where
  result : Nat
  repairedBy : String

/-- One input and the correctly rounded nearest-even result MPFR 4.1.0 gives for it. -/
structure Fixture where
  name : String
  format : FormatName
  operation : Operation
  arguments : List Nat
  expected : Nat
  /-- Set while FloatLib returns another encoding, which the check then requires exactly. -/
  knownFailure : Option KnownFailure := none

/--
Huge arguments of sine and cosine, many near multiples of `pi / 2`.

A fixed 1107-bit `pi / 2` gave the binary64 sine of `6221301883130153 * 2^971` 2,637,270 ulps
away. Binary128 arguments at and above `2^4097`, up to `1.75 * 2^16383`, were rejected as beyond a
fixed exponent budget, and the binary256 arguments near the top of the range read a `2^19`-bit
level of `2 / pi`. The rows after the binary256 extremes are the two inputs of each format closest
to a multiple of `pi / 2` in the hard-case corpus of
`tests/oracles/data/transcendental-hard-cases.tsv`.
-/
def trigReduction : List Fixture := [
  { name := "binary64 sin of 6221301883130153*2^971", format := .binary64, operation := .sin,
    arguments := [0x7fe61a3db8c8d129], expected := 0xbc7dd15f96b823f2 },
  { name := "binary64 cos of 6221301883130153*2^971", format := .binary64, operation := .cos,
    arguments := [0x7fe61a3db8c8d129], expected := 0x3ff0000000000000 },
  { name := "binary64 sin of -6221301883130153*2^971", format := .binary64, operation := .sin,
    arguments := [0xffe61a3db8c8d129], expected := 0x3c7dd15f96b823f2 },
  { name := "binary64 cos of -6221301883130153*2^971", format := .binary64, operation := .cos,
    arguments := [0xffe61a3db8c8d129], expected := 0x3ff0000000000000 },
  { name := "binary64 cos of 0x1.b1c15d78e7c7cp+1017", format := .binary64, operation := .cos,
    arguments := [0x7f8b1c15d78e7c7c], expected := 0x3c920cfc515a2cbc },
  { name := "binary64 cos of 0x1.36bf9a50c044p+1008", format := .binary64, operation := .cos,
    arguments := [0x7ef36bf9a50c0440], expected := 0x3c7d90bcc35ff8fa },
  { name := "binary64 cos of 0x1.7f6a4d2df7d7fp+1003", format := .binary64, operation := .cos,
    arguments := [0x7ea7f6a4d2df7d7f], expected := 0x3c9793f0234434dd },
  { name := "binary128 sin of 0x1p+4097", format := .binary128, operation := .sin,
    arguments := [0x50000000000000000000000000000000],
    expected := 0xbffe5ee8e0d4cd35291c790670f6d82b },
  { name := "binary128 cos of 0x1p+4097", format := .binary128, operation := .cos,
    arguments := [0x50000000000000000000000000000000],
    expected := 0x3ffe74d5eae21ce2e37dd756ddb60419 },
  { name := "binary128 sin of -0x1p+4097", format := .binary128, operation := .sin,
    arguments := [0xd0000000000000000000000000000000],
    expected := 0x3ffe5ee8e0d4cd35291c790670f6d82b },
  { name := "binary128 cos of -0x1p+4097", format := .binary128, operation := .cos,
    arguments := [0xd0000000000000000000000000000000],
    expected := 0x3ffe74d5eae21ce2e37dd756ddb60419 },
  { name := "binary128 sin of 0x1p+5000", format := .binary128, operation := .sin,
    arguments := [0x53870000000000000000000000000000],
    expected := 0xbffe1acec26afb2e0d3c395fd4caae85 },
  { name := "binary128 cos of 0x1p+5000", format := .binary128, operation := .cos,
    arguments := [0x53870000000000000000000000000000],
    expected := 0xbffeaace7a0913d5c1871b83446b2304 },
  { name := "binary128 sin of -0x1p+5000", format := .binary128, operation := .sin,
    arguments := [0xd3870000000000000000000000000000],
    expected := 0x3ffe1acec26afb2e0d3c395fd4caae85 },
  { name := "binary128 cos of -0x1p+5000", format := .binary128, operation := .cos,
    arguments := [0xd3870000000000000000000000000000],
    expected := 0xbffeaace7a0913d5c1871b83446b2304 },
  { name := "binary128 sin of 0x1.cp+16383", format := .binary128, operation := .sin,
    arguments := [0x7ffec000000000000000000000000000],
    expected := 0x3ffe87a245ffbc8d27099b432444b8c8 },
  { name := "binary128 cos of 0x1.cp+16383", format := .binary128, operation := .cos,
    arguments := [0x7ffec000000000000000000000000000],
    expected := 0xbffe49cc5be30a458ca3dccf2bce2bda },
  { name := "binary128 sin of -0x1.cp+16383", format := .binary128, operation := .sin,
    arguments := [0xfffec000000000000000000000000000],
    expected := 0xbffe87a245ffbc8d27099b432444b8c8 },
  { name := "binary128 cos of -0x1.cp+16383", format := .binary128, operation := .cos,
    arguments := [0xfffec000000000000000000000000000],
    expected := 0xbffe49cc5be30a458ca3dccf2bce2bda },
  { name := "binary128 sin of 0x1.116ddfdb67e63123e7050f2cc6abp+4096", format := .binary128,
    operation := .sin,
    arguments := [0x4fff116ddfdb67e63123e7050f2cc6ab],
    expected := 0x3f9068a363bdbf24f848402bf5ba065c },
  { name := "binary128 cos of 0x1.a4d58c542c80c4cea222bcf86c15p+4045", format := .binary128,
    operation := .cos,
    arguments := [0x4fcca4d58c542c80c4cea222bcf86c15],
    expected := 0x3f8b16728f666b136e6128b2e188407a },
  { name := "binary128 sin of 0x1.f7c5fd03b4406d52f997b02ae816p+4097", format := .binary128,
    operation := .sin,
    arguments := [0x5000f7c5fd03b4406d52f997b02ae816],
    expected := 0x3fff0000000000000000000000000000 },
  { name := "binary128 cos of 0x1.f7c5fd03b4406d52f997b02ae816p+4097", format := .binary128,
    operation := .cos,
    arguments := [0x5000f7c5fd03b4406d52f997b02ae816],
    expected := 0xbf8b65c20bf321f7ba3bc48ad3622537 },
  { name := "binary128 cos of 0x1.e612dba772a00f53c0c0c1856739p+5000", format := .binary128,
    operation := .cos,
    arguments := [0x5387e612dba772a00f53c0c0c1856739],
    expected := 0x3f8dfd91f4b48c19081cbaa100b412a0 },
  { name := "binary128 cos of 0x1.7d1f5c209f1c120539d262b4dd19p+16383", format := .binary128,
    operation := .cos,
    arguments := [0x7ffe7d1f5c209f1c120539d262b4dd19],
    expected := 0x3f8e91f007a570fb4d7de6aff1c464dd },
  { name := "binary128 sin of 0x1.8p+4096", format := .binary128, operation := .sin,
    arguments := [0x4fff8000000000000000000000000000],
    expected := 0xbffeb0102f0a5b16a59c65537065cfbb },
  { name := "binary256 sin of (2^236 + 12345) * 2^261764", format := .binary256, operation := .sin,
    arguments := [0x7ff6f00000000000000000000000000000000000000000000000000000003039],
    expected := 0xbfffee076eae759b259fe3f11ecd40e73d1bc71384a098a79df88a450cb424db },
  { name := "binary256 cos of (2^236 + 12345) * 2^261764", format := .binary256, operation := .cos,
    arguments := [0x7ff6f00000000000000000000000000000000000000000000000000000003039],
    expected := 0xbfffd61d2ed08db7832e514d216af86f993b49acaabb9f7228483464097e78b7 },
  { name := "binary128 sin of 0x1p+4096", format := .binary128, operation := .sin,
    arguments := [0x4fff0000000000000000000000000000],
    expected := 0x3ffd797f59557d19b9b60b18461ebdd6 },
  { name := "binary128 cos of 0x1p+4096", format := .binary128, operation := .cos,
    arguments := [0x4fff0000000000000000000000000000],
    expected := 0xbffedbf0615365baf8a1e946bbb568d4 },
  { name := "binary128 sin of -0x1p+4096", format := .binary128, operation := .sin,
    arguments := [0xcfff0000000000000000000000000000],
    expected := 0xbffd797f59557d19b9b60b18461ebdd6 },
  { name := "binary128 cos of -0x1p+4096", format := .binary128, operation := .cos,
    arguments := [0xcfff0000000000000000000000000000],
    expected := 0xbffedbf0615365baf8a1e946bbb568d4 },
  { name := "binary256 sin of 0x1p+4096", format := .binary256, operation := .sin,
    arguments := [0x40fff00000000000000000000000000000000000000000000000000000000000],
    expected := 0x3fffd797f59557d19b9b60b18461ebdd5f9168ca07f3177f0dbf547fc4bedf68 },
  { name := "binary256 cos of 0x1p+4096", format := .binary256, operation := .cos,
    arguments := [0x40fff00000000000000000000000000000000000000000000000000000000000],
    expected := 0xbfffedbf0615365baf8a1e946bbb568d45fd90a7188cfb194b7f6cceea8dfeed },
  { name := "binary256 sin of -0x1p+4096", format := .binary256, operation := .sin,
    arguments := [0xc0fff00000000000000000000000000000000000000000000000000000000000],
    expected := 0xbfffd797f59557d19b9b60b18461ebdd5f9168ca07f3177f0dbf547fc4bedf68 },
  { name := "binary256 cos of -0x1p+4096", format := .binary256, operation := .cos,
    arguments := [0xc0fff00000000000000000000000000000000000000000000000000000000000],
    expected := 0xbfffedbf0615365baf8a1e946bbb568d45fd90a7188cfb194b7f6cceea8dfeed },
  { name := "binary256 sin of 0x1p+4097", format := .binary256, operation := .sin,
    arguments := [0x4100000000000000000000000000000000000000000000000000000000000000],
    expected := 0xbfffe5ee8e0d4cd35291c790670f6d82b2597a38b3b325f2e220f09c49f41850 },
  { name := "binary256 cos of 0x1p+4097", format := .binary256, operation := .cos,
    arguments := [0x4100000000000000000000000000000000000000000000000000000000000000],
    expected := 0x3fffe74d5eae21ce2e37dd756ddb60418c03c419ad9fb59d73d419bdc576db5b },
  { name := "binary256 sin of -0x1p+4097", format := .binary256, operation := .sin,
    arguments := [0xc100000000000000000000000000000000000000000000000000000000000000],
    expected := 0x3fffe5ee8e0d4cd35291c790670f6d82b2597a38b3b325f2e220f09c49f41850 },
  { name := "binary256 cos of -0x1p+4097", format := .binary256, operation := .cos,
    arguments := [0xc100000000000000000000000000000000000000000000000000000000000000],
    expected := 0x3fffe74d5eae21ce2e37dd756ddb60418c03c419ad9fb59d73d419bdc576db5b },
  { name := "binary256 sin of 0x1p+5000", format := .binary256, operation := .sin,
    arguments := [0x4138700000000000000000000000000000000000000000000000000000000000],
    expected := 0xbfffe1acec26afb2e0d3c395fd4caae848c97f4ace78b43d032ed0e28298d5b5 },
  { name := "binary256 cos of 0x1p+5000", format := .binary256, operation := .cos,
    arguments := [0x4138700000000000000000000000000000000000000000000000000000000000],
    expected := 0xbfffeaace7a0913d5c1871b83446b2304579deee4123760aa4b3d46c734c8577 },
  { name := "binary256 sin of -0x1p+5000", format := .binary256, operation := .sin,
    arguments := [0xc138700000000000000000000000000000000000000000000000000000000000],
    expected := 0x3fffe1acec26afb2e0d3c395fd4caae848c97f4ace78b43d032ed0e28298d5b5 },
  { name := "binary256 cos of -0x1p+5000", format := .binary256, operation := .cos,
    arguments := [0xc138700000000000000000000000000000000000000000000000000000000000],
    expected := 0xbfffeaace7a0913d5c1871b83446b2304579deee4123760aa4b3d46c734c8577 },
  { name := "binary256 sin of the largest finite value", format := .binary256, operation := .sin,
    arguments := [0x7fffefffffffffffffffffffffffffffffffffffffffffffffffffffffffffff],
    expected := 0x3fffe8c2227bc0c62c0225d6ac3a9e51421945912aa79fbc3d8d8147dd67470e },
  { name := "binary256 cos of the largest finite value", format := .binary256, operation := .cos,
    arguments := [0x7fffefffffffffffffffffffffffffffffffffffffffffffffffffffffffffff],
    expected := 0x3fffe4461409ea97cec20e9fb0504305289feb03f5720767a45fc5e48fe1dbd4 },
  { name := "binary256 sin of the negated largest finite value", format := .binary256,
    operation := .sin,
    arguments := [0xffffefffffffffffffffffffffffffffffffffffffffffffffffffffffffffff],
    expected := 0xbfffe8c2227bc0c62c0225d6ac3a9e51421945912aa79fbc3d8d8147dd67470e },
  { name := "binary256 cos of the negated largest finite value", format := .binary256,
    operation := .cos,
    arguments := [0xffffefffffffffffffffffffffffffffffffffffffffffffffffffffffffffff],
    expected := 0x3fffe4461409ea97cec20e9fb0504305289feb03f5720767a45fc5e48fe1dbd4 },
  { name := "binary16 sin of 0x1.63p+7", format := .binary16, operation := .sin,
    arguments := [0x598c], expected := 0x3c00 },
  { name := "binary16 cos of 0x1.63p+7", format := .binary16, operation := .cos,
    arguments := [0x598c], expected := 0x80fd },
  { name := "binary16 sin of 0x1.63p+8", format := .binary16, operation := .sin,
    arguments := [0x5d8c], expected := 0x81fa },
  { name := "binary16 cos of 0x1.63p+8", format := .binary16, operation := .cos,
    arguments := [0x5d8c], expected := 0xbc00 },
  { name := "bfloat16 sin of 0x1.7ap+58", format := .bfloat16, operation := .sin,
    arguments := [0x5cbd], expected := 0x3f80 },
  { name := "bfloat16 cos of 0x1.7ap+58", format := .bfloat16, operation := .cos,
    arguments := [0x5cbd], expected := 0x3929 },
  { name := "bfloat16 sin of 0x1.0ap+67", format := .bfloat16, operation := .sin,
    arguments := [0x6105], expected := 0x3f80 },
  { name := "bfloat16 cos of 0x1.0ap+67", format := .bfloat16, operation := .cos,
    arguments := [0x6105], expected := 0xb931 },
  { name := "binary32 sin of 0x1.f37c8ap+95", format := .binary32, operation := .sin,
    arguments := [0x6f79be45], expected := 0x3f800000 },
  { name := "binary32 cos of 0x1.f37c8ap+95", format := .binary32, operation := .cos,
    arguments := [0x6f79be45], expected := 0xb0ddeea9 },
  { name := "binary32 sin of 0x1.47d0fep+34", format := .binary32, operation := .sin,
    arguments := [0x50a3e87f], expected := 0x3f800000 },
  { name := "binary32 cos of 0x1.47d0fep+34", format := .binary32, operation := .cos,
    arguments := [0x50a3e87f], expected := 0xb10a4ed8 },
  { name := "binary64 sin of 0x1.6ac5b262ca1ffp+849", format := .binary64, operation := .sin,
    arguments := [0x7506ac5b262ca1ff], expected := 0x3ff0000000000000 },
  { name := "binary64 cos of 0x1.6ac5b262ca1ffp+849", format := .binary64, operation := .cos,
    arguments := [0x7506ac5b262ca1ff], expected := 0xbc214ae72e6ba22f },
  { name := "binary64 sin of 0x1.6c6cbc45dc8dep+5", format := .binary64, operation := .sin,
    arguments := [0x4046c6cbc45dc8de], expected := 0x3ff0000000000000 },
  { name := "binary64 cos of 0x1.6c6cbc45dc8dep+5", format := .binary64, operation := .cos,
    arguments := [0x4046c6cbc45dc8de], expected := 0xbc26d61b58c99c43 },
  { name := "binary128 sin of 0x1.b19ee7c329d7d951906d1e11b5cfp+1964", format := .binary128,
    operation := .sin,
    arguments := [0x47abb19ee7c329d7d951906d1e11b5cf],
    expected := 0x3fff0000000000000000000000000000 },
  { name := "binary128 cos of 0x1.b19ee7c329d7d951906d1e11b5cfp+1964", format := .binary128,
    operation := .cos,
    arguments := [0x47abb19ee7c329d7d951906d1e11b5cf],
    expected := 0x3f83ad1a2037cd7820f748483f5d39c3 },
  { name := "binary128 sin of 0x1.7f0503746ff217260fbe2d9776fdp+3811", format := .binary128,
    operation := .sin,
    arguments := [0x4ee27f0503746ff217260fbe2d9776fd],
    expected := 0x3fff0000000000000000000000000000 },
  { name := "binary128 cos of 0x1.7f0503746ff217260fbe2d9776fdp+3811", format := .binary128,
    operation := .cos,
    arguments := [0x4ee27f0503746ff217260fbe2d9776fd],
    expected := 0xbf8422dddcbac5883ffcf32e86e1ab0d }
]

/--
Sine and cosine arguments whose reduction reads the largest cache levels of `2 / pi`, `2^20` bits
for the largest finite `ieee 20 37` values and `2^21` bits for the `ieee 31 23` arguments. The
last lies in the largest binade of `ieee 31 23` whose first window stays within
`trigReductionLevelLimit`. Computing these levels takes several seconds, so
`lake -d tests exe check reduction` checks these rows outside the default suite.
-/
def slowTrigReduction : List Fixture := [
  { name := "ieee 20 37 sin of the largest finite value", format := .ieee20x37, operation := .sin,
    arguments := [0x1ffffdfffffffff], expected := 0x0ffff8d085e98e1 },
  { name := "ieee 20 37 cos of the largest finite value", format := .ieee20x37, operation := .cos,
    arguments := [0x1ffffdfffffffff], expected := 0x0ffffdf0083ddf7 },
  { name := "ieee 20 37 sin of the negated largest finite value", format := .ieee20x37,
    operation := .sin,
    arguments := [0x3ffffdfffffffff], expected := 0x2ffff8d085e98e1 },
  { name := "ieee 20 37 cos of the negated largest finite value", format := .ieee20x37,
    operation := .cos,
    arguments := [0x3ffffdfffffffff], expected := 0x0ffffdf0083ddf7 },
  { name := "ieee 31 23 sin of 0x1.8p+1048575", format := .ieee31x23, operation := .sin,
    arguments := [0x2007ffff400000], expected := 0x5fffffff1387ac },
  { name := "ieee 31 23 cos of 0x1.8p+1048575", format := .ieee31x23, operation := .cos,
    arguments := [0x2007ffff400000], expected := 0x5fffffff513709 },
  { name := "ieee 31 23 sin of 0x1.8p+1048600", format := .ieee31x23, operation := .sin,
    arguments := [0x2008000bc00000], expected := 0x5fffffff721802 },
  { name := "ieee 31 23 cos of 0x1.8p+1048600", format := .ieee31x23, operation := .cos,
    arguments := [0x2008000bc00000], expected := 0x1ffffffea673d3 },
  { name := "ieee 31 23 sin of 0x1.8p+2095185", format := .ieee31x23, operation := .sin,
    arguments := [0x200ffc28400000], expected := 0x5fffffff5cc333 },
  { name := "ieee 31 23 cos of 0x1.8p+2095185", format := .ieee31x23, operation := .cos,
    arguments := [0x200ffc28400000], expected := 0x5fffffff019d50 },
  { name := "ieee 31 23 sin of 0x1.8p+2095186", format := .ieee31x23, operation := .sin,
    arguments := [0x200ffc28c00000], expected := 0x1fffffff5f8c0b },
  { name := "ieee 31 23 cos of 0x1.8p+2095186", format := .ieee31x23, operation := .cos,
    arguments := [0x200ffc28c00000], expected := 0x5ffffffef98052 },
  { name := "ieee 31 23 sin of 0x1.8p+2097045", format := .ieee31x23, operation := .sin,
    arguments := [0x200fffca400000], expected := 0x1fffffff0cfdf0 },
  { name := "ieee 31 23 cos of 0x1.8p+2097045", format := .ieee31x23, operation := .cos,
    arguments := [0x200fffca400000], expected := 0x1fffffff55acf6 }
]

/--
Inputs where earlier kernels misrounded, and the branch boundaries of the exponential.

`tanh` below one half truncated its square root without a sticky bit. The binary16 `sinh` series
was too short, as was the binary128 one near one half, and the 31-bit-exponent `exp` and `sinh`
lost precision in `x / log 2`. `exp (2^-53)` landed on the midpoint `1 + 2^-53`, and the binary32
`exp` near `2^-24` lost `x^2/2` on its fixed-point scale. The binary64 `exp` rows are both zeros,
the neighbours of one and one half of either sign, tiny negative arguments around `2^-54`, and two
neighbours near `2^-38` whose bits extend below the fixed-point scale. The bias-239 row is
`exp (-64)`, a normal number in that format that must not underflow.
-/
def kernelAccuracy : List Fixture := [
  { name := "binary16 tanh of 0x1.d0cp-6", format := .binary16, operation := .tanh,
    arguments := [0x2743], expected := 0x2743 },
  { name := "binary16 tanh of 0x1.24cp-5", format := .binary16, operation := .tanh,
    arguments := [0x2893], expected := 0x2893 },
  { name := "binary16 tanh of 0x1.f54p-5", format := .binary16, operation := .tanh,
    arguments := [0x2bd5], expected := 0x2bd3 },
  { name := "binary16 tanh of 0x1.c8p-4", format := .binary16, operation := .tanh,
    arguments := [0x2f20], expected := 0x2f19 },
  { name := "binary16 tanh of 0x1.66cp-3", format := .binary16, operation := .tanh,
    arguments := [0x319b], expected := 0x318d },
  { name := "binary16 tanh of 0x1.95p-2", format := .binary16, operation := .tanh,
    arguments := [0x3654], expected := 0x3605 },
  { name := "binary16 tanh of 0x1.c64p-2", format := .binary16, operation := .tanh,
    arguments := [0x3719], expected := 0x36ab },
  { name := "binary16 tanh of 0x1.e6cp-2", format := .binary16, operation := .tanh,
    arguments := [0x379b], expected := 0x3715 },
  { name := "binary16 tanh of -0x1.d0cp-6", format := .binary16, operation := .tanh,
    arguments := [0xa743], expected := 0xa743 },
  { name := "binary16 tanh of -0x1.24cp-5", format := .binary16, operation := .tanh,
    arguments := [0xa893], expected := 0xa893 },
  { name := "binary16 tanh of -0x1.f54p-5", format := .binary16, operation := .tanh,
    arguments := [0xabd5], expected := 0xabd3 },
  { name := "binary16 tanh of -0x1.c8p-4", format := .binary16, operation := .tanh,
    arguments := [0xaf20], expected := 0xaf19 },
  { name := "binary16 tanh of -0x1.66cp-3", format := .binary16, operation := .tanh,
    arguments := [0xb19b], expected := 0xb18d },
  { name := "binary16 tanh of -0x1.95p-2", format := .binary16, operation := .tanh,
    arguments := [0xb654], expected := 0xb605 },
  { name := "binary16 tanh of -0x1.c64p-2", format := .binary16, operation := .tanh,
    arguments := [0xb719], expected := 0xb6ab },
  { name := "binary16 tanh of -0x1.e6cp-2", format := .binary16, operation := .tanh,
    arguments := [0xb79b], expected := 0xb715 },
  { name := "binary16 sinh of 0x1.6e8p-2", format := .binary16, operation := .sinh,
    arguments := [0x35ba], expected := 0x35da },
  { name := "binary16 sinh of 0x1.fb4p-2", format := .binary16, operation := .sinh,
    arguments := [0x37ed], expected := 0x3821 },
  { name := "binary16 sinh of -0x1.6e8p-2", format := .binary16, operation := .sinh,
    arguments := [0xb5ba], expected := 0xb5da },
  { name := "binary16 sinh of -0x1.fb4p-2", format := .binary16, operation := .sinh,
    arguments := [0xb7ed], expected := 0xb821 },
  { name := "binary32 tanh of 0x1.123e82p-2", format := .binary32, operation := .tanh,
    arguments := [0x3e891f41], expected := 0x3e85ef63 },
  { name := "binary32 tanh of 0x1.a5e744p-2", format := .binary32, operation := .tanh,
    arguments := [0x3ed2f3a2], expected := 0x3ec7c5f9 },
  { name := "binary64 tanh of -0x1.90a0c65f8eafp-2", format := .binary64, operation := .tanh,
    arguments := [0xbfd90a0c65f8eaf0], expected := 0xbfd7d5d931716277 },
  { name := "binary64 tanh of 0x1.8dbb98c62e406p-3", format := .binary64, operation := .tanh,
    arguments := [0x3fc8dbb98c62e406], expected := 0x3fc88ce8cc8b5df7 },
  { name := "binary128 tanh of 0x1.a12f7f534a76cp-2", format := .binary128, operation := .tanh,
    arguments := [0x3ffda12f7f534a76c000000000000000],
    expected := 0x3ffd8b8a35b4c2f5ae938c13f5c02fa9 },
  { name := "binary128 sinh of 0x1.fa1adb2375defa2459420e6047b9p-2", format := .binary128,
    operation := .sinh,
    arguments := [0x3ffdfa1adb2375defa2459420e6047b9],
    expected := 0x3ffe077b418b6dee89b22fc4836f051b },
  { name := "binary128 tanh of 0x1.f597754b48659695a96c7c24fdbdp-2", format := .binary128,
    operation := .tanh,
    arguments := [0x3ffdf597754b48659695a96c7c24fdbd],
    expected := 0x3ffdd0fbe68dd172270a7973ae39ea7e },
  { name := "binary128 tanh of -0x1.fe0bde928e8a045c11df5a9d091fp-2", format := .binary128,
    operation := .tanh,
    arguments := [0xbffdfe0bde928e8a045c11df5a9d091f],
    expected := 0xbffdd7ab912116427112230a2ebf17f8 },
  { name := "binary64 exp of 0x1p-53", format := .binary64, operation := .exp,
    arguments := [0x3ca0000000000000], expected := 0x3ff0000000000001 },
  { name := "binary32 exp of 0x1p-24", format := .binary32, operation := .exp,
    arguments := [0x33800000], expected := 0x3f800001 },
  { name := "binary32 exp of -0x1p-25", format := .binary32, operation := .exp,
    arguments := [0xb3000000], expected := 0x3f800000 },
  { name := "binary32 exp of 0x1p-25", format := .binary32, operation := .exp,
    arguments := [0x33000000], expected := 0x3f800000 },
  { name := "binary32 exp of -0x1p-24", format := .binary32, operation := .exp,
    arguments := [0xb3800000], expected := 0x3f7fffff },
  { name := "binary64 exp of 0", format := .binary64, operation := .exp,
    arguments := [0x0000000000000000], expected := 0x3ff0000000000000 },
  { name := "binary64 exp of -0", format := .binary64, operation := .exp,
    arguments := [0x8000000000000000], expected := 0x3ff0000000000000 },
  { name := "binary64 exp of 0x1.fffffffffffffp-1", format := .binary64, operation := .exp,
    arguments := [0x3fefffffffffffff], expected := 0x4005bf0a8b145769 },
  { name := "binary64 exp of 0x1p+0", format := .binary64, operation := .exp,
    arguments := [0x3ff0000000000000], expected := 0x4005bf0a8b145769 },
  { name := "binary64 exp of 0x1.0000000000001p+0", format := .binary64, operation := .exp,
    arguments := [0x3ff0000000000001], expected := 0x4005bf0a8b14576b },
  { name := "binary64 exp of 0x1.fffffffffffffp-2", format := .binary64, operation := .exp,
    arguments := [0x3fdfffffffffffff], expected := 0x3ffa61298e1e069b },
  { name := "binary64 exp of 0x1p-1", format := .binary64, operation := .exp,
    arguments := [0x3fe0000000000000], expected := 0x3ffa61298e1e069c },
  { name := "binary64 exp of 0x1.0000000000001p-1", format := .binary64, operation := .exp,
    arguments := [0x3fe0000000000001], expected := 0x3ffa61298e1e069d },
  { name := "binary64 exp of -0x1p+0", format := .binary64, operation := .exp,
    arguments := [0xbff0000000000000], expected := 0x3fd78b56362cef38 },
  { name := "binary64 exp of -0x1.fffffffffffffp-1", format := .binary64, operation := .exp,
    arguments := [0xbfefffffffffffff], expected := 0x3fd78b56362cef39 },
  { name := "binary64 exp of -0x1p-1", format := .binary64, operation := .exp,
    arguments := [0xbfe0000000000000], expected := 0x3fe368b2fc6f960a },
  { name := "binary64 exp of -0x1.fffffffffffffp-2", format := .binary64, operation := .exp,
    arguments := [0xbfdfffffffffffff], expected := 0x3fe368b2fc6f960a },
  { name := "binary64 exp of -0x1p-60", format := .binary64, operation := .exp,
    arguments := [0xbc30000000000000], expected := 0x3ff0000000000000 },
  { name := "binary64 exp of -0x1p-54", format := .binary64, operation := .exp,
    arguments := [0xbc90000000000000], expected := 0x3ff0000000000000 },
  { name := "binary64 exp of -0x1.0000000000001p-54", format := .binary64, operation := .exp,
    arguments := [0xbc90000000000001], expected := 0x3fefffffffffffff },
  { name := "binary64 exp of 0x1p-54", format := .binary64, operation := .exp,
    arguments := [0x3c90000000000000], expected := 0x3ff0000000000000 },
  { name := "binary64 exp of -0x1.0000000000001p+0", format := .binary64, operation := .exp,
    arguments := [0xbff0000000000001], expected := 0x3fd78b56362cef36 },
  { name := "binary64 exp of -0x1.0000000000001p-1", format := .binary64, operation := .exp,
    arguments := [0xbfe0000000000001], expected := 0x3fe368b2fc6f9609 },
  { name := "binary64 exp of 0x1.0001fffffdfffp-38", format := .binary64, operation := .exp,
    arguments := [0x3d90001fffffdfff], expected := 0x3ff0000000004000 },
  { name := "binary64 exp of 0x1.0001fffffep-38", format := .binary64, operation := .exp,
    arguments := [0x3d90001fffffe000], expected := 0x3ff0000000004001 },
  { name := "ieee 31 23 exp of 0x1.628372p+29", format := .ieee31x23, operation := .exp,
    arguments := [0x2000000e3141b9], expected := 0x3ff746e461b186 },
  { name := "ieee 31 23 exp of 0x1.1fbdp+28", format := .ieee31x23, operation := .exp,
    arguments := [0x2000000d8fde80], expected := 0x2cf8f2df8c2485 },
  { name := "ieee 31 23 sinh of 0x1.60572cp+29", format := .ieee31x23, operation := .sinh,
    arguments := [0x2000000e302b96], expected := 0x3fc51e5d054ad7 },
  { name := "ieee 31 23 sinh of -0x1.13d1fep+29", format := .ieee31x23, operation := .sinh,
    arguments := [0x6000000e09e8ff], expected := 0x78decaf70ec6b5 },
  { name := "ieee 31 23 sinh of 0x1.19d7e8p+29", format := .ieee31x23, operation := .sinh,
    arguments := [0x2000000e0cebf4], expected := 0x3969d3274093d3 },
  { name := "ieee 31 52 exp of 0x1.60c609a08511p+29", format := .ieee31x52, operation := .exp,
    arguments := [0x4000001c60c609a085110], expected := 0x7f9e3afc12800bf8fb8b8 },
  { name := "bias 239 exp of -64", format := .bias239, operation := .exp,
    arguments := [0xfa800000], expected := 0x494b4ea4 }
]

/--
Powers with non-integral exponents, which once rounded three times through `exp (y * log x)`.

Exact results must come out exact: `9^0.5 = 3` and `100^1.5 = 1000`, in binary64 and binary128.
Binary64's nearest third `0x1.5555555555555p-2` lies just below one third, so 8 and 27 raised to
it are not exact powers, but they round to 2 and 3. The 31-bit-exponent rows raise the least
subnormal to `0.5` and the largest finite value to `-0.5`. Both results are near `2^(-2^29)`, far
outside the range of any catalog format. The last three rows are exact rounding midpoints.
Binary16 `4^-12.5 = 2^-25` is half the least subnormal and settles at `+0`, since its reduced
argument is enclosed exactly. No enclosure settles `(2^18 - 1)^3` and `257^3`, the powers `1.5`
of their squares, so `pow` falls back to `exp (y * log x)`, which misses the binary64 one by 11
ulps. Every other result is irrational, two of them large.
-/
def nonIntegralPowers : List Fixture := [
  { name := "binary64 pow(9, 0.5)", format := .binary64, operation := .pow,
    arguments := [0x4022000000000000, 0x3fe0000000000000], expected := 0x4008000000000000 },
  { name := "binary64 pow(100, 1.5)", format := .binary64, operation := .pow,
    arguments := [0x4059000000000000, 0x3ff8000000000000], expected := 0x408f400000000000 },
  { name := "binary64 pow(8, 0x1.5555555555555p-2)", format := .binary64, operation := .pow,
    arguments := [0x4020000000000000, 0x3fd5555555555555], expected := 0x4000000000000000 },
  { name := "binary64 pow(27, 0x1.5555555555555p-2)", format := .binary64, operation := .pow,
    arguments := [0x403b000000000000, 0x3fd5555555555555], expected := 0x4008000000000000 },
  { name := "binary64 pow(2, 0.5)", format := .binary64, operation := .pow,
    arguments := [0x4000000000000000, 0x3fe0000000000000], expected := 0x3ff6a09e667f3bcd },
  { name := "binary64 pow(3, 0.5)", format := .binary64, operation := .pow,
    arguments := [0x4008000000000000, 0x3fe0000000000000], expected := 0x3ffbb67ae8584caa },
  { name := "binary64 pow(2, 1.5)", format := .binary64, operation := .pow,
    arguments := [0x4000000000000000, 0x3ff8000000000000], expected := 0x4006a09e667f3bcd },
  { name := "binary64 pow(1.5, 2.5)", format := .binary64, operation := .pow,
    arguments := [0x3ff8000000000000, 0x4004000000000000], expected := 0x40060b9fd68a4554 },
  { name := "binary64 pow(0x1.d9e6bde20a78p+2, 0x1.4a37efc2bc32p+8)", format := .binary64,
    operation := .pow,
    arguments := [0x401d9e6bde20a780, 0x4074a37efc2bc320], expected := 0x7b8c318c1e2ef2d5 },
  { name := "binary32 pow(5, 1.5)", format := .binary32, operation := .pow,
    arguments := [0x40a00000, 0x3fc00000], expected := 0x4132e2ac },
  { name := "binary32 pow(0x1.3adce8p+3, 0x1.dff92ep+4)", format := .binary32, operation := .pow,
    arguments := [0x411d6e74, 0x41effc97], expected := 0x70f79b67 },
  { name := "binary128 pow(2, 0.5)", format := .binary128, operation := .pow,
    arguments := [0x40000000000000000000000000000000, 0x3ffe0000000000000000000000000000],
    expected := 0x3fff6a09e667f3bcc908b2fb1366ea95 },
  { name := "binary128 pow(9, 0.5)", format := .binary128, operation := .pow,
    arguments := [0x40022000000000000000000000000000, 0x3ffe0000000000000000000000000000],
    expected := 0x40008000000000000000000000000000 },
  { name := "binary128 pow(1.5, 2.5)", format := .binary128, operation := .pow,
    arguments := [0x3fff8000000000000000000000000000, 0x40004000000000000000000000000000],
    expected := 0x400060b9fd68a45544ca385c36b85da0 },
  { name := "binary128 pow(100, 1.5)", format := .binary128, operation := .pow,
    arguments := [0x40059000000000000000000000000000, 0x3fff8000000000000000000000000000],
    expected := 0x4008f400000000000000000000000000 },
  { name := "ieee 31 23 pow of the least subnormal to 0.5", format := .ieee31x23,
    operation := .pow,
    arguments := [0x00000000000001, 0x1fffffff000000], expected := 0xffffffa3504f3 },
  { name := "ieee 31 23 pow of the largest finite value to -0.5", format := .ieee31x23,
    operation := .pow,
    arguments := [0x3fffffff7fffff, 0x5fffffff000000], expected := 0xfffffff800000 },
  { name := "binary16 pow(4, -12.5), half the least subnormal", format := .binary16,
    operation := .pow, arguments := [0x4400, 0xca40], expected := 0x0000 },
  { name := "binary64 pow(68718952449, 1.5), an exact midpoint", format := .binary64,
    operation := .pow,
    arguments := [0x422ffff000020000, 0x3ff8000000000000], expected := 0x434fffe800060000,
    knownFailure := some ⟨0x434fffe80006000b, "CR6"⟩ },
  { name := "binary32 pow(66049, 1.5), an exact midpoint", format := .binary32, operation := .pow,
    arguments := [0x47810080, 0x3fc00000], expected := 0x4b818180 }
]

/-- Every row with an MPFR result. -/
def mpfrFixtures : List Fixture :=
  trigReduction ++ kernelAccuracy ++ nonIntegralPowers

/-- A special operand or result, built in each checked format. -/
inductive Special where
  | positiveZero
  | negativeZero
  | one
  | negativeOne
  | two
  | negativeTwo
  | three
  | negativeThree
  | half
  | negativeHalf
  | positiveInfinity
  | negativeInfinity
  | largest
  | negativeLargest
  | smallestSubnormal
  | negativeSmallestSubnormal
  | canonicalNaN
  deriving DecidableEq, Repr

/-- An operation on special operands and its exact expected result. -/
structure SpecialCase where
  operation : Operation
  arguments : List Special
  result : Special

/-- Special operands with exact results, which signal no exception. -/
def exactSpecials : List SpecialCase := [
  ⟨.exp, [.positiveZero], .one⟩, ⟨.exp, [.negativeZero], .one⟩,
  ⟨.exp, [.positiveInfinity], .positiveInfinity⟩, ⟨.exp, [.negativeInfinity], .positiveZero⟩,
  ⟨.log, [.one], .positiveZero⟩, ⟨.log, [.positiveInfinity], .positiveInfinity⟩,
  ⟨.sin, [.positiveZero], .positiveZero⟩, ⟨.sin, [.negativeZero], .negativeZero⟩,
  ⟨.cos, [.positiveZero], .one⟩, ⟨.cos, [.negativeZero], .one⟩,
  ⟨.sinh, [.positiveZero], .positiveZero⟩, ⟨.sinh, [.negativeZero], .negativeZero⟩,
  ⟨.sinh, [.positiveInfinity], .positiveInfinity⟩,
  ⟨.sinh, [.negativeInfinity], .negativeInfinity⟩,
  ⟨.cosh, [.positiveZero], .one⟩, ⟨.cosh, [.negativeZero], .one⟩,
  ⟨.cosh, [.positiveInfinity], .positiveInfinity⟩,
  ⟨.cosh, [.negativeInfinity], .positiveInfinity⟩,
  ⟨.tanh, [.positiveZero], .positiveZero⟩, ⟨.tanh, [.negativeZero], .negativeZero⟩,
  ⟨.tanh, [.positiveInfinity], .one⟩, ⟨.tanh, [.negativeInfinity], .negativeOne⟩,
  ⟨.pow, [.two, .positiveZero], .one⟩, ⟨.pow, [.negativeTwo, .negativeZero], .one⟩,
  ⟨.pow, [.positiveInfinity, .positiveZero], .one⟩,
  ⟨.pow, [.canonicalNaN, .positiveZero], .one⟩, ⟨.pow, [.canonicalNaN, .negativeZero], .one⟩,
  ⟨.pow, [.one, .canonicalNaN], .one⟩, ⟨.pow, [.one, .positiveInfinity], .one⟩,
  ⟨.pow, [.one, .negativeHalf], .one⟩,
  ⟨.pow, [.negativeOne, .positiveInfinity], .one⟩,
  ⟨.pow, [.negativeOne, .negativeInfinity], .one⟩,
  ⟨.pow, [.two, .one], .two⟩, ⟨.pow, [.negativeTwo, .one], .negativeTwo⟩,
  ⟨.pow, [.positiveInfinity, .two], .positiveInfinity⟩,
  ⟨.pow, [.positiveInfinity, .negativeTwo], .positiveZero⟩,
  ⟨.pow, [.negativeInfinity, .three], .negativeInfinity⟩,
  ⟨.pow, [.negativeInfinity, .negativeThree], .negativeZero⟩,
  ⟨.pow, [.negativeInfinity, .two], .positiveInfinity⟩,
  ⟨.pow, [.negativeInfinity, .half], .positiveInfinity⟩,
  ⟨.pow, [.positiveZero, .three], .positiveZero⟩, ⟨.pow, [.negativeZero, .three], .negativeZero⟩,
  ⟨.pow, [.negativeZero, .two], .positiveZero⟩,
  ⟨.pow, [.negativeZero, .positiveInfinity], .positiveZero⟩,
  ⟨.pow, [.two, .positiveInfinity], .positiveInfinity⟩,
  ⟨.pow, [.two, .negativeInfinity], .positiveZero⟩,
  ⟨.pow, [.half, .positiveInfinity], .positiveZero⟩,
  ⟨.pow, [.half, .negativeInfinity], .positiveInfinity⟩
]

/-- Invalid operations: the result is the canonical NaN. -/
def invalidSpecials : List SpecialCase := [
  ⟨.log, [.negativeOne], .canonicalNaN⟩, ⟨.log, [.negativeInfinity], .canonicalNaN⟩,
  ⟨.log, [.negativeSmallestSubnormal], .canonicalNaN⟩,
  ⟨.sin, [.positiveInfinity], .canonicalNaN⟩, ⟨.sin, [.negativeInfinity], .canonicalNaN⟩,
  ⟨.cos, [.positiveInfinity], .canonicalNaN⟩, ⟨.cos, [.negativeInfinity], .canonicalNaN⟩,
  ⟨.pow, [.negativeTwo, .half], .canonicalNaN⟩,
  ⟨.pow, [.negativeThree, .negativeHalf], .canonicalNaN⟩
]

/-- Exact infinities from finite operands, which signal division by zero. -/
def divideByZeroSpecials : List SpecialCase := [
  ⟨.log, [.positiveZero], .negativeInfinity⟩, ⟨.log, [.negativeZero], .negativeInfinity⟩,
  ⟨.pow, [.positiveZero, .negativeOne], .positiveInfinity⟩,
  ⟨.pow, [.negativeZero, .negativeOne], .negativeInfinity⟩,
  ⟨.pow, [.negativeZero, .negativeTwo], .positiveInfinity⟩,
  ⟨.pow, [.positiveZero, .negativeHalf], .positiveInfinity⟩
]

/-- Results beyond the largest finite magnitude, which overflow to an infinity. -/
def overflowSpecials : List SpecialCase := [
  ⟨.exp, [.largest], .positiveInfinity⟩,
  ⟨.sinh, [.largest], .positiveInfinity⟩, ⟨.sinh, [.negativeLargest], .negativeInfinity⟩,
  ⟨.cosh, [.largest], .positiveInfinity⟩, ⟨.cosh, [.negativeLargest], .positiveInfinity⟩,
  ⟨.pow, [.largest, .two], .positiveInfinity⟩,
  ⟨.pow, [.negativeLargest, .three], .negativeInfinity⟩
]

/-- Nonzero results below half the smallest subnormal, which underflow to a zero. -/
def underflowSpecials : List SpecialCase := [
  ⟨.exp, [.negativeLargest], .positiveZero⟩,
  ⟨.pow, [.smallestSubnormal, .two], .positiveZero⟩,
  ⟨.pow, [.negativeSmallestSubnormal, .three], .negativeZero⟩
]

/-- Rounded results that stay finite and normal, which signal only inexact. -/
def inexactSpecials : List SpecialCase := [
  ⟨.tanh, [.largest], .one⟩, ⟨.tanh, [.negativeLargest], .negativeOne⟩,
  ⟨.exp, [.smallestSubnormal], .one⟩, ⟨.exp, [.negativeSmallestSubnormal], .one⟩,
  ⟨.cos, [.smallestSubnormal], .one⟩, ⟨.cosh, [.smallestSubnormal], .one⟩
]

/-- Quiet NaN operands, which propagate unchanged and signal no exception. -/
def quietNaNSpecials : List SpecialCase := [
  ⟨.exp, [.canonicalNaN], .canonicalNaN⟩, ⟨.log, [.canonicalNaN], .canonicalNaN⟩,
  ⟨.sin, [.canonicalNaN], .canonicalNaN⟩, ⟨.cos, [.canonicalNaN], .canonicalNaN⟩,
  ⟨.sinh, [.canonicalNaN], .canonicalNaN⟩, ⟨.cosh, [.canonicalNaN], .canonicalNaN⟩,
  ⟨.tanh, [.canonicalNaN], .canonicalNaN⟩,
  ⟨.pow, [.canonicalNaN, .two], .canonicalNaN⟩, ⟨.pow, [.two, .canonicalNaN], .canonicalNaN⟩
]

/-- The whole special-value matrix. -/
def specialCases : List SpecialCase :=
  exactSpecials ++ quietNaNSpecials ++ invalidSpecials ++ divideByZeroSpecials ++
    overflowSpecials ++ underflowSpecials ++ inexactSpecials

/-- A NaN operand: signaling or quiet, its sign and its payload. -/
structure NaNOperand where
  signaling : Bool
  negative : Bool
  payload : Nat
  deriving DecidableEq, Repr

/-- The signaling NaN of the matrix, payload `0x2a`. -/
def signalingNaN (negative : Bool := false) : NaNOperand := ⟨true, negative, 0x2a⟩

/-- The quiet NaN of the matrix, payload `0x15`. -/
def quietNaN (negative : Bool := false) : NaNOperand := ⟨false, negative, 0x15⟩

/-- NaN operands of the unary functions: both kinds with both signs. -/
def unaryNaNOperands : List NaNOperand :=
  [signalingNaN, signalingNaN true, quietNaN, quietNaN true]

/-- A `pow` operand of the NaN matrix. -/
inductive PowOperand where
  | nan (operand : NaNOperand)
  | special (value : Special)

/-- The expected `pow` result: one, or the base or exponent NaN quieted with its payload. -/
inductive PowNaNResult where
  | one
  | quietBase
  | quietExponent
  deriving DecidableEq, Repr

/-- A `pow` row of the NaN matrix. -/
structure PowNaNCase where
  base : PowOperand
  exponent : PowOperand
  result : PowNaNResult

/--
`pow` with NaN operands. IEEE 754-2019 requires a quiet NaN for a signaling NaN operand, even
where a quiet NaN in its place gives a number (6.2 and 9.2.1), and `pow(qNaN, +-0) = 1` and
`pow(1, qNaN) = 1` (9.2.1). It leaves open which NaN operand the result comes from. FloatLib's
policy, `chooseNaN2`, chooses a signaling operand before a quiet one and the base before the
exponent among NaNs of the same kind, and keeps the chosen operand's payload, as 6.2.3
recommends.
-/
def powNaNCases : List PowNaNCase := [
  ⟨.nan signalingNaN, .special .positiveZero, .quietBase⟩,
  ⟨.nan signalingNaN, .special .negativeZero, .quietBase⟩,
  ⟨.nan quietNaN, .special .positiveZero, .one⟩,
  ⟨.nan quietNaN, .special .negativeZero, .one⟩,
  ⟨.special .one, .nan signalingNaN, .quietExponent⟩,
  ⟨.special .one, .nan quietNaN, .one⟩,
  ⟨.nan signalingNaN, .special .one, .quietBase⟩,
  ⟨.nan quietNaN, .special .two, .quietBase⟩,
  ⟨.special .two, .nan signalingNaN, .quietExponent⟩,
  ⟨.special .two, .nan (quietNaN true), .quietExponent⟩,
  ⟨.nan signalingNaN, .nan (signalingNaN true), .quietBase⟩,
  ⟨.nan (signalingNaN true), .nan signalingNaN, .quietBase⟩,
  ⟨.nan quietNaN, .nan signalingNaN, .quietExponent⟩,
  ⟨.nan signalingNaN, .nan quietNaN, .quietBase⟩,
  ⟨.nan quietNaN, .nan (quietNaN true), .quietBase⟩,
  ⟨.nan (quietNaN true), .nan quietNaN, .quietBase⟩
]

end FloatLibTests.Fixtures.Transcendentals
