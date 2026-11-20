/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public meta import FloatLib.Floats.Formats.BinaryInterchange.Configured
public meta import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded

/-!
# The recommended functions of IEEE 754-2019 §9.2 on binary formats

Special cases of the functions of `ExecFloat.Binary.CorrectlyRounded` on binary16, as
ISO/IEC 9899:2024 (C23, N3220) F.10.1 to F.10.4 state them: the results at zeros, infinities and
NaNs, the domain errors with `invalid`, the poles with `divideByZero`, the exact results that
raise no flag, and overflows and underflows in several rounding directions. `cases` holds every
case once, and compiled evaluation checks it when this module is elaborated. `wideCases` are
results in a layout with 35 exponent bits, where the rounding must not build the powers of two
at the ends of the exponent range. `hintCases` compare the outcome with the enclosure search
and the outcome of the comparisons alone, for every function. The results at ordinary operands are
compared with `mpmath` by `tests/oracles/ieee2019.sh`.

The second half applies the theorems to binary64 and to the named functions, which shows that
a named function is its member of the enumeration by definition and that the premise on the
format holds.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RecommendedFunctions

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.ExecFloat.Binary

/-- The binary16 value with the encoding `bits`. -/
def b16 (bits : Nat) : Binary16 := ExecFloat.Binary.ofNatBits bits

/--
The encoding of a result and its flags as the sum of invalid 1, divideByZero 2, overflow 4,
underflow 8 and inexact 16.
-/
def result (outcome : type_of% (CorrectlyRounded.exp2 (b16 0))) : Nat × Nat :=
  (outcome.value.toNatBits,
    (if outcome.status.invalid then 1 else 0) + (if outcome.status.divideByZero then 2 else 0) +
      (if outcome.status.overflow then 4 else 0) + (if outcome.status.underflow then 8 else 0) +
      (if outcome.status.inexact then 16 else 0))

/-- A layout with the 35 exponent bits of the 4,096-bit format and four fraction bits. -/
abbrev Wide := ExecFloat.Binary (exponentBits := 35) (fractionBits := 4)

/-- The encoding in `Wide` of `±(1 + fraction / 16) * 2 ^ exponent`. -/
def wideBits (negative : Bool) (exponent : Int) (fraction : Nat) : Nat :=
  (if negative then 2 ^ 39 else 0) + ((2 ^ 34 - 1 : Int) + exponent).toNat * 16 + fraction

/-- The value of `Wide` with that encoding. -/
def wide (negative : Bool) (exponent : Int) (fraction : Nat) : Wide :=
  ExecFloat.Binary.ofNatBits (wideBits negative exponent fraction)

/-- The encoding of a result in `Wide` and whether it is inexact. -/
def wideResult (outcome : type_of% (CorrectlyRounded.exp2 (wide false 0 0))) : Nat × Bool :=
  (outcome.value.toNatBits, outcome.status.inexact)

/--
The special cases: a name and whether the case holds. The encodings are binary16: `0x3C00` is
one, `0x4000` two, `0x3800` a half, `0x7C00` infinity, `0x7E00` the quiet NaN, `0x7D00` a
signaling NaN and `0x7F00` that NaN quieted. A result is the pair of an encoding and the flags.
-/
def cases : List (String × Bool) :=
  [ ("exp2 3 is 8", result (CorrectlyRounded.exp2 (b16 0x4200)) == (0x4800, 0)),
    ("exp2 -0 is 1", result (CorrectlyRounded.exp2 (b16 0x8000)) == (0x3C00, 0)),
    ("exp2 -inf is +0", result (CorrectlyRounded.exp2 (b16 0xFC00)) == (0x0000, 0)),
    ("exp2 +inf is +inf", result (CorrectlyRounded.exp2 (b16 0x7C00)) == (0x7C00, 0)),
    ("exp2 sNaN is the NaN quieted, invalid",
      result (CorrectlyRounded.exp2 (b16 0x7D00)) == (0x7F00, 1)),
    ("exp2 qNaN is the NaN", result (CorrectlyRounded.exp2 (b16 0x7E00)) == (0x7E00, 0)),
    ("exp2 16 overflows", result (CorrectlyRounded.exp2 (b16 0x4C00)) == (0x7C00, 20)),
    ("exp2 -24 is the least subnormal", result (CorrectlyRounded.exp2 (b16 0xCE00)) == (0x0001, 0)),
    ("exp2 -25 underflows to zero", result (CorrectlyRounded.exp2 (b16 0xCE40)) == (0x0000, 24)),
    ("exp2m1 3 is 7", result (CorrectlyRounded.exp2m1 (b16 0x4200)) == (0x4700, 0)),
    ("exp2m1 -0 is -0", result (CorrectlyRounded.exp2m1 (b16 0x8000)) == (0x8000, 0)),
    ("exp2m1 -inf is -1", result (CorrectlyRounded.exp2m1 (b16 0xFC00)) == (0xBC00, 0)),
    ("exp10 2 is 100", result (CorrectlyRounded.exp10 (b16 0x4000)) == (0x5640, 0)),
    ("exp10m1 +inf is +inf", result (CorrectlyRounded.exp10m1 (b16 0x7C00)) == (0x7C00, 0)),
    ("exp10m1 1 is 9", result (CorrectlyRounded.exp10m1 (b16 0x3C00)) == (0x4880, 0)),
    ("log2 8 is 3", result (CorrectlyRounded.log2 (b16 0x4800)) == (0x4200, 0)),
    ("log2 1 is +0", result (CorrectlyRounded.log2 (b16 0x3C00)) == (0x0000, 0)),
    ("log2 +0 is -inf, divideByZero", result (CorrectlyRounded.log2 (b16 0x0000)) == (0xFC00, 2)),
    ("log2 -0 is -inf, divideByZero", result (CorrectlyRounded.log2 (b16 0x8000)) == (0xFC00, 2)),
    ("log2 -1 is invalid", result (CorrectlyRounded.log2 (b16 0xBC00)) == (0x7E00, 1)),
    ("log2 -inf is invalid", result (CorrectlyRounded.log2 (b16 0xFC00)) == (0x7E00, 1)),
    ("log10 100 is 2", result (CorrectlyRounded.log10 (b16 0x5640)) == (0x4000, 0)),
    ("log10 +inf is +inf", result (CorrectlyRounded.log10 (b16 0x7C00)) == (0x7C00, 0)),
    ("log2p1 3 is 2", result (CorrectlyRounded.log2p1 (b16 0x4200)) == (0x4000, 0)),
    ("log2p1 -0 is -0", result (CorrectlyRounded.log2p1 (b16 0x8000)) == (0x8000, 0)),
    ("log2p1 -1 is -inf, divideByZero",
      result (CorrectlyRounded.log2p1 (b16 0xBC00)) == (0xFC00, 2)),
    ("log2p1 -2 is invalid", result (CorrectlyRounded.log2p1 (b16 0xC000)) == (0x7E00, 1)),
    ("log10p1 9 is 1", result (CorrectlyRounded.log10p1 (b16 0x4880)) == (0x3C00, 0)),
    ("sin -0 is -0", result (CorrectlyRounded.sin (b16 0x8000)) == (0x8000, 0)),
    ("sin +inf is invalid", result (CorrectlyRounded.sin (b16 0x7C00)) == (0x7E00, 1)),
    ("cos -0 is 1", result (CorrectlyRounded.cos (b16 0x8000)) == (0x3C00, 0)),
    ("cos -inf is invalid", result (CorrectlyRounded.cos (b16 0xFC00)) == (0x7E00, 1)),
    ("tan -0 is -0", result (CorrectlyRounded.tan (b16 0x8000)) == (0x8000, 0)),
    ("sinPi 1/2 is 1", result (CorrectlyRounded.sinPi (b16 0x3800)) == (0x3C00, 0)),
    ("sinPi 3 is +0", result (CorrectlyRounded.sinPi (b16 0x4200)) == (0x0000, 0)),
    ("sinPi -3 is -0", result (CorrectlyRounded.sinPi (b16 0xC200)) == (0x8000, 0)),
    ("sinPi +inf is invalid", result (CorrectlyRounded.sinPi (b16 0x7C00)) == (0x7E00, 1)),
    ("cosPi 1 is -1", result (CorrectlyRounded.cosPi (b16 0x3C00)) == (0xBC00, 0)),
    ("cosPi 3/2 is +0", result (CorrectlyRounded.cosPi (b16 0x3E00)) == (0x0000, 0)),
    ("cosPi -1/2 is +0", result (CorrectlyRounded.cosPi (b16 0xB800)) == (0x0000, 0)),
    ("tanPi 1/4 is 1", result (CorrectlyRounded.tanPi (b16 0x3400)) == (0x3C00, 0)),
    ("tanPi 2 is +0", result (CorrectlyRounded.tanPi (b16 0x4000)) == (0x0000, 0)),
    ("tanPi 3 is -0", result (CorrectlyRounded.tanPi (b16 0x4200)) == (0x8000, 0)),
    ("tanPi -2 is -0", result (CorrectlyRounded.tanPi (b16 0xC000)) == (0x8000, 0)),
    ("tanPi -3 is +0", result (CorrectlyRounded.tanPi (b16 0xC200)) == (0x0000, 0)),
    ("tanPi 1/2 is +inf, divideByZero",
      result (CorrectlyRounded.tanPi (b16 0x3800)) == (0x7C00, 2)),
    ("tanPi 3/2 is -inf, divideByZero",
      result (CorrectlyRounded.tanPi (b16 0x3E00)) == (0xFC00, 2)),
    ("asin -0 is -0", result (CorrectlyRounded.asin (b16 0x8000)) == (0x8000, 0)),
    ("asin 2 is invalid", result (CorrectlyRounded.asin (b16 0x4000)) == (0x7E00, 1)),
    ("acos 1 is +0", result (CorrectlyRounded.acos (b16 0x3C00)) == (0x0000, 0)),
    ("acos -2 is invalid", result (CorrectlyRounded.acos (b16 0xC000)) == (0x7E00, 1)),
    ("atan +inf is pi/2 rounded", result (CorrectlyRounded.atan (b16 0x7C00)) == (0x3E48, 16)),
    ("atan -inf is -pi/2 rounded", result (CorrectlyRounded.atan (b16 0xFC00)) == (0xBE48, 16)),
    ("asinPi 1 is 1/2", result (CorrectlyRounded.asinPi (b16 0x3C00)) == (0x3800, 0)),
    ("acosPi -1 is 1", result (CorrectlyRounded.acosPi (b16 0xBC00)) == (0x3C00, 0)),
    ("acosPi 0 is 1/2", result (CorrectlyRounded.acosPi (b16 0x0000)) == (0x3800, 0)),
    ("atanPi 1 is 1/4", result (CorrectlyRounded.atanPi (b16 0x3C00)) == (0x3400, 0)),
    ("atanPi -inf is -1/2", result (CorrectlyRounded.atanPi (b16 0xFC00)) == (0xB800, 0)),
    ("sinh -inf is -inf", result (CorrectlyRounded.sinh (b16 0xFC00)) == (0xFC00, 0)),
    ("cosh -inf is +inf", result (CorrectlyRounded.cosh (b16 0xFC00)) == (0x7C00, 0)),
    ("cosh +0 is 1", result (CorrectlyRounded.cosh (b16 0x0000)) == (0x3C00, 0)),
    ("tanh +inf is 1", result (CorrectlyRounded.tanh (b16 0x7C00)) == (0x3C00, 0)),
    ("tanh -0 is -0", result (CorrectlyRounded.tanh (b16 0x8000)) == (0x8000, 0)),
    ("asinh -inf is -inf", result (CorrectlyRounded.asinh (b16 0xFC00)) == (0xFC00, 0)),
    ("acosh 1 is +0", result (CorrectlyRounded.acosh (b16 0x3C00)) == (0x0000, 0)),
    ("acosh 1/2 is invalid", result (CorrectlyRounded.acosh (b16 0x3800)) == (0x7E00, 1)),
    ("acosh -inf is invalid", result (CorrectlyRounded.acosh (b16 0xFC00)) == (0x7E00, 1)),
    ("atanh 1 is +inf, divideByZero", result (CorrectlyRounded.atanh (b16 0x3C00)) == (0x7C00, 2)),
    ("atanh -1 is -inf, divideByZero",
      result (CorrectlyRounded.atanh (b16 0xBC00)) == (0xFC00, 2)),
    ("atanh 2 is invalid", result (CorrectlyRounded.atanh (b16 0x4000)) == (0x7E00, 1)),
    ("atan2 +0 -0 is pi rounded",
      result (CorrectlyRounded.atan2 (b16 0x0000) (b16 0x8000)) == (0x4248, 16)),
    ("atan2 -0 -1 is -pi rounded",
      result (CorrectlyRounded.atan2 (b16 0x8000) (b16 0xBC00)) == (0xC248, 16)),
    ("atan2 -0 +0 is -0", result (CorrectlyRounded.atan2 (b16 0x8000) (b16 0x0000)) == (0x8000, 0)),
    ("atan2 1 -0 is pi/2 rounded",
      result (CorrectlyRounded.atan2 (b16 0x3C00) (b16 0x8000)) == (0x3E48, 16)),
    ("atan2 1 +inf is +0", result (CorrectlyRounded.atan2 (b16 0x3C00) (b16 0x7C00)) ==
        (0x0000, 0)),
    ("atan2Pi +inf -inf is 3/4",
      result (CorrectlyRounded.atan2Pi (b16 0x7C00) (b16 0xFC00)) == (0x3A00, 0)),
    ("atan2Pi -inf +inf is -1/4",
      result (CorrectlyRounded.atan2Pi (b16 0xFC00) (b16 0x7C00)) == (0xB400, 0)),
    ("atan2Pi 1 1 is 1/4", result (CorrectlyRounded.atan2Pi (b16 0x3C00) (b16 0x3C00)) ==
        (0x3400, 0)),
    ("atan2Pi -0 -1 is -1",
      result (CorrectlyRounded.atan2Pi (b16 0x8000) (b16 0xBC00)) == (0xBC00, 0)),
    ("atan2Pi 1 -inf is 1", result (CorrectlyRounded.atan2Pi (b16 0x3C00) (b16 0xFC00)) ==
        (0x3C00, 0)),
    ("atan2Pi 2 +0 is 1/2", result (CorrectlyRounded.atan2Pi (b16 0x4000) (b16 0x0000)) ==
        (0x3800, 0)),
    ("E4M3 powr 22 2 overflows toward zero at the reserved top word",
      (Model.Transcendentals.CorrectlyRounded.powr (Model.ofRat FloatFormat.e4m3 22)
        (Model.ofRat FloatFormat.e4m3 2) .towardZero).status.overflow),
    ("E2M1 exp2m1 3 overflows at the nearest-even midpoint and saturates",
      let r := Model.Transcendentals.CorrectlyRounded.exp2m1 (Model.ofRat FloatFormat.e2m1 3)
      r.status.overflow && Model.toRat? r.value == some 6),
    ("E4M3FNUZ exp2 10 has a positive overflow ternary",
      (Model.Transcendentals.CorrectlyRounded.exp2 (Model.ofRat FloatFormat.e4m3fnuz 10)).ternary
        == .gt),
    ("powr 4 1/2 is 2", result (CorrectlyRounded.powr (b16 0x4400) (b16 0x3800)) == (0x4000, 0)),
    ("powr 3 -0 is 1", result (CorrectlyRounded.powr (b16 0x4200) (b16 0x8000)) == (0x3C00, 0)),
    ("powr +0 -1 is +inf, divideByZero",
      result (CorrectlyRounded.powr (b16 0x0000) (b16 0xBC00)) == (0x7C00, 2)),
    ("powr -0 -inf is +inf", result (CorrectlyRounded.powr (b16 0x8000) (b16 0xFC00)) ==
        (0x7C00, 0)),
    ("powr -0 2 is +0", result (CorrectlyRounded.powr (b16 0x8000) (b16 0x4000)) == (0x0000, 0)),
    ("powr -1 2 is invalid", result (CorrectlyRounded.powr (b16 0xBC00) (b16 0x4000)) ==
        (0x7E00, 1)),
    ("powr 1 +inf is invalid", result (CorrectlyRounded.powr (b16 0x3C00) (b16 0x7C00)) ==
        (0x7E00, 1)),
    ("powr +inf +0 is invalid", result (CorrectlyRounded.powr (b16 0x7C00) (b16 0x0000)) ==
        (0x7E00, 1)),
    ("powr +0 -0 is invalid", result (CorrectlyRounded.powr (b16 0x0000) (b16 0x8000)) ==
        (0x7E00, 1)),
    ("powr 2 -inf is +0", result (CorrectlyRounded.powr (b16 0x4000) (b16 0xFC00)) == (0x0000, 0)),
    ("powr 1/2 -inf is +inf", result (CorrectlyRounded.powr (b16 0x3800) (b16 0xFC00)) ==
        (0x7C00, 0)),
    ("powr 1 qNaN is the NaN", result (CorrectlyRounded.powr (b16 0x3C00) (b16 0x7E00)) ==
        (0x7E00, 0)),
    ("pow 4 1/2 is 2", result (CorrectlyRounded.pow (b16 0x4400) (b16 0x3800)) == (0x4000, 0)),
    ("pow -2 3 is -8", result (CorrectlyRounded.pow (b16 0xC000) (b16 0x4200)) == (0xC800, 0)),
    ("pow -2 2 is 4", result (CorrectlyRounded.pow (b16 0xC000) (b16 0x4000)) == (0x4400, 0)),
    ("pow -2 -1 is -1/2", result (CorrectlyRounded.pow (b16 0xC000) (b16 0xBC00)) == (0xB800, 0)),
    ("pow -2 1/2 is invalid", result (CorrectlyRounded.pow (b16 0xC000) (b16 0x3800)) ==
        (0x7E00, 1)),
    ("pow qNaN -0 is 1", result (CorrectlyRounded.pow (b16 0x7E00) (b16 0x8000)) == (0x3C00, 0)),
    ("pow sNaN +0 is invalid", result (CorrectlyRounded.pow (b16 0x7D00) (b16 0x0000)) ==
        (0x7F00, 1)),
    ("pow 1 qNaN is 1", result (CorrectlyRounded.pow (b16 0x3C00) (b16 0x7E00)) == (0x3C00, 0)),
    ("pow 1 sNaN is invalid", result (CorrectlyRounded.pow (b16 0x3C00) (b16 0x7D00)) ==
        (0x7F00, 1)),
    ("pow -inf +0 is 1", result (CorrectlyRounded.pow (b16 0xFC00) (b16 0x0000)) == (0x3C00, 0)),
    ("pow -0 -3 is -inf, divideByZero",
      result (CorrectlyRounded.pow (b16 0x8000) (b16 0xC200)) == (0xFC00, 2)),
    ("pow -0 -2 is +inf, divideByZero",
      result (CorrectlyRounded.pow (b16 0x8000) (b16 0xC000)) == (0x7C00, 2)),
    ("pow +0 -1/2 is +inf, divideByZero",
      result (CorrectlyRounded.pow (b16 0x0000) (b16 0xB800)) == (0x7C00, 2)),
    ("pow -0 -inf is +inf", result (CorrectlyRounded.pow (b16 0x8000) (b16 0xFC00)) ==
        (0x7C00, 0)),
    ("pow -0 +inf is +0", result (CorrectlyRounded.pow (b16 0x8000) (b16 0x7C00)) == (0x0000, 0)),
    ("pow -0 3 is -0", result (CorrectlyRounded.pow (b16 0x8000) (b16 0x4200)) == (0x8000, 0)),
    ("pow -0 2 is +0", result (CorrectlyRounded.pow (b16 0x8000) (b16 0x4000)) == (0x0000, 0)),
    ("pow -1 +inf is 1", result (CorrectlyRounded.pow (b16 0xBC00) (b16 0x7C00)) == (0x3C00, 0)),
    ("pow -1 -inf is 1", result (CorrectlyRounded.pow (b16 0xBC00) (b16 0xFC00)) == (0x3C00, 0)),
    ("pow 1/2 +inf is +0", result (CorrectlyRounded.pow (b16 0x3800) (b16 0x7C00)) == (0x0000, 0)),
    ("pow -1/2 -inf is +inf", result (CorrectlyRounded.pow (b16 0xB800) (b16 0xFC00)) ==
        (0x7C00, 0)),
    ("pow -2 +inf is +inf", result (CorrectlyRounded.pow (b16 0xC000) (b16 0x7C00)) ==
        (0x7C00, 0)),
    ("pow 2 -inf is +0", result (CorrectlyRounded.pow (b16 0x4000) (b16 0xFC00)) == (0x0000, 0)),
    ("pow +inf -1 is +0", result (CorrectlyRounded.pow (b16 0x7C00) (b16 0xBC00)) == (0x0000, 0)),
    ("pow +inf 1/2 is +inf", result (CorrectlyRounded.pow (b16 0x7C00) (b16 0x3800)) ==
        (0x7C00, 0)),
    ("pow -inf -3 is -0", result (CorrectlyRounded.pow (b16 0xFC00) (b16 0xC200)) == (0x8000, 0)),
    ("pow -inf -2 is +0", result (CorrectlyRounded.pow (b16 0xFC00) (b16 0xC000)) == (0x0000, 0)),
    ("pow -inf 3 is -inf", result (CorrectlyRounded.pow (b16 0xFC00) (b16 0x4200)) ==
        (0xFC00, 0)),
    ("pow -inf 1/2 is +inf", result (CorrectlyRounded.pow (b16 0xFC00) (b16 0x3800)) ==
        (0x7C00, 0)),
    ("pow -inf +inf is +inf", result (CorrectlyRounded.pow (b16 0xFC00) (b16 0x7C00)) ==
        (0x7C00, 0)),
    ("pow -inf -inf is +0", result (CorrectlyRounded.pow (b16 0xFC00) (b16 0xFC00)) ==
        (0x0000, 0)),
    ("pow -3 3 toward positive is -27",
      result (CorrectlyRounded.pow (b16 0xC200) (b16 0x4200) .up) == (0xCEC0, 0)),
    ("pow -2 17 toward zero is the negative largest finite value, overflow",
      result (CorrectlyRounded.pow (b16 0xC000) (b16 0x4C40) .towardZero) == (0xFBFF, 20)),
    ("pow -2 17 toward negative is -inf, overflow",
      result (CorrectlyRounded.pow (b16 0xC000) (b16 0x4C40) .down) == (0xFC00, 20)),
    ("compound 1 3 is 8", result (CorrectlyRounded.compound (b16 0x3C00) 3) == (0x4800, 0)),
    ("compound -1 -2 is +inf, divideByZero",
      result (CorrectlyRounded.compound (b16 0xBC00) (-2)) == (0x7C00, 2)),
    ("compound -1 2 is +0", result (CorrectlyRounded.compound (b16 0xBC00) 2) == (0x0000, 0)),
    ("compound -1 0 is 1", result (CorrectlyRounded.compound (b16 0xBC00) 0) == (0x3C00, 0)),
    ("compound qNaN 0 is 1", result (CorrectlyRounded.compound (b16 0x7E00) 0) == (0x3C00, 0)),
    ("compound sNaN 0 is invalid", result (CorrectlyRounded.compound (b16 0x7D00) 0) ==
        (0x7F00, 1)),
    ("compound -2 1 is invalid", result (CorrectlyRounded.compound (b16 0xC000) 1) == (0x7E00, 1)),
    ("compound +inf -1 is +0", result (CorrectlyRounded.compound (b16 0x7C00) (-1)) == (0x0000, 0)),
    ("compound +inf 2 is +inf", result (CorrectlyRounded.compound (b16 0x7C00) 2) == (0x7C00, 0)),
    ("exp2 16 toward zero is the largest finite value, overflow",
      result (CorrectlyRounded.exp2 (b16 0x4C00) .towardZero) == (0x7BFF, 20)),
    ("exp2 16 toward positive is +inf, overflow",
      result (CorrectlyRounded.exp2 (b16 0x4C00) .up) == (0x7C00, 20)),
    ("exp2 -25 toward positive is the least subnormal, underflow",
      result (CorrectlyRounded.exp2 (b16 0xCE40) .up) == (0x0001, 24)),
    ("exp2 -25 toward zero is +0, underflow",
      result (CorrectlyRounded.exp2 (b16 0xCE40) .towardZero) == (0x0000, 24)),
    ("exp2 -25 to nearest with ties away is the least subnormal, underflow",
      result (CorrectlyRounded.exp2 (b16 0xCE40) .nearestAway) == (0x0001, 24)),
    ("exp2 3 toward negative is 8, exact", result (CorrectlyRounded.exp2 (b16 0x4200) .down) ==
      (0x4800, 0)),
    ("atan +inf toward positive is the value above pi/2",
      result (CorrectlyRounded.atan (b16 0x7C00) .up) == (0x3E49, 16)),
    ("atan -inf toward positive is the value above -pi/2",
      result (CorrectlyRounded.atan (b16 0xFC00) .up) == (0xBE48, 16)),
    ("atan2 +0 -1 toward zero is the value below pi",
      result (CorrectlyRounded.atan2 (b16 0x0000) (b16 0xBC00) .towardZero) == (0x4248, 16)),
    ("atan2 +0 -1 toward positive is the value above pi",
      result (CorrectlyRounded.atan2 (b16 0x0000) (b16 0xBC00) .up) == (0x4249, 16)),
    ("log2 1 toward negative is +0", result (CorrectlyRounded.log2 (b16 0x3C00) .down) ==
      (0x0000, 0)),
    ("tanh +inf toward negative is 1", result (CorrectlyRounded.tanh (b16 0x7C00) .down) ==
      (0x3C00, 0)) ]

/--
Results in `Wide`, whose exponent range ends at `2 ^ (2 ^ 34)`: the rounding has to find the
binade of the result without building that power. The expected values are the correctly rounded
five-bit significands of `sin 1`, `sqrt 2`, `pi / 4` and `10 ^ 100 / 2 ^ 332`, and the exact
powers of two. The last two cases are the powers that `powerBounds` places around three.
-/
def wideCases : List (String × Bool) :=
  [ ("sin 1 is 27/32",
      wideResult (CorrectlyRounded.sin (wide false 0 0)) == (wideBits false (-1) 11, true)),
    ("sin 1 toward zero is 26/32",
      wideResult (CorrectlyRounded.sin (wide false 0 0) .towardZero) ==
        (wideBits false (-1) 10, true)),
    ("exp2 1/2 is 23/16",
      wideResult (CorrectlyRounded.exp2 (wide false (-1) 0)) == (wideBits false 0 7, true)),
    ("exp2 1/2 toward negative is 22/16",
      wideResult (CorrectlyRounded.exp2 (wide false (-1) 0) .down) == (wideBits false 0 6, true)),
    ("atan 1 is 25/32",
      wideResult (CorrectlyRounded.atan (wide false 0 0)) == (wideBits false (-1) 9, true)),
    ("atan 1 toward positive is 26/32",
      wideResult (CorrectlyRounded.atan (wide false 0 0) .up) == (wideBits false (-1) 10, true)),
    ("exp2 992 is 2 ^ 992",
      wideResult (CorrectlyRounded.exp2 (wide false 9 15)) == (wideBits false 992 0, false)),
    ("exp2 -992 is 2 ^ -992",
      wideResult (CorrectlyRounded.exp2 (wide true 9 15)) == (wideBits false (-992) 0, false)),
    ("log2 of 2 ^ -992 is -992",
      wideResult (CorrectlyRounded.log2 (wide false (-992) 0)) == (wideBits true 9 15, false)),
    ("exp10 100 is 18/16 * 2 ^ 332",
      wideResult (CorrectlyRounded.exp10 (wide false 6 9)) == (wideBits false 332 2, true)),
    ("exp10 100 toward positive is 19/16 * 2 ^ 332",
      wideResult (CorrectlyRounded.exp10 (wide false 6 9) .up) == (wideBits false 332 3, true)),
    ("three is below 2 ^ 2",
      (Model.AlgebraicRounding.powerBounds (FloatFormat.ieee 35 4)
        fun candidate => cmp (3 : ℚ) candidate).above == some 2),
    ("three is above 2 ^ 0",
      (Model.AlgebraicRounding.powerBounds (FloatFormat.ieee 35 4)
        fun candidate => cmp (3 : ℚ) candidate).below == some 0) ]

open Model.Transcendentals.CorrectlyRounded in
/-- The members of `Function` with their names. -/
def members : List (String × Function) :=
  [("exp2", .exp2), ("exp2m1", .exp2m1), ("exp10", .exp10), ("exp10m1", .exp10m1),
    ("log2", .log2), ("log10", .log10), ("log2p1", .log2p1), ("log10p1", .log10p1),
    ("sin", .sin), ("cos", .cos), ("tan", .tan), ("sinPi", .sinPi), ("cosPi", .cosPi),
    ("tanPi", .tanPi), ("asin", .asin), ("acos", .acos), ("atan", .atan), ("asinPi", .asinPi),
    ("acosPi", .acosPi), ("atanPi", .atanPi), ("sinh", .sinh), ("cosh", .cosh), ("tanh", .tanh),
    ("asinh", .asinh), ("acosh", .acosh), ("atanh", .atanh)]

/-- A model outcome as its encoding, its five flags and its ternary value. -/
def modelResult (outcome : Model.IEEEOutcome FloatFormat.binary16) :
    Nat × List Bool × Ordering :=
  (outcome.value.toNatBits,
    [outcome.status.invalid, outcome.status.divideByZero, outcome.status.overflow,
      outcome.status.underflow, outcome.status.inexact],
    outcome.ternary)

open Model.Transcendentals.CorrectlyRounded in
/--
The enclosure hint does not change an outcome: for every member of `Function` and ten binary16
operands (subnormal, small, near one, large, of both signs), `Function.apply`, which tries an
enclosure first, delivers the value, the flags and the ternary value of the comparisons alone,
and so do `atan2`, `atan2Pi`, `powr`, `pow` and `compound` on ten pairs of these operands.
-/
def hintCases : List (String × Bool) :=
  let operands : List (Model FloatFormat.binary16) :=
    [0x0001, 0x03FF, 0x2E66, 0x3555, 0x3C00, 0x4248, 0x5640, 0x8400, 0xB99A, 0xC100].map
      Model.ofNatBits
  let levels := Function.levels FloatFormat.binary16
  let pairs := operands.zip operands.rotateLeft
  (members.flatMap fun (name, function) =>
    operands.map fun x =>
      (s!"{name} of the binary16 encoding {x.toNatBits} with and without the enclosure",
        modelResult (function.apply x) ==
          modelResult (Model.ComparisonRounding.unary (function.rule levels) x))) ++
  pairs.flatMap fun (x, y) =>
    [(s!"atan2 of the encodings {x.toNatBits} and {y.toNatBits} with and without the enclosure",
        modelResult (atan2 x y) ==
          modelResult (Model.ComparisonRounding.binary (angleRule false levels) x y)),
      (s!"atan2Pi of the encodings {x.toNatBits} and {y.toNatBits}",
        modelResult (atan2Pi x y) ==
          modelResult (Model.ComparisonRounding.binary (angleRule true levels) x y)),
      (s!"powr of the encodings {x.toNatBits} and {y.toNatBits}",
        modelResult (powr x y) == modelResult (Model.ComparisonRounding.binary powrRule x y)),
      (s!"pow of the encodings {x.toNatBits} and {y.toNatBits}",
        modelResult (pow x y) == modelResult (Model.ComparisonRounding.binary powRule x y)),
      (s!"compound of the encoding {x.toNatBits} with exponent 3",
        modelResult (compound x 3) ==
          modelResult (Model.ComparisonRounding.unary (compoundRule 3) x))]

#eval show IO Unit from do
  let failures := (cases ++ wideCases ++ hintCases).filter fun entry => !entry.2
  unless failures.isEmpty do
    throw <| IO.userError s!"special cases that fail: {failures.map (·.1)}"
  IO.println <| s!"{cases.length} special cases of the recommended functions hold, " ++
    s!"{wideCases.length} results with 35 exponent bits, and {hintCases.length} outcomes " ++
    "agree with and without the enclosure"

/-! ## The theorems on binary64 -/

section Contracts

open Model.Transcendentals.CorrectlyRounded

variable {x y : Model FloatFormat.binary64} {p q : ℚ}

/-- A named function is its member of the enumeration, so the one theorem applies to it. -/
example (hq : Model.toRat? x = some q) (hfinite : Model.isFinite (sin x).value = true) :
    Model.toReal (sin x).value = Model.roundAt FloatFormat.binary64 (Real.sin q) :=
  Function.toReal_apply rfl .sin hq trivial hfinite

example (hq : Model.toRat? x = some q) (hdomain : 0 < q)
    (hfinite : Model.isFinite (log2 x).value = true) :
    Model.toReal (log2 x).value = Model.roundAt FloatFormat.binary64 (Real.logb 2 q) :=
  Function.toReal_apply rfl .log2 hq hdomain hfinite

example (hq : Model.toRat? x = some q) (hdomain : -1 < q ∧ q < 1)
    (hfinite : Model.isFinite (atanh x).value = true) :
    (atanh x).status.inexact = true ↔ Model.toReal (atanh x).value ≠ Real.artanh q :=
  Function.inexact_apply_iff .atanh hq hdomain .nearest hfinite

/-- In every rounding direction `inexact` says that the result is not the real value. -/
example (mode : Model.IEEERoundingMode) (hq : Model.toRat? x = some q)
    (hfinite : Model.isFinite (sinh x mode).value = true) :
    (sinh x mode).status.inexact = true ↔ Model.toReal (sinh x mode).value ≠ Real.sinh q :=
  Function.inexact_apply_iff .sinh hq trivial mode hfinite

/-- The results toward negative and toward positive infinity enclose the real function. -/
example (hq : Model.toRat? x = some q) :
    Model.toEReal (sin x .down).value ≤ (Real.sin q : EReal) ∧
      (Real.sin q : EReal) ≤ Model.toEReal (sin x .up).value :=
  Function.apply_encloses rfl .sin hq trivial

example (hq : Model.toRat? x = some q) (hdomain : 0 < q) :
    Model.toEReal (log10 x .down).value ≤ (Real.logb 10 q : EReal) ∧
      (Real.logb 10 q : EReal) ≤ Model.toEReal (log10 x .up).value :=
  Function.apply_encloses rfl .log10 hq hdomain

example (hx : Model.toRat? x = some p) (hy : Model.toRat? y = some q) (hp : 0 < p) :
    Model.toEReal (powr x y .down).value ≤ (((p : ℝ) ^ (q : ℝ) : ℝ) : EReal) ∧
      (((p : ℝ) ^ (q : ℝ) : ℝ) : EReal) ≤ Model.toEReal (powr x y .up).value :=
  powr_encloses rfl hx hy hp

example (hy : Model.toRat? y = some q) (hx : Model.toRat? x = some p) (hne : q ≠ 0) :
    Model.toEReal (atan2 y x .down).value ≤ (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ : EReal) ∧
      (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ : EReal) ≤ Model.toEReal (atan2 y x .up).value :=
  atan2_encloses rfl hy hx hne

/--
Every rounding direction: when the rounding of the real function in that direction is at most
the largest finite magnitude, the result is finite and is that rounding.
-/
example (mode : Model.IEEERoundingMode) (hq : Model.toRat? x = some q) (hne : Real.sinh q ≠ 0)
    (hrange : |Model.roundAt FloatFormat.binary64 (Real.sinh q) mode| ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary64)) :
    Model.isFinite (sinh x mode).value = true ∧
      Model.toReal (sinh x mode).value = Model.roundAt FloatFormat.binary64 (Real.sinh q) mode :=
  (Function.apply_roundsTo .sinh hq trivial hne).finite hrange

/-- Toward zero, a real value beyond the largest finite magnitude gives the largest finite
value of its sign, and toward positive infinity a positive one gives `+∞`. -/
example (hq : Model.toRat? x = some q)
    (hover : Model.toReal (Model.posMaxFinite FloatFormat.binary64) <
      |Model.roundAt FloatFormat.binary64 ((2 : ℝ) ^ (q : ℝ)) .towardZero|) :
    (exp2 x .towardZero).value = Model.maxFinite FloatFormat.binary64 false := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (q : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h := (Function.apply_roundsTo (mode := .towardZero) .exp2 hq trivial
    hpos.ne').overflow hover
  rw [show decide (Function.real .exp2 q < 0) = false from
    decide_eq_false (not_lt.mpr hpos.le)] at h
  exact h

/-- In a format with signed zeros the result has the sign of the real function, also when it
is a zero. -/
example (mode : Model.IEEERoundingMode) (hq : Model.toRat? x = some q) (hneg : Real.sin q < 0) :
    Model.signBit (sin x mode).value = true :=
  ((Function.apply_roundsTo .sin hq trivial hneg.ne).signBit rfl).trans
    (decide_eq_true hneg)

/-- A real value of zero gives a zero in every direction. -/
example (mode : Model.IEEERoundingMode) (hq : Model.toRat? x = some q) (hdomain : 0 < q)
    (hzero : Real.logb 2 q = 0) : Model.isZero (log2 x mode).value = true :=
  Function.isZero_apply .log2 hq hdomain hzero mode

/-- The functions of two operands in every direction. -/
example (mode : Model.IEEERoundingMode) (hx : Model.toRat? x = some p)
    (hy : Model.toRat? y = some q) (hp : 0 < p) :
    Model.RoundsTo FloatFormat.binary64 mode ((p : ℝ) ^ (q : ℝ)) false (powr x y mode).value :=
  powr_roundsTo hx hy hp

example (mode : Model.IEEERoundingMode) (hx : Model.toRat? x = some p)
    (hy : Model.toRat? y = some q) (hp : 0 < p) :
    Model.RoundsTo FloatFormat.binary64 mode ((p : ℝ) ^ (q : ℝ)) false (pow x y mode).value :=
  pow_roundsTo_of_pos hx hy hp

example (mode : Model.IEEERoundingMode) (n : ℤ) (hx : Model.toRat? x = some p)
    (hy : Model.toRat? y = some (n : ℚ)) (hp : p < 0) :
    Model.RoundsTo FloatFormat.binary64 mode ((p : ℝ) ^ n) (decide ((p : ℝ) ^ n < 0))
      (pow x y mode).value :=
  pow_roundsTo_of_neg hx hy hp

example (mode : Model.IEEERoundingMode) (hx : Model.toRat? x = some q) (hq : -1 < q) (n : ℤ) :
    Model.RoundsTo FloatFormat.binary64 mode ((1 + (q : ℝ)) ^ (n : ℝ)) false
      (compound x n mode).value :=
  compound_roundsTo hx hq n

example (mode : Model.IEEERoundingMode) (hy : Model.toRat? y = some q)
    (hx : Model.toRat? x = some p) (hne : q ≠ 0) :
    Model.RoundsTo FloatFormat.binary64 mode (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩) (decide (q < 0))
      (atan2 y x mode).value :=
  atan2_roundsTo hy hx hne

example (mode : Model.IEEERoundingMode) (hy : Model.toRat? y = some q)
    (hx : Model.toRat? x = some p) (hne : q ≠ 0) :
    Model.RoundsTo FloatFormat.binary64 mode (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ / Real.pi)
      (decide (q < 0)) (atan2Pi y x mode).value :=
  atan2Pi_roundsTo hy hx hne

/--
The overflow flag is the overflow of IEEE 754-2019 §7.4 in every direction: it is raised exactly
when the rounding of the real value with an unbounded exponent range exceeds the largest finite
value in magnitude.
-/
example (mode : Model.IEEERoundingMode) (hq : Model.toRat? x = some q) :
    (exp2 x mode).status.overflow = true ↔
      Model.toReal (Model.posMaxFinite FloatFormat.binary64) <
        |Model.roundAt FloatFormat.binary64 ((2 : ℝ) ^ (q : ℝ)) mode| :=
  Function.overflow_apply_iff .exp2 hq trivial
    (Real.rpow_pos_of_pos (by norm_num) _).ne' mode

example (mode : Model.IEEERoundingMode) (n : ℤ) {w : Model FloatFormat.binary64} {r : ℚ}
    (hx : Model.toRat? x = some p) (hy : Model.toRat? y = some q)
    (hinteger : Model.toRat? y = some (n : ℚ)) (hw : Model.toRat? w = some r) (hp : 0 < p)
    (hr : r < 0) :
    ((powr x y mode).status.overflow = true ↔
        Model.toReal (Model.posMaxFinite FloatFormat.binary64) <
          |Model.roundAt FloatFormat.binary64 ((p : ℝ) ^ (q : ℝ)) mode|) ∧
      ((pow x y mode).status.overflow = true ↔
        Model.toReal (Model.posMaxFinite FloatFormat.binary64) <
          |Model.roundAt FloatFormat.binary64 ((p : ℝ) ^ (q : ℝ)) mode|) ∧
      ((compound x n mode).status.overflow = true ↔
        Model.toReal (Model.posMaxFinite FloatFormat.binary64) <
          |Model.roundAt FloatFormat.binary64 ((1 + (p : ℝ)) ^ (n : ℝ)) mode|) ∧
      ((pow w y mode).status.overflow = true ↔
        Model.toReal (Model.posMaxFinite FloatFormat.binary64) <
          |Model.roundAt FloatFormat.binary64 ((r : ℝ) ^ n) mode|) :=
  ⟨powr_overflow_iff hx hy hp mode, pow_overflow_iff_of_pos hx hy hp mode,
    compound_overflow_iff hx (by linarith) n mode, pow_overflow_iff_of_neg hw hinteger hr mode⟩

/-- A finite operand in the domain raises neither `invalid` nor `divideByZero`. -/
example (mode : Model.IEEERoundingMode) (hx : Model.toRat? x = some p)
    (hy : Model.toRat? y = some q) (hp : 0 < p) :
    ((atanh x mode).status.invalid = false ∨ ¬Function.atanh.Domain p) ∧
      (powr x y mode).status.divideByZero = false :=
  ⟨Classical.byCases
      (fun hdomain : Function.atanh.Domain p =>
        .inl (Function.invalid_divideByZero_apply .atanh hx hdomain mode).1) .inr,
    (Model.ComparisonRounding.binary_invalid_divideByZero powrRule hx hy (locates_powr _ _ hp)
      mode _).2⟩

example (mode : Model.IEEERoundingMode) (hy : Model.toRat? y = some q)
    (hx : Model.toRat? x = some p) (hne : q ≠ 0) :
    (atan2 y x mode).status.overflow = true ↔
      Model.toReal (Model.posMaxFinite FloatFormat.binary64) <
        |Model.roundAt FloatFormat.binary64 (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩) mode| :=
  (atan2_overflow_iff hy hx hne mode).1

/--
The underflow flag is the underflow of IEEE 754-2019 §7.5 in every direction: it is raised
exactly when the result is inexact and the magnitude of the real value is tiny after rounding.
-/
example (mode : Model.IEEERoundingMode) (hq : Model.toRat? x = some q) :
    (exp2 x mode).status.underflow = true ↔
      (exp2 x mode).status.inexact = true ∧
        Model.AlgebraicRounding.TinyAfterRounding FloatFormat.binary64
          (mode.magnitudeRounding (decide ((2 : ℝ) ^ (q : ℝ) < 0))) |(2 : ℝ) ^ (q : ℝ)| :=
  Function.underflow_apply_iff .exp2 hq trivial
    (Real.rpow_pos_of_pos (by norm_num) _).ne' mode

example (mode : Model.IEEERoundingMode) (n : ℤ) {w : Model FloatFormat.binary64} {r : ℚ}
    (hx : Model.toRat? x = some p) (hy : Model.toRat? y = some q)
    (hinteger : Model.toRat? y = some (n : ℚ)) (hw : Model.toRat? w = some r) (hp : 0 < p)
    (hr : r < 0) (hne : q ≠ 0) :
    ((powr x y mode).status.underflow = true → (powr x y mode).status.inexact = true) ∧
      ((pow x y mode).status.underflow = true → (pow x y mode).status.inexact = true) ∧
      ((compound x n mode).status.underflow = true →
        (compound x n mode).status.inexact = true) ∧
      ((pow w y mode).status.underflow = true → (pow w y mode).status.inexact = true) ∧
      ((atan2 y x mode).status.underflow = true → (atan2 y x mode).status.inexact = true) ∧
      ((atan2Pi y x mode).status.underflow = true → (atan2Pi y x mode).status.inexact = true) :=
  ⟨fun h => ((powr_underflow_iff hx hy hp mode).mp h).1,
    fun h => ((pow_underflow_iff_of_pos hx hy hp mode).mp h).1,
    fun h => ((compound_underflow_iff hx (by linarith) n mode).mp h).1,
    fun h => ((pow_underflow_iff_of_neg hw hinteger hr mode).mp h).1,
    fun h => (((atan2_underflow_iff hy hx hne mode).1).mp h).1,
    fun h => (((atan2_underflow_iff hy hx hne mode).2).mp h).1⟩

/-- The functions of two arguments raise neither `invalid` nor `divideByZero` at finite
operands in the domain. -/
example (mode : Model.IEEERoundingMode) (n : ℤ) {w : Model FloatFormat.binary64} {r : ℚ}
    (hx : Model.toRat? x = some p) (hy : Model.toRat? y = some q)
    (hinteger : Model.toRat? y = some (n : ℚ)) (hw : Model.toRat? w = some r) (hp : 0 < p)
    (hr : r < 0) (hne : q ≠ 0) :
    (powr x y mode).status.invalid = false ∧ (pow x y mode).status.invalid = false ∧
      (compound x n mode).status.divideByZero = false ∧
      (pow w y mode).status.invalid = false ∧ (atan2 y x mode).status.invalid = false ∧
      (atan2Pi y x mode).status.divideByZero = false :=
  ⟨(powr_invalid_divideByZero hx hy hp mode).1,
    (pow_invalid_divideByZero_of_pos hx hy hp mode).1,
    (compound_invalid_divideByZero hx (by linarith) n mode).2,
    (pow_invalid_divideByZero_of_neg hw hinteger hr mode).1,
    (atan2_invalid_divideByZero hy hx hne mode).1.1,
    (atan2_invalid_divideByZero hy hx hne mode).2.2⟩

/-- The functions of two arguments raise `inexact` exactly when a finite result is not the real
value. -/
example (mode : Model.IEEERoundingMode) (n : ℤ) {w : Model FloatFormat.binary64} {r : ℚ}
    (hx : Model.toRat? x = some p) (hy : Model.toRat? y = some q)
    (hinteger : Model.toRat? y = some (n : ℚ)) (hw : Model.toRat? w = some r) (hp : 0 < p)
    (hr : r < 0) (hne : q ≠ 0)
    (hpowr : Model.isFinite (powr x y mode).value = true)
    (hpow : Model.isFinite (pow x y mode).value = true)
    (hcompound : Model.isFinite (compound x n mode).value = true)
    (hnegative : Model.isFinite (pow w y mode).value = true)
    (hangle : Model.isFinite (atan2 y x mode).value = true)
    (hturn : Model.isFinite (atan2Pi y x mode).value = true) :
    ((powr x y mode).status.inexact = true ↔
        Model.toReal (powr x y mode).value ≠ (p : ℝ) ^ (q : ℝ)) ∧
      ((pow x y mode).status.inexact = true ↔
        Model.toReal (pow x y mode).value ≠ (p : ℝ) ^ (q : ℝ)) ∧
      ((compound x n mode).status.inexact = true ↔
        Model.toReal (compound x n mode).value ≠ (1 + (p : ℝ)) ^ (n : ℝ)) ∧
      ((pow w y mode).status.inexact = true ↔
        Model.toReal (pow w y mode).value ≠ (r : ℝ) ^ n) ∧
      ((atan2 y x mode).status.inexact = true ↔
        Model.toReal (atan2 y x mode).value ≠ Complex.arg ⟨(p : ℝ), (q : ℝ)⟩) ∧
      ((atan2Pi y x mode).status.inexact = true ↔
        Model.toReal (atan2Pi y x mode).value ≠ Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ / Real.pi) :=
  ⟨powr_inexact_iff hx hy hp mode hpowr, pow_inexact_iff_of_pos hx hy hp mode hpow,
    compound_inexact_iff hx (by linarith) n mode hcompound,
    pow_inexact_iff_of_neg hw hinteger hr mode hnegative,
    atan2_inexact_iff hy hx hne mode hangle, atan2Pi_inexact_iff hy hx hne mode hturn⟩

/-- The comparator-level statement, with a comparator that exists: the one of a rational. -/
example (mode : Model.IEEERoundingMode) :
    Model.RoundsTo FloatFormat.binary64 mode (((1 / 3 : ℚ) : ℝ)) false
      (Model.ComparisonRounding.round FloatFormat.binary64
        (fun candidate => cmp (1 / 3 : ℚ) candidate) mode) := by
  have h := Model.ComparisonRounding.round_roundsTo (fmt := FloatFormat.binary64) (mode := mode)
    _ (by norm_num) (Model.ComparisonRounding.Rule.locates_rational (1 / 3))
  have hsign : decide ((((1 / 3 : ℚ) : ℝ)) < 0) = false := decide_eq_false (by norm_num)
  rwa [hsign] at h

/-- The enclosure search is right about the function, so the theorems apply to its results. -/
example (negative : Bool) (hq : (0 : ℚ) < q) :
    Model.ComparisonRounding.Hint.Sound
      (Function.hint FloatFormat.binary64 .log2 (.finite negative q)) (Real.logb 2 q) :=
  Function.hint_sound .log2 negative hq

example (hy : Model.toRat? y = some q) (hx : Model.toRat? x = some p) (hne : q ≠ 0) :
    Model.toEReal (atan2Pi y x .down).value ≤
        ((Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ / Real.pi : ℝ) : EReal) ∧
      ((Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ / Real.pi : ℝ) : EReal) ≤
        Model.toEReal (atan2Pi y x .up).value :=
  atan2Pi_encloses rfl hy hx hne

example (hx : Model.toRat? x = some q) (hq : -1 < q) (n : ℤ) :
    Model.toEReal (compound x n .down).value ≤ (((1 + (q : ℝ)) ^ (n : ℝ) : ℝ) : EReal) ∧
      (((1 + (q : ℝ)) ^ (n : ℝ) : ℝ) : EReal) ≤ Model.toEReal (compound x n .up).value :=
  compound_encloses rfl hx hq n

/-- A delivery without a hint is covered by the same theorems: no result is a sound hint. -/
example (compare : ℚ → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hfinite : Model.isFinite
      (Model.ComparisonRounding.deliver FloatFormat.binary64 compare).value = true) :
    Model.toReal (Model.ComparisonRounding.deliver FloatFormat.binary64 compare).value =
      Model.roundAt FloatFormat.binary64 target :=
  Model.ComparisonRounding.toReal_deliver rfl compare target hcompare
    (Model.ComparisonRounding.Hint.sound_none target) hfinite

/-- The comparator-level enclosure, with a comparator that exists: the one of a rational. -/
example :
    Model.toEReal (Model.ComparisonRounding.round FloatFormat.binary64
      (fun candidate => cmp (1 / 3 : ℚ) candidate) .down) ≤ (((1 / 3 : ℚ) : ℝ) : EReal) :=
  Model.ComparisonRounding.toEReal_round_down_le rfl _ _
    (Model.ComparisonRounding.Rule.locates_rational (1 / 3))

example (hx : Model.toRat? x = some p) (hy : Model.toRat? y = some q) (hp : 0 < p)
    (hfinite : Model.isFinite (powr x y).value = true) :
    Model.toReal (powr x y).value = Model.roundAt FloatFormat.binary64 ((p : ℝ) ^ (q : ℝ)) :=
  toReal_powr rfl hx hy hp hfinite

example (hx : Model.toRat? x = some q) (hq : -1 < q) (n : ℤ)
    (hfinite : Model.isFinite (compound x n).value = true) :
    Model.toReal (compound x n).value =
      Model.roundAt FloatFormat.binary64 ((1 + (q : ℝ)) ^ (n : ℝ)) :=
  toReal_compound rfl hx hq n hfinite

example (hy : Model.toRat? y = some q) (hx : Model.toRat? x = some p) (hne : q ≠ 0)
    (hfinite : Model.isFinite (atan2 y x).value = true) :
    Model.toReal (atan2 y x).value =
      Model.roundAt FloatFormat.binary64 (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩) :=
  toReal_atan2 rfl hy hx hne hfinite

example (hy : Model.toRat? y = some q) (hx : Model.toRat? x = some p) (hne : q ≠ 0)
    (hfinite : Model.isFinite (atan2Pi y x).value = true) :
    Model.toReal (atan2Pi y x).value =
      Model.roundAt FloatFormat.binary64 (Complex.arg ⟨(p : ℝ), (q : ℝ)⟩ / Real.pi) :=
  toReal_atan2Pi rfl hy hx hne hfinite

/-- The enclosure search gives a value with the sign of the function, a zero included. -/
example (negative : Bool) (hq : (0 : ℚ) < q) :
    Model.ComparisonRounding.Hint.Signed
      (Function.hint FloatFormat.binary64 .log2 (.finite negative q)) (Real.logb 2 q) :=
  Function.hint_signed .log2 negative hq

/-- A comparison with a power of two that is read off `powerBounds` is the comparator's answer. -/
example (compare : ℚ → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)) (exponent : ℤ) :
    (Model.AlgebraicRounding.powerBounds FloatFormat.binary64 compare).compare compare exponent =
      compare (Model.AlgebraicRounding.powerOfTwo exponent) :=
  Model.AlgebraicRounding.powerBounds_compare FloatFormat.binary64 hcompare exponent

/-- The flags of a rounding by comparisons, and the rule of an exact rational value. -/
example (compare : ℚ → Ordering) (mode : Model.IEEERoundingMode)
    (h : Model.isFinite (Model.ComparisonRounding.round FloatFormat.binary64 compare mode) =
      false) :
    (Model.ComparisonRounding.deliver FloatFormat.binary64 compare mode).status.overflow = true :=
  Model.ComparisonRounding.deliver_overflow_of_isFinite_eq_false compare mode h

example : (Model.ComparisonRounding.Rule.rational (1 / 2)).Locates ((1 / 2 : ℚ) : ℝ) :=
  Model.ComparisonRounding.Rule.locates_rational _

/-- The configured form on binary64, with the format premise discharged by `ieee_format`. -/
example {value : Binary64} (hvalue : ExecFloat.Binary.toRat? value = some q)
    (hfinite : ExecFloat.Binary.isFinite (CorrectlyRounded.cosh value).value = true) :
    ExecFloat.Binary.toReal (CorrectlyRounded.cosh value).value =
      Model.roundAt FloatFormat.binary64 (Real.cosh q) :=
  CorrectlyRounded.toReal_apply .cosh hvalue trivial hfinite

/-- The configured form in every direction. -/
example {value : Binary64} (mode : Model.IEEERoundingMode)
    (hvalue : ExecFloat.Binary.toRat? value = some q) :
    Model.RoundsTo FloatFormat.binary64 mode (Real.cosh q) false
      (ExecFloat.Binary.toModel (CorrectlyRounded.cosh value mode).value) := by
  have hpos : 0 < Real.cosh q := Real.cosh_pos _
  have h := CorrectlyRounded.apply_roundsTo .cosh hvalue trivial hpos.ne' mode
  rw [show decide (Function.real .cosh q < 0) = false from
    decide_eq_false (not_lt.mpr hpos.le)] at h
  exact h

end Contracts

end FloatLibTests.Conformance.BinaryInterchange.RecommendedFunctions
