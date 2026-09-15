/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Exact.Runtime
public import FloatLib.Numerics.Representations.FixedInt.Core
public import Mathlib.Data.Rat.Defs

/-!
# Bounded fixed-point execution

A bounded fixed-point code stores its coefficient in `FixedInt width` and interprets that signed
integer at a fixed radix scale. Arithmetic names state their overflow policy explicitly:

* wrapping addition and subtraction use direct `BitVec` arithmetic;
* wrapping multiplication sign-extends or truncates both inputs to the destination width before
  multiplying;
* checked operations return `none` when the exact coefficient is out of range;
* saturating operations clamp the exact coefficient to the destination range.

Multiplication composes scales: operands with `p` and `q` fractional digits produce `p + q`
fractional digits. The destination width is independent of the two input widths.
-/

@[expose] public section

open FloatLib.Numerics
open FloatLib.Numerics.Representations

namespace FloatLib.Floats.Formats.FixedPoint.Bounded

/--
A signed `width`-bit coefficient interpreted with a fixed radix scale.

This is a transparent type definition rather than an abbreviation. It has exactly the
`FixedInt width` runtime representation, while retaining the radix and scale in elaborated type
expressions so proof-aware tooling can identify the numerical format.
-/
@[reducible] def Code (_radix : Radix) (_fractionalDigits : Nat) (width : Nat) :=
  FixedInt width

/-- Natural scaling denominator of a fixed-point format. -/
abbrev scale := FixedPoint.scale

/-- Signed integer coefficient stored by a bounded fixed-point code. -/
@[inline] def coefficient {width : Nat} (code : FixedInt width) : Int :=
  code.toInt

/-- Exact rational value of a bounded fixed-point code. -/
@[inline] def toRat (radix : Radix) (fractionalDigits : Nat) {width : Nat}
    (code : FixedInt width) : ℚ :=
  coefficient code / (scale radix fractionalDigits : Nat)

/-- Encode an integer coefficient modulo `2 ^ width`. -/
@[inline] def ofInt (width : Nat) (value : Int) : FixedInt width :=
  FixedInt.ofInt value

/-- Addition modulo `2 ^ width`. -/
@[inline] def wrapAdd {width : Nat}
    (left right : FixedInt width) : FixedInt width :=
  FixedInt.wrapAdd left right

/-- Subtraction modulo `2 ^ width`. -/
@[inline] def wrapSub {width : Nat}
    (left right : FixedInt width) : FixedInt width :=
  FixedInt.wrapSub left right

/--
Multiplication modulo `2^outWidth`.

Both coefficients are resized in two's-complement form before the native `BitVec` product. This
implements exact multiplication followed by centered reduction at the destination width.
-/
@[inline] def wrapMul (outWidth : Nat) {leftWidth rightWidth : Nat}
    (left : FixedInt leftWidth) (right : FixedInt rightWidth) :
    FixedInt outWidth :=
  ⟨left.bits.signExtend outWidth * right.bits.signExtend outWidth⟩

/-- Return the exact same-scale sum when it fits the signed coefficient width. -/
@[inline] def checkedAdd {width : Nat}
    (left right : FixedInt width) : Option (FixedInt width) :=
  FixedInt.checkedAdd left right

/-- Return the exact same-scale difference when it fits the signed coefficient width. -/
@[inline] def checkedSub {width : Nat}
    (left right : FixedInt width) : Option (FixedInt width) :=
  FixedInt.checkedSub left right

/-- Return the exact product when its coefficient fits `outWidth` signed bits. -/
@[inline] def checkedMul (outWidth : Nat) {leftWidth rightWidth : Nat}
    (left : FixedInt leftWidth) (right : FixedInt rightWidth) :
    Option (FixedInt outWidth) :=
  let product := coefficient left * coefficient right
  if FixedInt.InRange outWidth product then
    some (FixedInt.ofInt product)
  else
    none

/-- Same-scale addition with saturation at the signed coefficient bounds. -/
@[inline] def saturatingAdd {width : Nat}
    (left right : FixedInt width) : FixedInt width :=
  FixedInt.saturatingAdd left right

/-- Same-scale subtraction with saturation at the signed coefficient bounds. -/
@[inline] def saturatingSub {width : Nat}
    (left right : FixedInt width) : FixedInt width :=
  FixedInt.saturatingSub left right

/-- Product with its exact coefficient saturated to `outWidth` signed bits. -/
@[inline] def saturatingMul (outWidth : Nat) {leftWidth rightWidth : Nat}
    (left : FixedInt leftWidth) (right : FixedInt rightWidth) :
    FixedInt outWidth :=
  FixedInt.ofIntSaturating (coefficient left * coefficient right)

end FloatLib.Floats.Formats.FixedPoint.Bounded
