/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Comparison.Runtime

/-!
# Executable exact-dyadic posit rounding

Finite posit inputs and the exact results of addition, subtraction, multiplication, and fused
multiply-add are dyadic. This module runs the standardized code search using aligned integer
comparisons instead of repeatedly materializing normalized rational values.

The search interval, `(n + 1)`-bit threshold rule, saturation behavior, tie-breaking rule, and
whole-word negative symmetry are identical to `Model.roundRat`. Refinement theorems live in
`Dyadic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DyadicRounding

/--
Exact dyadic value of the posit word with unsigned code `code`.

For `code < format.signMaskNat`, the value is nonnegative and finite. In general, `ofNatBits`
first reduces the code modulo the format's modulus. Zero and NaR map to `Dyadic.zero`; other
words decode with their sign.
-/
@[inline] def nonnegativeDyadicAt (format : Format) (code : Nat) : FloatLib.Numerics.Dyadic :=
  match Model.decodeExact (Model.ofNatBits (format := format) code) with
  | .zero => FloatLib.Numerics.Dyadic.zero
  | .finite fields => fields.toDyadic
  | .nar => FloatLib.Numerics.Dyadic.zero

/--
Exact smallest positive value in the dyadic comparison domain.

Code `1` has a unit significand and an all-zero regime prefix. Writing that value directly avoids
running the width-linear generic decoder for the same format constant on every rounding call.
-/
@[inline] def minPositive (format : Format) : FloatLib.Numerics.Dyadic :=
  {
    negative := false
    significand := 1
    exponent := -(4 * Int.ofNat (format.payloadBits - 1))
  }

/-- Exact `(n + 1)`-bit standard boundary above a retained `n`-bit code. -/
@[inline] def roundingThreshold (format : Format) (lowerCode : Nat) : FloatLib.Numerics.Dyadic :=
  nonnegativeDyadicAt format.nextPrecision (2 * lowerCode + 1)

/--
Greatest positive code accepted by exact dyadic comparison.

The shared bisection routine guarantees that the optimized and reference searches have identical
control flow once their comparison predicates are related.
-/
@[inline] def lowerCodeForPositive (format : Format) (target : FloatLib.Numerics.Dyadic) : Nat :=
  Model.lowerCodeByBisection
    (fun code => (nonnegativeDyadicAt format code).isLessOrEqual target)
    format.bits 0 format.signMaskNat

/--
Select a retained code by comparing the target with the exact appended-bit threshold.

A three-way comparison aligns the dyadic significands once. Equality selects the even retained
code, as required by the standard's tie rule.
-/
@[inline] def chooseNearestCode
    (target threshold : FloatLib.Numerics.Dyadic) (lower upper : Nat) : Nat :=
  match target.compare threshold with
  | .lt => lower
  | .eq => if lower % 2 = 0 then lower else upper
  | .gt => upper

/--
Round a positive exact dyadic value to a nonnegative posit code.

Zero and negative inputs map to zero, making the positive-rounding helper total. Arithmetic callers
pass a nonzero magnitude with `negative = false`.
-/
@[inline] def roundPositiveCode (format : Format) (target : FloatLib.Numerics.Dyadic) : Nat :=
  if target.significand == 0 || target.negative then
    0
  else if target.isLess (minPositive format) then
    1
  else
    let lower := lowerCodeForPositive format target
    let upper := lower + 1
    if upper < format.signMaskNat then
      let threshold := roundingThreshold format lower
      chooseNearestCode target threshold lower upper
    else
      lower

/-- Pack the nonnegative code selected by `roundPositiveCode`. -/
@[inline] def roundPositive (format : Format) (target : FloatLib.Numerics.Dyadic) : Model format :=
  Model.ofNatBits (roundPositiveCode format target)

/-- Clear the sign while preserving the exact dyadic magnitude fields. -/
@[inline] def magnitude (value : FloatLib.Numerics.Dyadic) : FloatLib.Numerics.Dyadic :=
  { value with negative := false }

/--
Restore a result sign directly on a complete posit encoding.

Every nonzero negative posit is the whole-word two's complement of its positive encoding. The
explicit zero branch preserves the standard's unique zero. This operation is independent
of the runtime carrier and is therefore shared by native-word and fixed-limb backends.
-/
@[inline] def restoreSignCode
    (format : Format) (negative : Bool) (positiveCode : Nat) : Nat :=
  if negative then
    if positiveCode == 0 then
      0
    else
      format.modulus - positiveCode
  else
    positiveCode

/--
Round any exact dyadic value using unique posit zero and whole-word negative symmetry.

The sign stored on an exact dyadic zero is forgotten because the Posit Standard (2022) has one
zero encoding.
-/
@[noinline] def round (format : Format) (value : FloatLib.Numerics.Dyadic) : Model format :=
  if value.significand == 0 then
    Model.zero format
  else
    let magnitude := magnitude value
    if value.negative then
      Model.neg (roundPositive format magnitude)
    else
      roundPositive format magnitude

end FloatLib.Floats.Formats.Posit.Model.DyadicRounding
