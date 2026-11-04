/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime

/-!
# Standard interfaces for binary models

These instances give `Model fmt` Lean's ordinary numeric interfaces. Arithmetic, comparisons and
constants go straight to the format-generic executable kernels, and constants are built from
exact integers and rounded as the descriptor says.

Elementary functions, `Pow` and `MathFunctions` aren't installed here, so for those you import
`FloatLib.Floats.Formats.BinaryInterchange.Transcendentals` (or
`Configured.Transcendentals`) by name. Certified `sqrt` and `abs` stay on this path.

Natural numbers enter through `NatCast`, following mathlib. It isn't a `Coe`, because the map
rounds. Numerals resolve the way they do for any mathlib type with `Zero`, `One` and `NatCast`:
`0` is `posZero fmt`, `1` is `posOne fmt`, and `2`, `3`, ... are `Nat.cast` through mathlib's
`instOfNatAtLeastTwo`. With no `OfNat` instance of its own, `(0 : Model fmt)` and `Zero.zero` are
the same term.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Natural numbers are converted by one nearest-even rounding in the destination format.

Numerals `2`, `3`, ... resolve to this cast through mathlib's `instOfNatAtLeastTwo`.
-/
instance {fmt : FloatFormat} : NatCast (Model fmt) where
  natCast value := roundDyadic fmt { negative := false, significand := value, exponent := 0 }

/-- Positive zero in the destination format. -/
instance {fmt : FloatFormat} : Zero (Model fmt) where
  zero := posZero fmt

/-- Exact positive one in the destination format. -/
instance {fmt : FloatFormat} : One (Model fmt) where
  one := posOne fmt

/-- Unfolding lemma for the natural-number cast. -/
theorem natCast_def {fmt : FloatFormat} (value : Nat) :
    ((value : Nat) : Model fmt) =
      roundDyadic fmt { negative := false, significand := value, exponent := 0 } :=
  rfl

/-- The numeral `0` is the format's positive zero. -/
@[simp] theorem zero_eq_posZero {fmt : FloatFormat} : (0 : Model fmt) = posZero fmt :=
  rfl

/-- The numeral `1` is the format's exact positive one. -/
@[simp] theorem one_eq_posOne {fmt : FloatFormat} : (1 : Model fmt) = posOne fmt :=
  rfl

/-- Casting the natural number zero rounds to positive zero, so it agrees with the numeral `0`. -/
@[simp] theorem natCast_zero {fmt : FloatFormat} : ((0 : Nat) : Model fmt) = 0 := by
  change roundDyadic fmt { negative := false, significand := 0, exponent := 0 } = posZero fmt
  cases hieee : fmt.isIEEE
  · simp [roundDyadic, hieee, roundDyadicGeneral, zero]
  · simp [roundDyadic, hieee, ieeeRoundDyadic, posZero_eq_ofModel_zero]

/-- Negation with the descriptor's signed-zero and NaN conventions. -/
instance {fmt : FloatFormat} : Neg (Model fmt) where
  neg := neg

/-- Descriptor-aware nearest-even addition. -/
instance {fmt : FloatFormat} : Add (Model fmt) where
  add := add

/-- Descriptor-aware nearest-even subtraction. -/
instance {fmt : FloatFormat} : Sub (Model fmt) where
  sub := sub

/-- Descriptor-aware nearest-even multiplication. -/
instance {fmt : FloatFormat} : Mul (Model fmt) where
  mul := mul

/-- Descriptor-aware nearest-even division. -/
instance {fmt : FloatFormat} : Div (Model fmt) where
  div := div

/--
Boolean equality with IEEE NaN and signed-zero conventions.

NaNs compare unequal, the two zero encodings compare equal, and all other values compare by their
exact storage bits.
-/
instance {fmt : FloatFormat} : BEq (Model fmt) where
  beq left right :=
    if isNaN left || isNaN right then
      false
    else if isZero left && isZero right then
      true
    else
      left.bits == right.bits

/-- Strict IEEE numerical order. Unordered comparisons are false. -/
instance {fmt : FloatFormat} : LT (Model fmt) where
  lt := lt

/-- Non-strict IEEE numerical order. Unordered comparisons are false. -/
instance {fmt : FloatFormat} : LE (Model fmt) where
  le := le

/-- Decidability of the comparison-based strict order. -/
instance {fmt : FloatFormat} :
    DecidableRel ((· < ·) : Model fmt → Model fmt → Prop) := by
  intro left right
  change Decidable (lt left right)
  dsimp [lt]
  infer_instance

/-- Decidability of the comparison-based non-strict order. -/
instance {fmt : FloatFormat} :
    DecidableRel ((· ≤ ·) : Model fmt → Model fmt → Prop) := by
  intro left right
  change Decidable (le left right)
  dsimp [le]
  cases compare left right with
  | none => exact isFalse (by intro falseProof; cases falseProof)
  | some ordering =>
      cases ordering with
      | lt => exact isTrue trivial
      | eq => exact isTrue trivial
      | gt => exact isFalse (by intro falseProof; cases falseProof)

/-- IEEE `minimum`, including signed-zero and NaN propagation rules. -/
instance {fmt : FloatFormat} : Min (Model fmt) where
  min x y := minimum x y

/-- IEEE `maximum`, including signed-zero and NaN propagation rules. -/
instance {fmt : FloatFormat} : Max (Model fmt) where
  max x y := maximum x y

end Model
end FloatLib.Floats.Formats.BinaryInterchange
