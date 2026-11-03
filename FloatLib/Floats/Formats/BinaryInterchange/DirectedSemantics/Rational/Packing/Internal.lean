/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime

/-!
# Internal lemmas for directed rational packing

The rational packing proofs share three IEEE facts: subnormal fields are finite, the smallest
normal field pair is finite, and positive upward overflow produces positive infinity.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Packing.Internal

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
section

/--
An IEEE word with a zero exponent field denotes a finite value. `ofFields` truncates the fraction
to the descriptor width, so the fraction needs no bound.
-/
theorem isFinite_ofFields_subnormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mantissa : Nat) :
    isFinite (ofFields fmt false 0 mantissa) = true :=
  isFinite_ofFields_ieee fmt hfmt false 0 mantissa fmt.expAllOnesNat_pos

/-- The minimum-normal field pair denotes a finite value in every encoding. -/
theorem isFinite_ofFields_minNormal (fmt : FloatFormat) :
    isFinite (ofFields fmt false 1 0) = true := by
  have hone := FloatFormat.one_lt_expAllOnesNat fmt
  have hexponent : 1 < 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat at hone
    omega
  rw [isFinite_ofFields fmt false 1 0 hexponent (Nat.two_pow_pos _)]
  cases fmt.encoding <;> simp [Nat.ne_of_lt hone]

/-- Positive IEEE overflow rounds to positive infinity when the direction is upward. -/
theorem directedOverflow_false_true_eq_posInf
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    directedOverflow fmt false true = posInf fmt := by
  simp [directedOverflow, nativeOverflow,
    FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt]

end

end Packing.Internal
end Model
end FloatLib.Floats.Formats.BinaryInterchange
