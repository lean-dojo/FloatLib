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
noncomputable section

/-- An in-range IEEE subnormal fraction field denotes a finite value. -/
theorem isFinite_ofFields_subnormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mantissa : Nat)
    (_hmantissa : mantissa < 2 ^ fmt.fracWidth) :
    isFinite (ofFields fmt false 0 mantissa) = true :=
  isFinite_ofFields_ieee fmt hfmt false 0 mantissa fmt.expAllOnesNat_pos

/-- The canonical IEEE minimum-normal field pair denotes a finite value. -/
theorem isFinite_ofFields_minNormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    isFinite (ofFields fmt false 1 0) = true :=
  isFinite_ofFields_ieee fmt hfmt false 1 0
    (by
      have hfour : 4 ≤ 2 ^ fmt.expWidth := by
        simpa using
          Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
            fmt.expWidth_ge_two
      unfold FloatFormat.expAllOnesNat
      omega)

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
