/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Order theory for exact dyadics

Here we show that the executable `cmpDyadic` comparison agrees with real order. The proof reduces
it to `cmpDyadicAligned`, which is the exact-dyadic comparator `Numerics.Dyadic.compare`. That
comparator orders the rational denotations (`Numerics.Dyadic.compare_eq_compare_toRat`), and the
cast to the reals preserves the order. `Dyadic.toReal_eq_signedSignificand_shiftLeft` states the
alignment of a significand at a smaller exponent in the reals.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

namespace Dyadic

/--
Real semantics after moving a dyadic significand to any smaller exponent.

The aligned integer is the exact signed significand at scale `2^exponent`.
-/
theorem toReal_eq_signedSignificand_shiftLeft (d : Numerics.Dyadic) (exponent : Int)
    (hexponent : exponent ≤ d.exponent) :
    d.toReal =
      ((Numerics.Dyadic.mk d.negative
          (Nat.shiftLeft d.significand (Int.toNat (d.exponent - exponent))) 0).signedSignificand : ℝ) *
        bpow Numerics.binaryRadix exponent := by
  have hnonneg : 0 ≤ d.exponent - exponent := sub_nonneg.mpr hexponent
  have htoNat : (Int.ofNat (Int.toNat (d.exponent - exponent))) = d.exponent - exponent := by
    simpa using Int.toNat_of_nonneg hnonneg
  have hpow :
      bpow Numerics.binaryRadix d.exponent =
        bpow Numerics.binaryRadix exponent *
          bpow Numerics.binaryRadix (d.exponent - exponent) := by
    have hadd : exponent + (d.exponent - exponent) = d.exponent := by omega
    simpa [hadd] using
      bpow.add_exp Numerics.binaryRadix exponent (d.exponent - exponent)
  let shift := Int.toNat (d.exponent - exponent)
  have hpowShift :
      bpow Numerics.binaryRadix (d.exponent - exponent) =
        bpow Numerics.binaryRadix (Int.ofNat shift) := by
    simpa [shift] using
      congrArg (fun value : Int => bpow Numerics.binaryRadix value) htoNat.symm
  have hshift :
      ((Numerics.Dyadic.mk d.negative (Nat.shiftLeft d.significand shift) 0).signedSignificand : ℝ) =
        (d.signedSignificand : ℝ) *
          bpow Numerics.binaryRadix (d.exponent - exponent) := by
    have hshiftNat := signedSignificand_shiftLeft d shift
    simpa [hpowShift] using hshiftNat
  rw [toReal_eq_signedSignificand, hpow]
  rw [show
    (d.signedSignificand : ℝ) *
        (bpow Numerics.binaryRadix exponent *
          bpow Numerics.binaryRadix (d.exponent - exponent)) =
      ((d.signedSignificand : ℝ) *
          bpow Numerics.binaryRadix (d.exponent - exponent)) *
        bpow Numerics.binaryRadix exponent by ring]
  simpa [shift, mul_assoc] using
    congrArg (fun value : ℝ => value * bpow Numerics.binaryRadix exponent) hshift.symm

end Dyadic

/-- Executable dyadic comparison is the comparison of the real values. -/
theorem cmpDyadic_eq_compare (a b : Numerics.Dyadic) :
    cmpDyadic a b = compare a.toReal b.toReal := by
  rw [cmpDyadic_eq_cmpDyadicAligned,
    show cmpDyadicAligned a b = Numerics.Dyadic.compare a b from rfl,
    Numerics.Dyadic.compare_eq_compare_toRat, ← Numerics.Dyadic.cast_toRat,
    ← Numerics.Dyadic.cast_toRat]
  simpa only [cmp_eq_compare] using
    ((Rat.cast_strictMono (K := ℝ)).cmp_map_eq a.toRat b.toRat).symm

/-- Executable dyadic comparison returns `.lt` if and only if the real values are ordered. -/
theorem cmpDyadic_lt_iff (a b : Numerics.Dyadic) :
    cmpDyadic a b = .lt ↔ a.toReal < b.toReal := by
  rw [cmpDyadic_eq_compare, compare_lt_iff_lt]

/-- Executable dyadic comparison returns `.eq` if and only if the real values are equal. -/
theorem cmpDyadic_eq_iff (a b : Numerics.Dyadic) :
    cmpDyadic a b = .eq ↔ a.toReal = b.toReal := by
  rw [cmpDyadic_eq_compare, compare_eq_iff_eq]

/-- Executable dyadic comparison returns `.gt` if and only if the real values are reversed. -/
theorem cmpDyadic_gt_iff (a b : Numerics.Dyadic) :
    cmpDyadic a b = .gt ↔ b.toReal < a.toReal := by
  rw [cmpDyadic_eq_compare, compare_gt_iff_gt]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
