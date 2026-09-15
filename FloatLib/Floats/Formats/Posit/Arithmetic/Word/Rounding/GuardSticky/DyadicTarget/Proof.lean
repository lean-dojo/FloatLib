/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.DyadicTarget.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Proof

/-!
# Correctness of exact-target guard-and-sticky dispatch

The executable capacity test changes representation only. Both branches are proved equal to the
shared arbitrary-width direct packer.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordRounding.GuardSticky.DyadicTarget

open FloatLib.Numerics

/-- Capacity-selected guard-and-sticky rounding is shared direct Posit rounding. -/
theorem roundCodeNat_eq_direct
    (format : Format) (heligible : NativeWord.Eligible format)
    (target : FloatLib.Numerics.Dyadic) :
    roundCodeNat format heligible target =
      DirectDyadicPacking.roundCode format target := by
  unfold roundCodeNat
  split
  next hfit =>
    rw [GuardSticky.roundCodeNat_eq_direct]
    apply congrArg (DirectDyadicPacking.roundCode format)
    apply FloatLib.Numerics.Dyadic.ext
    · rfl
    · exact UInt64.toNat_ofNat_of_lt hfit
    · rfl
  next =>
    rfl

/-- Capacity-selected exact-target rounding always returns a complete posit encoding. -/
theorem roundCodeNat_lt_modulus
    (format : Format) (heligible : NativeWord.Eligible format)
    (target : FloatLib.Numerics.Dyadic) :
    roundCodeNat format heligible target < format.modulus := by
  rw [roundCodeNat_eq_direct]
  exact DirectDyadicPacking.roundCode_lt_modulus format target

end FloatLib.Floats.Formats.Posit.Model.NativeWordRounding.GuardSticky.DyadicTarget
