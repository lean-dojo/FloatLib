/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath.Nearest
public meta import FloatLib.Tactic.NearestFlat

/-!
# Flat forms of MX element rounding

The shared bisection and its nearest-code proofs are in `KernelPath.Nearest`.
This module specializes their constants for every MX profile and registers the
conversion equation with the kernel evaluator.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics FloatLib.Floats.ExecFloat.KernelPath

/-! ## The forms that the kernel evaluates -/


/--
`nearest` with one flat test and one flat entry per sign-magnitude profile, and `int8Nearest`
with a flat test and a flat entry for INT8: the form that Lean's kernel evaluates
(`nearestAll_eq`, `nearestAll_int8`).
-/
noncomputable def nearestAll (profile : Profile) (sp neg ap q : Nat) : Nat :=
  Profile.casesOn (motive := fun _ => Nat) profile
    (nearest_flat% .e5m2 sp neg ap q 128 7) (nearest_flat% .e4m3 sp neg ap q 128 7)
    (nearest_flat% .e3m2 sp neg ap q 32 5) (nearest_flat% .e2m3 sp neg ap q 32 5)
    (nearest_flat% .e2m1 sp neg ap q 8 3)
    (int8NearestWith
      (fun i => kernel_inline% [int8Below] (int8Below sp (Nat.mul ap 64) q i))
      (fun i =>
        kernel_inline% [entry, int8Code, codeKey, distance, tie, magnitude, signBit,
            twosComplement, denominator, Profile.width]
          (entry .int8 sp neg ap q (int8Code sp i)))
      sp)

/-- The flat form is `nearest`, for every sign-magnitude profile. -/
theorem nearestAll_eq (profile : Profile) (h : twosComplement profile = false)
    (sp neg ap q : Nat) : nearestAll profile sp neg ap q = nearest profile sp neg ap q := by
  cases profile
  case int8 => cases h
  all_goals exact kernel_refl%

/-- The flat form is `int8Nearest` for INT8. -/
theorem nearestAll_int8 (sp neg ap q : Nat) :
    nearestAll .int8 sp neg ap q = int8Nearest sp neg ap q :=
  kernel_refl%

/--
The code that nearest-even rounding selects for `input`, with its rounding key above its `width`
bits: the bisection of the profile for the numerator and the denominator of the input and its
sign bit.
-/
noncomputable def roundCode (profile : Profile) (input : SignedRat) : Nat :=
  nearestAll profile (decide (input.value.num < 0)).toNat input.negative.toNat
    input.value.num.natAbs input.value.den

/--
Nearest-even element rounding by bisection, for every profile and every input: the word that
`quantizeFinite` selects is the low `width` bits of `roundCode`.
-/
@[kernel_optimize (cost := 1800)]
theorem quantizeFinite_eq_round (profile : Profile) (input : SignedRat) :
    quantizeFinite profile input = BitVec.ofNat profile.width (roundCode profile input) := by
  rw [quantizeFinite_eq_scan]
  unfold roundCode scanCode
  rw [scanAll_eq]
  cases htwos : twosComplement profile
  · rw [nearestAll_eq profile htwos,
      scan_eq_nearest profile htwos _ _ _ _ (Bool.toNat_le _) (Bool.toNat_le _)
        input.value.den_pos]
  · have hprofile : profile = .int8 := by
      cases profile <;> first | rfl | cases htwos
    subst hprofile
    have hcount : (2 : Nat) ^ Profile.int8.width = 256 := rfl
    rw [nearestAll_int8, hcount,
      scan_eq_int8Nearest _ _ _ _ (Bool.toNat_le _) (Bool.toNat_le _) input.value.den_pos]

attribute [kernel_optimize unfold] quantize quantizeWith


end FloatLib.Floats.Formats.OCP.MX.Standard.Element
