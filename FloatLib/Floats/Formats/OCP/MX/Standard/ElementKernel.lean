/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing
public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath.Nearest
public import FloatLib.Tactic.KernelShape
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
`nearest` as one flat term per sign-magnitude profile, and `int8Nearest` as one flat term for
INT8, each with the constants of its profile computed: the form that Lean's kernel evaluates
(`nearestAll_eq`, `nearestAll_int8`). Each profile is a function of the input, so the kernel
copies the term of the one profile that it evaluates.
-/
noncomputable def nearestAll (profile : Profile) (sp neg ap q : Nat) : Nat :=
  Profile.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun sp neg ap q => nearest_flat% .e5m2 sp neg ap q)
    (fun sp neg ap q => nearest_flat% .e4m3 sp neg ap q)
    (fun sp neg ap q => nearest_flat% .e3m2 sp neg ap q)
    (fun sp neg ap q => nearest_flat% .e2m3 sp neg ap q)
    (fun sp neg ap q => nearest_flat% .e2m1 sp neg ap q)
    (fun sp neg ap q => int8_nearest_flat% sp neg ap q)
    profile sp neg ap q

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
`nearestAll` with a guess of the field that the bisection finds: the flat forms of
`nearestGuessed` and `int8NearestGuessed` with `nearestAll` as the alternative. The quotient of
the input gives the field in a few operations, two tests confirm it, and the bisection runs
only when a test fails (`nearestFast_eq`).
-/
noncomputable def nearestFast (profile : Profile) (sp neg ap q : Nat) : Nat :=
  Profile.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat)
    (fun sp neg ap q => nearest_guess_flat% .e5m2 sp neg ap q (nearestAll .e5m2 sp neg ap q))
    (fun sp neg ap q => nearest_guess_flat% .e4m3 sp neg ap q (nearestAll .e4m3 sp neg ap q))
    (fun sp neg ap q => nearest_guess_flat% .e3m2 sp neg ap q (nearestAll .e3m2 sp neg ap q))
    (fun sp neg ap q => nearest_guess_flat% .e2m3 sp neg ap q (nearestAll .e2m3 sp neg ap q))
    (fun sp neg ap q => nearest_guess_flat% .e2m1 sp neg ap q (nearestAll .e2m1 sp neg ap q))
    (fun sp neg ap q => int8_nearest_guess_flat% sp neg ap q (nearestAll .int8 sp neg ap q))
    profile sp neg ap q

/-- The guessed flat form is `nearestAll`, for every profile and every input. -/
@[kernel_optimize ← (cost := 300)]
theorem nearestFast_eq (profile : Profile) (sp neg ap q : Nat) :
    nearestFast profile sp neg ap q = nearestAll profile sp neg ap q := by
  cases profile
  case int8 =>
    refine (kernel_refl% : nearestFast .int8 sp neg ap q =
      int8NearestGuessed sp neg ap q (nearestAll .int8 sp neg ap q)).trans ?_
    rw [nearestAll_int8]
    exact int8NearestGuessed_eq sp neg ap q
  all_goals
    rw [nearestAll_eq _ rfl, ← nearestGuessed_eq _ rfl sp neg ap q, ← nearestAll_eq _ rfl]
    exact kernel_refl%

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

/-!
The kernel shape of `roundCode` reads the two sign bits with the recursor of `Bool` and the
numerator with the kernel arithmetic of `Int`.
-/
kernel_shape roundCode inlining [Bool.toNat]

attribute [kernel_optimize unfold] quantize quantizeWith

/-- The saturating mode is not the native mode: the decision that `quantize` unfolds to. -/
@[kernel_optimize (cost := 1)]
theorem decide_saturate_eq_native :
    decide (OverflowMode.saturate = OverflowMode.native) = false :=
  rfl

/-- The native mode is the native mode: the decision that `quantize` unfolds to. -/
@[kernel_optimize (cost := 1)]
theorem decide_native_eq_native :
    decide (OverflowMode.native = OverflowMode.native) = true :=
  rfl


end FloatLib.Floats.Formats.OCP.MX.Standard.Element
