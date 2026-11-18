/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.PositForm

public import FloatLib.Floats.Formats.Posit.Configured.Plan.Dispatch
public import FloatLib.Floats.Formats.Posit.Configured.Instances
public import FloatLib.Floats.Formats.Posit.KernelPath.Model
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Form

/-!
# Posit operations for Lean's kernel

A public posit operation runs the kernel of its storage plan: byte tables or machine words, both
written for compiled code. Lean's kernel pays for the plan's selection and for every word
operation, which it evaluates through the definitions of the fixed-width integers.

The form that the kernel should evaluate is the direct dyadic arithmetic of
`Model.DirectDyadicArithmetic` on the decoded words: integer significands and binary exponents,
and one pass that writes the regime, exponent and fraction of the result. `Backend.dyadicAdd`
and its siblings lift it through the carrier. Each equals the configured reference operation,
for every posit format, storage plan and carrier, by `Backend.dyadicAdd_eq_spec` and its siblings.
Each is registered as its operation's `KernelPath.KernelForm`, so `float_decide` rewrites
`x + y` to `Backend.dyadicAdd x y`.

An instance applies to a capability whose reference operation unfolds to the configured one
(`Capability.HasSpec`): the capability of a built-in storage plan at a closed width, and the
capability of a custom codec.

The carrier rewrites below expose the model operation and cancel encoding followed by decoding
through the `ModelCodec` laws; they apply to every lawful posit carrier. The model operations
(addition, subtraction, multiplication, division, square root, FMA, negation, comparisons and
the change of width) are then rewritten by `Posit.KernelPath.Model` to the flat operations of
`Posit.KernelPath.Flat` on natural-number encodings, each proved equal to the Posit Standard
operation for every width, so Lean's kernel never builds a word in the middle of a
computation.

A literal rounds an exact rational with `Model.roundRat`, a search over codes with rational
comparisons. `ofRat_eq_kernel`, `ofScientific_eq_kernel` and `ofNat_eq_kernel` rewrite
`ExecFloat.Posit.ofRat` and the decimal and natural literals to the flat rounding of a ratio of
natural numbers on encodings (`KernelPath.Flat.ofRatio`): the numerator and denominator of the
rational, the mantissa and the power of ten of a decimal literal as they are written, and the
natural number over one.

Reference: Standard for Posit Arithmetic (2022), §§3.3, 4.1, 5.2–5.7 and 6.1.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Floats.ExecFloat

variable {format : Format} {plan : StoragePlan format} {code : Type}
  [ModelCodec plan (Model format) code]

attribute [kernel_optimize]
  Backend.dyadicAdd.eq_def
  Backend.dyadicSub.eq_def
  Backend.dyadicMul.eq_def
  Backend.dyadicDiv.eq_def
  Backend.dyadicSqrt.eq_def
  Backend.dyadicFma.eq_def
  ModelCodec.decode_liftUnary
  ModelCodec.decode_liftBinary
  ModelCodec.decode_liftTernary
  ExecFloat.Posit.toNatBits.eq_def
  ExecFloat.Posit.toModel.eq_def
  Family.toModel.eq_def
  ExecFloat.Posit.ofNatBits.eq_def
  ExecFloat.Posit.ofModel.eq_def
  Family.ofModel.eq_def
  ModelCodec.decode_encode

/-! ## Literals -/

/-- Rounding a rational into a posit is the flat rounding of the ratio of its numerator and its
denominator, for every posit format and carrier. -/
@[kernel_optimize] theorem ofRat_eq_kernel (value : Rat) :
    (ExecFloat.Posit.ofRat value : FloatLib.Floats.ExecFloat (Family format code plan)) =
      ExecFloat.Posit.ofModel (Model.ofNatBits
        (KernelPath.Flat.ofRatio format.payloadBits 2
          (Int.casesOn (motive := fun _ => Nat) value.num (fun _ => 0) (fun _ => 1))
          value.num.natAbs value.den)) := by
  unfold ExecFloat.Posit.ofRat
  have hsign : Int.casesOn (motive := fun _ => Nat) value.num (fun _ => 0) (fun _ => 1) =
      if decide (value.num < 0) then 1 else 0 := by
    cases value.num with
    | ofNat n => simp
    | negSucc n => simp [Int.negSucc_lt_zero]
  rw [hsign, ← KernelPath.roundRat_ratio_kernel format (decide (value.num < 0))
    value.num.natAbs value.den value.den_nz]
  congr 2
  have hnum : (if decide (value.num < 0) = true then -((value.num.natAbs : Nat) : Rat)
      else ((value.num.natAbs : Nat) : Rat)) = (value.num : Rat) := by
    by_cases h : value.num < 0
    · rw [decide_eq_true h, ite_eq_left rfl, Nat.cast_natAbs, abs_of_neg h]
      push_cast
      ring
    · rw [decide_eq_false h, ite_eq_right (by decide), Nat.cast_natAbs,
        abs_of_nonneg (not_lt.mp h)]
  rw [hnum, Rat.num_div_den]

/-- A decimal literal of a posit type is the flat rounding of its mantissa over or times the
power of ten, with no normalization of the ratio. -/
@[kernel_optimize] theorem ofScientific_eq_kernel (mantissa : Nat) (exponentSign : Bool)
    (exponent : Nat) :
    (OfScientific.ofScientific mantissa exponentSign exponent :
        FloatLib.Floats.ExecFloat (Family format code plan)) =
      ExecFloat.Posit.ofModel (Model.ofNatBits
        (Bool.casesOn (motive := fun _ => Nat) exponentSign
          (KernelPath.Flat.ofRatio format.payloadBits 2 0
            (Nat.mul mantissa (Nat.pow 10 exponent)) 1)
          (KernelPath.Flat.ofRatio format.payloadBits 2 0 mantissa (Nat.pow 10 exponent)))) := by
  change ExecFloat.Posit.ofRat (OfScientific.ofScientific mantissa exponentSign exponent : Rat) = _
  unfold ExecFloat.Posit.ofRat
  cases exponentSign
  · have h := KernelPath.roundRat_ratio_kernel format false (mantissa * 10 ^ exponent) 1
      Nat.one_ne_zero
    simp only [Bool.false_eq_true, ite_false] at h
    change ExecFloat.Posit.ofModel _ = ExecFloat.Posit.ofModel (Model.ofNatBits
      (KernelPath.Flat.ofRatio _ _ 0 (mantissa * 10 ^ exponent) 1))
    rw [← h]
    congr 2
    rw [show (OfScientific.ofScientific mantissa false exponent : Rat) =
      ((mantissa * 10 ^ exponent : Nat) : Rat) from Rat.ofScientific_false_def]
    simp
  · have h := KernelPath.roundRat_ratio_kernel format false mantissa (10 ^ exponent)
      (Nat.ne_of_gt (Nat.pow_pos (by decide)))
    simp only [Bool.false_eq_true, ite_false] at h
    change ExecFloat.Posit.ofModel _ = ExecFloat.Posit.ofModel (Model.ofNatBits
      (KernelPath.Flat.ofRatio _ _ 0 mantissa (10 ^ exponent)))
    rw [← h]
    congr 2
    rw [show (OfScientific.ofScientific mantissa true exponent : Rat) =
      mkRat mantissa (10 ^ exponent) from Rat.ofScientific_true_def, Rat.mkRat_eq_div]
    push_cast
    rfl

/-- A natural-number literal of a posit type is the flat rounding of its value. -/
@[kernel_optimize] theorem ofNat_eq_kernel (value : Nat) :
    (OfNat.ofNat value : FloatLib.Floats.ExecFloat (Family format code plan)) =
      ExecFloat.Posit.ofModel (Model.ofNatBits
        (KernelPath.Flat.ofRatio format.payloadBits 2 0 value 1)) := by
  change ExecFloat.Posit.ofRat (value : Rat) = _
  unfold ExecFloat.Posit.ofRat
  have h := KernelPath.roundRat_ratio_kernel format false value 1 Nat.one_ne_zero
  simp only [Bool.false_eq_true, ite_false] at h
  rw [← h]
  simp

variable [Backend.PolicyFor (Family format code plan)]

/-! ## The kernel forms -/

/-- Posit Standard (2022), §5.4: direct dyadic addition refines the exact specification. -/
posit_form .add := Backend.dyadicAdd for Spec.addition by Backend.dyadicAdd_eq_spec (x y)
/-- Posit Standard (2022), §5.4: direct dyadic subtraction refines the exact specification. -/
posit_form .sub := Backend.dyadicSub for Spec.subtraction by Backend.dyadicSub_eq_spec (x y)
/-- Posit Standard (2022), §5.4: direct dyadic multiplication refines the exact specification. -/
posit_form .mul := Backend.dyadicMul for Spec.multiplication by Backend.dyadicMul_eq_spec (x y)
/-- Posit Standard (2022), §5.4: direct quotient rounding refines the exact specification. -/
posit_form .div := Backend.dyadicDiv for Spec.division by Backend.dyadicDiv_eq_spec (x y)
/-- Posit Standard (2022), §5.5: direct root rounding refines the exact specification. -/
posit_form .sqrt := Backend.dyadicSqrt for Spec.sqrt by Backend.dyadicSqrt_eq_spec (x)
/-- FloatLib FMA extension with Posit Standard (2022), §4.1 rounding: exact refinement. -/
posit_form .fma := Backend.dyadicFma for Spec.fma by Backend.dyadicFma_eq_spec (x y z)

end FloatLib.Floats.Formats.Posit.Configured
