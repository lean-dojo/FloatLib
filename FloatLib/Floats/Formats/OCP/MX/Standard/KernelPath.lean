/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.ElementKernel
public import FloatLib.Floats.Formats.OCP.MX.Standard.Format
public import FloatLib.Kernels.Block.Maximum

/-!
# Kernel paths for stored MX values

OCP MX v1.0, §§5.3 and 6.3. The scalar bisection and its proof are in
`Standard.KernelPath.Nearest`. This module exposes that conversion inside a stored
block, proves the exact code-value equation, and exposes the recommended
maximum-binade scale selection. These equations apply to every profile,
block grouping and input; the scale remains computed by the generic block scan.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics

/-! ## The value of a code -/

/-- The rational value of a code: its signed magnitude over the denominator of the profile, and
zero for a code that is not finite. -/
def codeValue (profile : Profile) (code : Nat) : ℚ :=
  Bool.casesOn (motive := fun _ => ℚ) (finiteCode profile code) 0
    (mkRat
      (Bool.casesOn (motive := fun _ => Int) (Nat.beq (signBit profile code) 1)
        (Int.ofNat (magnitude profile code)) (Int.negOfNat (magnitude profile code)))
      (denominator profile))

/-- The values of all codes of a profile, as one check: the rational value of the decoded word
of each code is `codeValue`. -/
def valueCheck (profile : Profile) : Bool :=
  (List.range (2 ^ profile.width)).all fun code =>
    decide (Block.finiteValue (decode (BitVec.ofNat profile.width code : Element profile)) =
      codeValue profile code)

/-- Every profile passes the value check. -/
theorem valueCheck_eq (profile : Profile) : valueCheck profile = true := by
  cases profile <;> decide +kernel

/--
Dequantization on natural numbers, for every profile and every word: the rational value of an
element word is the value of its code.
-/
@[kernel_optimize (cost := 350)]
theorem finiteValue_decode_eq {profile : Profile} (word : Element profile) :
    Block.finiteValue (decode word) = codeValue profile word.toNat := by
  have hcheck := valueCheck_eq profile
  simp only [valueCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hcheck
  have h := hcheck word.toNat word.isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

end FloatLib.Floats.Formats.OCP.MX.Standard.Element

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics

/--
A stored element of a quantized tensor of `Standard.format` is the element conversion of its
input divided by the scale of its block, for every profile, grouping and scale-selection policy.
-/
@[kernel_optimize] theorem elements_quantize {ι γ : Type} (group : ι → γ) (profile : Profile)
    (overflow : OverflowMode) (selection : Block.Policy ι γ) (x : ι → SignedRat) (i : ι) :
    ((format group profile overflow).quantize selection x).elements i =
      Element.quantize profile
        (.finite (x i * SignedRat.ofRat
          (1 / ((format group profile overflow).toFormat selection).scale
            (fun j => (x j).value) i)))
        overflow :=
  rfl

/--
The rational value of a position of a quantized tensor of `Standard.format` is the value of its
element conversion times the scale of its block, with the scale written once.
-/
@[kernel_optimize (cost := 14000)] theorem value_quantize_element {ι γ : Type} (group : ι → γ)
    (profile : Profile) (overflow : OverflowMode) (selection : Block.Policy ι γ)
    (x : ι → SignedRat) (i : ι) :
    ((format group profile overflow).quantize selection x).value i =
      (fun scale =>
        Block.finiteValue
            (Element.decode
              (Element.quantize profile (.finite (x i * SignedRat.ofRat (1 / scale))) overflow)) *
          scale)
        (((format group profile overflow).toFormat selection).scale (fun j => (x j).value) i) := by
  change _ * ((format group profile overflow).quantize selection x).scale i = _
  rw [Block.CodedFormat.scale_quantize]
  rfl

/--
The scale of a position under the standard policy of §6.3 is the E8M0 rounding of the largest
magnitude of its block divided by the largest power of two of the element format, and of one
for an all-zero block. The rule exposes the largest magnitude, which `Block.amax_eq_loop`
computes on natural numbers for data indexed by `Fin n`.
-/
@[kernel_optimize] theorem scale_eq_amax {ι γ : Type} [Fintype ι] [DecidableEq γ]
    (group : ι → γ) (profile : Profile) (overflow : OverflowMode) (y : ι → ℚ) (i : ι) :
    ((format group profile overflow).toFormat (policy group profile)).scale y i =
      (fun largest =>
        E8M0.codec.rounding.round
          (if largest = 0 then 1 else largest / 2 ^ profile.maxPowerExponent))
        (Block.amax group y (group i)) := by
  rw [toFormat_format]
  change Block.total [Block.Level.ofMax group E8M0.codec.rounding
    (2 ^ profile.maxPowerExponent) 1] y i = _
  rw [Block.total_singleton]
  rfl

/--
The rational value of a position of a stored tensor of `Standard.format` is the value of its
element code times the scale of its block. `value_quantize_element` declares a cost, so it goes
first for a quantized tensor.
-/
@[kernel_optimize] theorem value_eq_codeValue {ι γ : Type} {group : ι → γ} {profile : Profile}
    {overflow : OverflowMode} (t : Block.Tensor (format group profile overflow)) (i : ι) :
    t.value i =
      Element.codeValue profile (BitVec.toNat (w := profile.width) (t.elements i)) *
        t.scale i := by
  change Block.finiteValue (Element.decode (t.elements i)) * t.scale i = _
  rw [Element.finiteValue_decode_eq]

end FloatLib.Floats.Formats.OCP.MX.Standard
