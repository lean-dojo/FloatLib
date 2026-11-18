/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.ReferencePaths

public import FloatLib.Numerics.Executable.Packed
public import FloatLib.Numerics.Executable.Conversion.Finite
public import FloatLib.Floats.Formats.Block.Codecs
public import FloatLib.Numerics.Capabilities.BlockScaled

/-!
# Block-scaled tensors on the common carrier

`ExecFloat.Block F` is the stored tensor of any coded block format `F` on the common executable
carrier: OCP MX blocks, NVFP4 tensors, the unbounded shared-scale block. Its scalar domain is the
vector of signed rationals of its positions, and a tensor with a position that is not finite has no
value there and is summarized as NaN. `ExecFloat.Block.decode` keeps every position.
The richer `HasExactSemantics` observation retains all stored element and scale codes.

Conversion into a block format quantizes a finite vector with `CodedFormat.quantize`. Its context
is the scale-selection policy, and there is no default policy. A source that is not finite is
rejected.

`sharedScale ι` is the block whose elements are unbounded integers and whose one scale is a power
of two, and `sharedExponent ι exponent` is the policy that stores the exponent the caller supplies.

## Main results

* `ExecFloat.Block.value_quantize`: the values of a quantized tensor are those of the value theory.
* `ExecFloat.Block.Conversion.implements_run`: conversion meets its specification: the stored
  values are those `Format.reconstruct` computes, and each element code is the element codec's
  encoding of the exact scaled input.
* `blockScaled_tensor`: every position of a finite tensor is its stored element times its total
  scale, the generic `BlockScaled` capability.
* `sharedScale_scale`, `sharedScale_elements`, `sharedScale_value`: the shared-scale block stores
  the supplied exponent and the nearest-even integer of each scaled input.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace Formats.Block

variable {ι γ : Type}

/-- Type-level identity of the stored tensors of a coded block format. -/
inductive Family (F : CodedFormat ι γ) where
  /-- The only value: the family names a format in types and carries no data. -/
  | format

/--
Whole-tensor observation: the vector of position values when every position is finite, and NaN
otherwise. `Tensor.decode` keeps the class of each position.
-/
def Tensor.decodeAll [Fintype ι] {F : CodedFormat ι γ} (t : Tensor F) :
    NumericalValue (ι → SignedRat) :=
  if ∀ i, (t.decode i).isFinite = true then .finite fun i => ((t.decode i).finite?).getD 0
  else .exceptional .nan

/-- A whole tensor has a finite observation exactly when every position has its stated value. -/
theorem Tensor.decodeAll_eq_finite_iff [Fintype ι] {F : CodedFormat ι γ}
    (t : Tensor F) (x : ι → SignedRat) :
    t.decodeAll = .finite x ↔ ∀ i, t.decode i = .finite (x i) := by
  unfold decodeAll
  split
  · rename_i hall
    constructor
    · intro h i
      have hx := congrFun (NumericalValue.finite.inj h) i
      have hi := hall i
      cases hd : t.decode i <;> simp_all
    · intro h
      congr 1
      funext i
      simp [h i]
  · rename_i hnot
    constructor
    · intro h
      cases h
    · intro h
      exact (hnot fun i => by simp [h i]).elim

instance (F : CodedFormat ι γ) : EncodedFormat (Family F) where
  Code := Tensor F
  Scalar := ι → SignedRat

instance [Fintype ι] (F : CodedFormat ι γ) : FormatSemantics (Family F) where
  denote := Tensor.decodeAll

/-- Rich block observations retain the entire stored tensor, including every scale code. -/
instance [Fintype ι] (F : CodedFormat ι γ) : HasExactSemantics (Family F) where
  exactSemantics := ExactSemantics.ofRepresentation (formatSystem (Family F))

/--
Every position of a finite tensor is its stored element times its total scale: the generic
block-scaled capability, with the total scale field as the shared scale.
-/
theorem blockScaled_tensor [Fintype ι] (F : CodedFormat ι γ) :
    BlockScaled (formatSystem (Family F)) ι (ι → ℚ) (ι × NumericalValue SignedRat) SignedRat
      (fun (block : ι → SignedRat) (i : ι) => block i)
      (fun (t : Tensor F) => t.scale)
      (fun (t : Tensor F) (i : ι) => (i, F.element.decode (t.elements i)))
      (fun (σ : ι → ℚ) (stored : ι × NumericalValue SignedRat) =>
        ((stored.2.map fun v => v * SignedRat.ofRat (σ stored.1)).finite?).getD 0) := by
  intro t block ht i
  change Tensor.decodeAll t = .finite block at ht
  have hi := (Tensor.decodeAll_eq_finite_iff t block).mp ht i
  unfold Tensor.decode at hi
  split at hi
  · cases hd : F.element.decode (t.elements i) with
    | finite v =>
      simp only [hd, NumericalValue.finite.injEq] at hi
      simpa only [hd, NumericalValue.map_finite, NumericalValue.finite?_finite,
        Option.getD_some] using hi.symm
    | infinity negative =>
      simp only [hd] at hi
      split at hi <;> cases hi
    | exceptional e => simp [hd] at hi
  · cases hi

/-- Integer significands with one power-of-two scale for all positions: the unbounded
shared-scale block. No element saturates, and the caller supplies the scale. -/
@[reducible] def sharedScale (ι : Type) : CodedFormat ι Unit where
  element := Codec.int
  levels := [{ group := fun _ => (), codec := Codec.exponent }]

/-- The policy that stores the binary exponent the caller supplies. -/
def sharedExponent (ι : Type) (exponent : Int) : Policy ι Unit :=
  [Selection.supplied fun _ => (2 : ℚ) ^ exponent]

/-- The shared-scale block stores the exponent the caller supplied. -/
theorem sharedScale_code (exponent : Int) (x : ι → SignedRat) :
    ((sharedScale ι).quantize (sharedExponent ι exponent) x).scales.1 () = exponent := by
  change Int.log 2 (SignedRat.ofRat ((2 : ℚ) ^ exponent)).value = exponent
  simpa using Int.log_zpow (R := ℚ) (b := 2) (by norm_num) exponent

/-- The total scale of the shared-scale block is the supplied power of two. -/
theorem sharedScale_scale (exponent : Int) (x : ι → SignedRat) (i : ι) :
    ((sharedScale ι).quantize (sharedExponent ι exponent) x).scale i = (2 : ℚ) ^ exponent := by
  change Codec.exponent.value
    (((sharedScale ι).quantize (sharedExponent ι exponent) x).scales.1 ()) * 1 = _
  rw [sharedScale_code]
  simp [Codec.value, finiteValue]

/-- Each stored significand is the nearest integer, ties to even, of the input divided by the
shared scale. -/
theorem sharedScale_elements (exponent : Int) (x : ι → SignedRat) (i : ι) :
    ((sharedScale ι).quantize (sharedExponent ι exponent) x).elements i =
      roundRatEven ((x i).value / (2 : ℚ) ^ exponent) := by
  have hscale : ((sharedScale ι).toFormat (sharedExponent ι exponent)).scale
      (fun j => (x j).value) i = (2 : ℚ) ^ exponent := by
    rw [← CodedFormat.scale_quantize, sharedScale_scale]
  change roundRatEven (x i * SignedRat.ofRat
    (1 / ((sharedScale ι).toFormat (sharedExponent ι exponent)).scale
      (fun j => (x j).value) i)).value = _
  rw [hscale, SignedRat.value_mul, SignedRat.value_ofRat, mul_one_div]

/-- Each decoded position of a quantized shared-scale block is the nearest-even integer multiple
of the shared scale. -/
theorem sharedScale_value (exponent : Int) (x : ι → SignedRat) (i : ι) :
    ((sharedScale ι).quantize (sharedExponent ι exponent) x).value i =
      (roundRatEven ((x i).value / (2 : ℚ) ^ exponent) : ℚ) * (2 : ℚ) ^ exponent := by
  rw [Tensor.value, sharedScale_scale, sharedScale_elements]
  simp [Codec.value, finiteValue]

end Formats.Block

namespace ExecFloat

open Formats.Block

variable {ι γ : Type}

/-- The stored tensor of a coded block format on the common executable carrier. -/
abbrev Block (F : CodedFormat ι γ) :=
  FloatLib.Floats.ExecFloat (Family F)

namespace Block

variable {F : CodedFormat ι γ}

/-- Wrap a stored tensor without conversion. -/
@[inline] def ofCode (t : Tensor F) : ExecFloat.Block F :=
  ExecFloat.ofRaw t

/-- Recover the stored tensor without conversion. -/
@[inline] def toCode (value : ExecFloat.Block F) : Tensor F :=
  value.raw

/-- Exact value of one position, with its infinity or exceptional class. -/
@[inline] def decode (value : ExecFloat.Block F) (i : ι) : NumericalValue SignedRat :=
  value.toCode.decode i

/-- Rational value of one position. -/
@[inline] def value (value : ExecFloat.Block F) (i : ι) : ℚ :=
  value.toCode.value i

/-- Quantize a finite vector with a scale-selection policy and the format's element conversion. -/
@[inline] def quantize (F : CodedFormat ι γ) (policy : Policy ι γ) (x : ι → SignedRat) :
    ExecFloat.Block F :=
  ofCode (F.quantize policy x)

/-- Unwrapping a freshly wrapped tensor returns the original tensor. -/
@[simp, grind =] theorem toCode_ofCode (t : Tensor F) : toCode (ofCode t) = t :=
  rfl

/-- Rewrapping the tensor of a value returns the original value. -/
@[simp, grind =] theorem ofCode_toCode (value : ExecFloat.Block F) :
    ofCode value.toCode = value :=
  ExecFloat.ofRaw_raw value

/-- The rational values of a quantized tensor are those the format without codes reconstructs. -/
theorem value_quantize (F : CodedFormat ι γ) (policy : Policy ι γ) (x : ι → SignedRat)
    (i : ι) :
    (quantize F policy x).value i =
      (F.toFormat policy).reconstruct (fun j => (x j).value) i :=
  F.value_quantize policy x i

/-- Stored values follow the value theory and each element code encodes its exact scaled input. -/
def Quantizes (F : CodedFormat ι γ) (policy : Policy ι γ) (x : ι → SignedRat)
    (rounded : ExecFloat.Block F) : Prop :=
  (∀ i, rounded.value i = (F.toFormat policy).reconstruct (fun j => (x j).value) i) ∧
    ∀ i, rounded.toCode.elements i = F.element.encode
      (x i * SignedRat.ofRat (1 / (F.toFormat policy).scale (fun j => (x j).value) i))

/-- Quantizing a coded tensor meets both its reconstruction and stored-element contracts. -/
theorem quantizes_quantize (F : CodedFormat ι γ) (policy : Policy ι γ) (x : ι → SignedRat) :
    Quantizes F policy x (quantize F policy x) :=
  ⟨fun i => value_quantize F policy x i, fun _ => rfl⟩

namespace Conversion

variable [Fintype ι]

/-- Conversion flags: `inexact` when some position does not decode to its input, and `underflow`
when a nonzero input is stored as zero. -/
def status (x : ι → SignedRat) (rounded : ExecFloat.Block F) : ConversionStatus where
  inexact := decide (∃ i, rounded.decode i ≠ .finite (x i))
  underflow := decide (∃ i, (x i).value ≠ 0 ∧ rounded.value i = 0)

/-- Quantize a finite vector with the policy of the context, and reject a source that is not
finite. -/
def run (F : CodedFormat ι γ) (policy : Policy ι γ) :
    NumericalValue (ι → SignedRat) → ConversionOutcome (ExecFloat.Block F) :=
  ExecFloat.Conversion.runFinite (quantize F policy) status .reject

/--
Conversion contract. A finite vector is stored as a tensor whose values are those the format
without codes reconstructs under the policy and whose element codes are the element codec's
encodings of the exact scaled inputs. The flags are specified as `status`, the function `run` uses.
-/
def Spec (F : CodedFormat ι γ) (policy : Policy ι γ) (input : NumericalValue (ι → SignedRat))
    (outcome : ConversionOutcome (ExecFloat.Block F)) : Prop :=
  ExecFloat.Conversion.FiniteSpec (Quantizes F policy) status .reject input outcome

/-- Conversion into a block format meets its contract. -/
theorem implements_run (F : CodedFormat ι γ) :
    Quantization.Spec.Implements (Spec F) (run F) := by
  intro policy input
  exact ExecFloat.Conversion.implements_runFinite (quantize F policy) (Quantizes F policy)
    (quantizes_quantize F policy) status .reject input

/--
Block formats quantize finite vectors, and the conversion context is the scale-selection policy.
There is no `DefaultQuantizer`: a default would hide a scale selection.
-/
instance quantizer : Quantizer (ExecFloat.Block F) (ι → SignedRat) where
  Context := Policy ι γ
  run := run F
  spec := Spec F
  correct := implements_run F

/-- A stored tensor decodes to its vector of position values, or NaN when a position is not
finite. -/
instance exactDecoder : ExactDecoder (ExecFloat.Block F) (ι → SignedRat) where
  decode value := value.toCode.decodeAll

end Conversion

/-- A stored tensor over `Fin n` has one exact lane per position, in increasing order, with no
value at a position that is not finite. -/
instance {n : Nat} {F : CodedFormat (Fin n) γ} : ExactLanes (ExecFloat.Block F) where
  lanes block := (List.finRange n).map fun i => ((block.decode i).finite?).map SignedRat.value

end Block

end ExecFloat

end FloatLib.Floats

/-!
# Common execution paths for stored block tensors

The reference certificates and kernel unfolding rules apply to every codec, scale-level list,
grouping map and selection policy. `CodedFormat.value_quantize` relates this executable
quantization to the rational value theory. No new arithmetic implementation is introduced.

OCP MX v1.0, §§5.1 and 6.3, and NVIDIA, *Pretraining Large Language Models with NVFP4*,
arXiv:2509.25149v2, Appendix B.1–B.3, describe instances. NVIDIA's description is not a standard.
These paths use exact rational scale arithmetic; finite working-precision scale selection
is a different contract.
-/

namespace FloatLib.Floats.Formats.Block

reference_paths CodedFormat.quantize Tensor.decode

end FloatLib.Floats.Formats.Block
