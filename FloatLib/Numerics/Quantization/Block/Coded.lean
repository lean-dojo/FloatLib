/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Block.Policy
public import FloatLib.Numerics.Exact.SignedRat

/-!
# Stored block-scaled tensors

`Block.Format` is the value theory. This module is its executable form over the rationals, with
stored codes:

* a `Codec` is an executable scalar format: its codes, the exact value of each code with its
  infinity or exceptional class, and the code it stores for an exact value. Its `rounding` is the
  `Rounding ℚ` the value theory uses;
* a `CodedFormat` is a storage format: one element codec and a list of `CodedLevel`s, outermost
  first, each with its groups and its scale codec. A `Policy` has one scale-selection rule per
  level, and `CodedFormat.toFormat` gives the format of the value theory for a storage format and
  a policy;
* a `Tensor F` stores one scale code per group of each level and one element code per position.

`CodedFormat.quantize` takes the policy, selects and encodes the scales level by level and encodes
each element at its exact scaled input. `Tensor.decode` is exact and keeps the class of every
position: a position that uses a scale with no finite value is NaN, and otherwise the result is
the closed product of the element and its total scale, so a finite element is multiplied by its
scales, an element NaN survives, and an element infinity survives with the sign of the product,
or is NaN under the scale zero. For the positive scales of OCP MX 1.0 this is the rule of its
section 5.1, for any number of levels.

## Main results

* `CodedFormat.value_quantize`: the rational values of a quantized tensor are the values
  `Format.reconstruct` computes for the format without codes. So every theorem of the value theory
  (one rounding per element, error budgets, flush to zero, transposition, dot products) holds for
  the stored codes.
* `Tensor.value_of_decode`: a position that decodes to a finite value decodes to its rational value.
* `Tensor.decode_of_not_isFinite`, `Tensor.decode_finite`, `Tensor.decode_infinity`,
  `Tensor.decode_infinity_of_pos`, `Tensor.decode_exceptional`: the cases of exact decoding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics

/-- Rational value of a decoded observation: the finite value, and zero for an infinity or an
exceptional value. -/
def finiteValue : NumericalValue SignedRat → ℚ
  | .finite v => v.value
  | .infinity _ => 0
  | .exceptional _ => 0

/--
An executable scalar format over the rationals: stored codes, the exact value of each code, and
the code stored for an exact value, which applies the format's rounding and its saturation or
overflow policy. The stored value may depend on the sign of a zero input only through the sign of
the stored zero.
-/
structure Codec where
  /-- Stored codes. -/
  Code : Type
  /-- Exact value of a code, with its infinity or exceptional class. -/
  decode : Code → NumericalValue SignedRat
  /-- Code stored for an exact value. -/
  encode : SignedRat → Code
  /-- The stored value depends on the rational value of the input, not on the sign of a zero. -/
  value_encode : ∀ s : SignedRat,
    finiteValue (decode (encode s)) = finiteValue (decode (encode (SignedRat.ofRat s.value)))

namespace Codec

/-- Rational value of a code, and zero for a code with no finite value. -/
def value (C : Codec) (c : C.Code) : ℚ :=
  finiteValue (C.decode c)

/-- The rounding map of a codec: the rational value of the code stored for a rational. -/
def rounding (C : Codec) : Rounding ℚ where
  round q := C.value (C.encode (SignedRat.ofRat q))

/-- The value of an encoded input is the codec's rounding of its rational value. -/
theorem value_encode_eq (C : Codec) (s : SignedRat) :
    C.value (C.encode s) = C.rounding.round s.value :=
  C.value_encode s

/-- A code with a finite exact value has that value. -/
theorem value_of_decode (C : Codec) {c : C.Code} {v : SignedRat} (h : C.decode c = .finite v) :
    C.value c = v.value := by
  simp [value, finiteValue, h]

end Codec

variable {ι γ : Type}

/-- A scale level with stored codes: the group of each element and the codec of the level's
scales. -/
structure CodedLevel (ι γ : Type) where
  /-- The group whose scale an element uses. -/
  group : ι → γ
  /-- Codec of the level's scales. -/
  codec : Codec

/-- Scale selection of one level: the unrounded scale of each group, from the data already
divided by the scales of the levels above. -/
abbrev Selection (ι γ : Type) :=
  (ι → ℚ) → γ → ℚ

/-- A scale-selection policy: one selection rule per level, outermost first. A level without a
rule gets the ideal scale `1`. -/
abbrev Policy (ι γ : Type) :=
  List (Selection ι γ)

/-- The level of the value theory for a coded level and its selection rule. -/
def CodedLevel.toLevel (L : CodedLevel ι γ) (ideal : Selection ι γ) : Level ι γ ℚ where
  group := L.group
  format := L.codec.rounding
  ideal := ideal

namespace Selection

/-- A scale the caller chose for each group. The data is not read. -/
def supplied (s : γ → ℚ) : Selection ι γ :=
  fun _ g => s g

/-- Post-process the ideal scales of a rule, for example round them up to a power of two or keep
them above a floor. -/
def map (f : ℚ → ℚ) (rule : Selection ι γ) : Selection ι γ :=
  fun y g => f (rule y g)

variable [Fintype ι] [DecidableEq γ]

/-- Scale each group so that its largest magnitude maps to `target`, with the ideal scale `zero`
for an all-zero group: the rule of `Level.ofMax`. -/
def ofMax (group : ι → γ) (target zero : ℚ) : Selection ι γ :=
  fun y g => if amax group y g = 0 then zero else amax group y g / target

/-- Keep, for each group, the first of the candidate targets with the least measured error of the
elements rounded by `element` at the scale `codec` stores: the rule of `Level.ofCandidates`. -/
def ofCandidates (group : ι → γ) (codec element : Codec) (measure : ℚ → ℚ) (targets : List ℚ)
    (zero : ℚ) : Selection ι γ :=
  (Level.ofCandidates group codec.rounding (fun _ => element.rounding) measure targets zero).ideal

end Selection

/-- A coded level with the largest-magnitude rule is `Level.ofMax` of the value theory. -/
@[simp] theorem CodedLevel.toLevel_ofMax [Fintype ι] [DecidableEq γ] (L : CodedLevel ι γ)
    (target zero : ℚ) :
    L.toLevel (Selection.ofMax L.group target zero) =
      Level.ofMax L.group L.codec.rounding target zero :=
  rfl

/-- A coded level with a supplied scale is `Level.supplied` of the value theory. -/
@[simp] theorem CodedLevel.toLevel_supplied (L : CodedLevel ι γ) (s : γ → ℚ) :
    L.toLevel (Selection.supplied s) = Level.supplied L.group L.codec.rounding s :=
  rfl

/--
A block-scaled storage format: one element codec and the scale levels, outermost first. The
scale-selection policy is not part of the storage format: `CodedFormat.quantize` takes it, and two
tensors quantized with different policies have the same type.
-/
structure CodedFormat (ι γ : Type) where
  /-- Codec of the elements. -/
  element : Codec
  /-- Scale levels, outermost first. -/
  levels : List (CodedLevel ι γ)

/-- The levels of the value theory for coded levels and a policy. -/
def levelsWith : List (CodedLevel ι γ) → Policy ι γ → List (Level ι γ ℚ)
  | [], _ => []
  | L :: Ls, policy => L.toLevel (policy.headD fun _ _ => 1) :: levelsWith Ls policy.tail

/-- The format of the value theory for a storage format and a policy. -/
def CodedFormat.toFormat (F : CodedFormat ι γ) (policy : Policy ι γ) : Format ι γ ℚ where
  element _ := F.element.rounding
  levels := levelsWith F.levels policy

/-- Stored scale codes of a list of levels: for each level, one code per group. -/
def ScaleCodes : List (CodedLevel ι γ) → Type
  | [] => Unit
  | L :: Ls => (γ → L.codec.Code) × ScaleCodes Ls

namespace ScaleCodes

/-- Product of the rational values of the scales an element uses. -/
def total : (levels : List (CodedLevel ι γ)) → ScaleCodes levels → ι → ℚ
  | [], _, _ => 1
  | L :: Ls, (codes, rest), i => L.codec.value (codes (L.group i)) * total Ls rest i

/-- Whether every scale an element uses has a finite exact value. -/
def isFinite : (levels : List (CodedLevel ι γ)) → ScaleCodes levels → ι → Bool
  | [], _, _ => true
  | L :: Ls, (codes, rest), i =>
      (L.codec.decode (codes (L.group i))).isFinite && isFinite Ls rest i

end ScaleCodes

/-- Scale codes selected for the data `x`, outermost level first: each level encodes the ideal
scale its rule selects, and the next level sees the data divided by the stored scale. -/
def encodeScales : (levels : List (CodedLevel ι γ)) → Policy ι γ → (ι → ℚ) → ScaleCodes levels
  | [], _, _ => ()
  | L :: Ls, policy, x =>
      (fun g => L.codec.encode (SignedRat.ofRat ((policy.headD fun _ _ => 1) x g)),
        encodeScales Ls policy.tail fun i =>
          x i / (L.toLevel (policy.headD fun _ _ => 1)).scaleAt x i)

/-- The stored scales multiply to the total scale of the value theory. -/
theorem total_encodeScales (levels : List (CodedLevel ι γ)) (policy : Policy ι γ) (x : ι → ℚ)
    (i : ι) :
    ScaleCodes.total levels (encodeScales levels policy x) i =
      total (levelsWith levels policy) x i := by
  induction levels generalizing policy x with
  | nil => rfl
  | cons L Ls ih =>
    simp only [encodeScales, ScaleCodes.total, levelsWith, Block.total, ih]
    rfl

/-- A stored block-scaled tensor: the scale codes of every level and one element code per
position. -/
structure Tensor (F : CodedFormat ι γ) where
  /-- Scale codes, outermost level first. -/
  scales : ScaleCodes F.levels
  /-- Element codes. -/
  elements : ι → F.element.Code

namespace Tensor

variable {F : CodedFormat ι γ}

/-- Total scale of a position: the product of the values of the scales it uses. -/
def scale (t : Tensor F) (i : ι) : ℚ :=
  ScaleCodes.total F.levels t.scales i

/-- Rational value of a position: element times scales, and zero when the element or a scale has
no finite value. -/
def value (t : Tensor F) (i : ι) : ℚ :=
  F.element.value (t.elements i) * t.scale i

/--
Exact decoding of a position: the closed product of the element and its total scale when every
scale is finite. A finite element is multiplied by its scales without rounding. An element
infinity keeps its sign under a positive scale, changes it under a negative scale, and is NaN
under the scale zero. An exceptional element is kept. A scale with no finite value makes the
position NaN.
-/
def decode (t : Tensor F) (i : ι) : NumericalValue SignedRat :=
  if ScaleCodes.isFinite F.levels t.scales i then
    match F.element.decode (t.elements i) with
    | .finite v => .finite (v * SignedRat.ofRat (t.scale i))
    | .infinity negative =>
        if t.scale i = 0 then .exceptional .nan
        else .infinity (negative != decide (t.scale i < 0))
    | .exceptional e => .exceptional e
  else .exceptional .nan

/-- A position that uses a scale with no finite value decodes to NaN, whatever its element. -/
theorem decode_of_not_isFinite (t : Tensor F) (i : ι)
    (h : ScaleCodes.isFinite F.levels t.scales i = false) :
    t.decode i = .exceptional .nan := by
  simp [decode, h]

/-- A finite element under finite scales decodes to the exact product. -/
theorem decode_finite (t : Tensor F) (i : ι) {v : SignedRat}
    (h : ScaleCodes.isFinite F.levels t.scales i = true)
    (hv : F.element.decode (t.elements i) = .finite v) :
    t.decode i = .finite (v * SignedRat.ofRat (t.scale i)) := by
  simp [decode, h, hv]

/-- An element infinity under finite scales: NaN under the scale zero, and otherwise an infinity
whose sign is changed by a negative scale. -/
theorem decode_infinity (t : Tensor F) (i : ι) {negative : Bool}
    (h : ScaleCodes.isFinite F.levels t.scales i = true)
    (hv : F.element.decode (t.elements i) = .infinity negative) :
    t.decode i =
      if t.scale i = 0 then .exceptional .nan
      else .infinity (negative != decide (t.scale i < 0)) := by
  simp [decode, h, hv]

/-- A positive finite total scale keeps an element infinity and its sign. -/
theorem decode_infinity_of_pos (t : Tensor F) (i : ι) {negative : Bool}
    (h : ScaleCodes.isFinite F.levels t.scales i = true)
    (hv : F.element.decode (t.elements i) = .infinity negative) (hσ : 0 < t.scale i) :
    t.decode i = .infinity negative := by
  rw [decode_infinity t i h hv]
  simp [hσ.ne', not_lt.mpr hσ.le]

/-- Finite scales keep an exceptional element without changing the other positions. -/
theorem decode_exceptional (t : Tensor F) (i : ι) {e : ExceptionalValue}
    (h : ScaleCodes.isFinite F.levels t.scales i = true)
    (hv : F.element.decode (t.elements i) = .exceptional e) :
    t.decode i = .exceptional e := by
  simp [decode, h, hv]

/-- A position that decodes to a finite value decodes to its rational value. -/
theorem value_of_decode (t : Tensor F) (i : ι) {v : SignedRat} (h : t.decode i = .finite v) :
    v.value = t.value i := by
  unfold decode at h
  split at h
  · cases hd : F.element.decode (t.elements i) with
    | finite e =>
      rw [hd] at h
      simp only [NumericalValue.finite.injEq] at h
      rw [← h, value, F.element.value_of_decode hd]
      simp
    | infinity s =>
      rw [hd] at h
      dsimp only at h
      split at h <;> simp at h
    | exceptional e => simp [hd] at h
  · simp at h

/-- A finite decoded position has the rational payload `value`, including signed zeros. -/
theorem map_decode_of_isFinite (t : Tensor F) (i : ι)
    (h : (t.decode i).isFinite = true) :
    (t.decode i).map SignedRat.value = .finite (t.value i) := by
  cases hd : t.decode i with
  | finite v => simp [value_of_decode t i hd]
  | infinity s => simp [hd] at h
  | exceptional e => simp [hd] at h

end Tensor

namespace CodedFormat

/--
Quantize with a scale-selection policy: select and encode the scales, then encode each element at
its exact scaled input. A zero input keeps its sign.
-/
def quantize (F : CodedFormat ι γ) (policy : Policy ι γ) (x : ι → SignedRat) : Tensor F where
  scales := encodeScales F.levels policy fun i => (x i).value
  elements i :=
    F.element.encode
      (x i * SignedRat.ofRat (1 / (F.toFormat policy).scale (fun j => (x j).value) i))

/-- The total scale of a quantized tensor is the total scale the value theory selects. -/
theorem scale_quantize (F : CodedFormat ι γ) (policy : Policy ι γ) (x : ι → SignedRat) (i : ι) :
    (F.quantize policy x).scale i = (F.toFormat policy).scale (fun j => (x j).value) i :=
  total_encodeScales F.levels policy _ i

/--
The rational values of a quantized tensor are the values the format without codes reconstructs.
So the theorems of the value theory hold for the stored codes of every codec, level structure and
policy.
-/
theorem value_quantize (F : CodedFormat ι γ) (policy : Policy ι γ) (x : ι → SignedRat) (i : ι) :
    (F.quantize policy x).value i =
      (F.toFormat policy).reconstruct (fun j => (x j).value) i := by
  rw [Tensor.value, scale_quantize]
  simp only [quantize, Codec.value_encode_eq, SignedRat.value_mul, SignedRat.value_ofRat,
    mul_one_div, Format.reconstruct, Format.decode, Format.quantize, Format.normalized_eq]
  rfl

/-- Each stored element code is the element codec's encoding of the exact scaled input. -/
theorem elements_quantize (F : CodedFormat ι γ) (policy : Policy ι γ) (x : ι → SignedRat)
    (i : ι) :
    (F.quantize policy x).elements i =
      F.element.encode
        (x i * SignedRat.ofRat (1 / (F.toFormat policy).scale (fun j => (x j).value) i)) :=
  rfl

end CodedFormat

end FloatLib.Floats.Formats.Block
