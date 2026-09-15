/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith

/-!
# Numerical contracts for OCP MX element rounding

The bounded candidate search implements a mathematical nearest-even specification over all
finite element encodings. The proofs do not assume uniform spacing, and therefore cover
subnormals, binade boundaries, finite saturation, and the asymmetric two's-complement endpoint.
-/

public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

/-- Candidate enumeration contains exactly the finite words with their decoded rational values. -/
@[simp] theorem mem_candidates {profile : Profile} {word : Element profile} {value : Rat} :
    (word, value) ∈ candidates profile ↔ toRat? word = some value := by
  simp only [candidates, List.mem_filterMap, List.mem_ofFn]
  constructor
  · rintro ⟨other, _, h⟩
    cases hdecode : toRat? other with
    | none => simp [hdecode] at h
    | some otherValue =>
      simp only [hdecode, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact hdecode
  · intro h
    exact ⟨word, ⟨word.toFin, rfl⟩, by simp [h]⟩

private theorem toRat?_decodeFloat_zero (fmt : FloatFormat) :
    ((decodeFloat (Model.zero fmt false)).finite?).map SignedRat.value = some 0 := by
  simp [decodeFloat, Model.toDyadic?_zero]

/-- Every concrete profile contains positive zero. -/
@[simp] theorem toRat?_zero (profile : Profile) :
    toRat? (0#profile.width) = some 0 := by
  cases profile <;> simp only [toRat?, decode]
  · simpa [Model.zero, Model.posZero] using toRat?_decodeFloat_zero .e5m2
  · simpa [Model.zero, Model.posZero] using toRat?_decodeFloat_zero .e4m3fn
  · simpa [Model.zero, Model.posZero] using toRat?_decodeFloat_zero .e3m2
  · simpa [Model.zero, Model.posZero] using toRat?_decodeFloat_zero .e2m3
  · simpa [Model.zero, Model.posZero] using toRat?_decodeFloat_zero .e2m1
  · simp [BitVec.toInt_zero]

/-- INT8 is the two's-complement integer divided by 64, rather than a sign-magnitude encoding. -/
theorem toRat?_int8 (word : Element .int8) :
    toRat? word = some ((word.toInt : Rat) / 64) := by
  simp [toRat?, decode]

/-- The chosen INT8 profile uses the complete permitted asymmetric range. -/
theorem int8_bounds (word : Element .int8) :
    (-2 : Rat) ≤ (word.toInt : Rat) / 64 ∧ (word.toInt : Rat) / 64 ≤ 127 / 64 := by
  have hlo : (-128 : Int) ≤ word.toInt := BitVec.le_toInt word
  have hhi : word.toInt ≤ (127 : Int) := BitVec.toInt_le
  have hlo' : (-128 : Rat) ≤ word.toInt := by exact_mod_cast hlo
  have hhi' : (word.toInt : Rat) ≤ 127 := by exact_mod_cast hhi
  constructor <;> linarith

/-- There is always a finite candidate, so the executable fallback is unreachable. -/
theorem candidates_ne_nil (profile : Profile) : candidates profile ≠ [] := by
  have h : ((0 : Element profile), (0 : Rat)) ∈ candidates profile :=
    mem_candidates.mpr (toRat?_zero profile)
  exact List.ne_nil_of_mem h

/-- The executable finite element conversion satisfies the nearest-even numerical contract. -/
theorem quantizeFinite_quantizes (profile : Profile) (input : SignedRat) :
    Quantizes input (quantizeFinite profile input) := by
  obtain ⟨candidate, hcandidate⟩ :
      ∃ candidate, (candidates profile).argmin (roundingKey input) = some candidate := by
    cases h : (candidates profile).argmin (roundingKey input) with
    | none => exact False.elim (candidates_ne_nil profile (List.argmin_eq_none.mp h))
    | some candidate => exact ⟨candidate, rfl⟩
  have hmem : candidate ∈ (candidates profile).argmin (roundingKey input) := by
    simp [hcandidate]
  have hdecode := mem_candidates.mp (List.argmin_mem hmem)
  refine ⟨candidate.2, ?_, ?_⟩
  · simpa [quantizeFinite, hcandidate] using hdecode
  · intro other otherValue hother
    simpa [quantizeFinite, hcandidate] using
      (List.le_of_mem_argmin (mem_candidates.mpr hother) hmem)

/-- No finite element word has smaller absolute error than the rounded result. -/
theorem Quantizes.error_le {profile : Profile} {input : SignedRat}
    {word other : Element profile} {value otherValue : Rat}
    (h : Quantizes input word) (hvalue : toRat? word = some value)
    (hother : toRat? other = some otherValue) :
    |value - input.value| ≤ |otherValue - input.value| := by
  obtain ⟨result, hresult, hmin⟩ := h
  have : result = value := Option.some.inj (hresult.symm.trans hvalue)
  subst result
  exact Prod.Lex.monotone_fst _ _ (hmin other otherValue hother)

/-- A representable rational is reproduced exactly, including at finite endpoints. -/
theorem Quantizes.exact {profile : Profile} {input : SignedRat}
    {word other : Element profile} {value : Rat}
    (h : Quantizes input word) (hvalue : toRat? word = some value)
    (hother : toRat? other = some input.value) : value = input.value := by
  have herror := h.error_le hvalue hother
  simpa only [sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] using herror

/-- An equally close even word prevents selection of an odd word. -/
theorem Quantizes.even_of_tie {profile : Profile} {input : SignedRat}
    {word other : Element profile} {value otherValue : Rat}
    (h : Quantizes input word) (hvalue : toRat? word = some value)
    (hother : toRat? other = some otherValue)
    (htie : |value - input.value| = |otherValue - input.value|)
    (heven : other.toNat % 2 = 0) : word.toNat % 2 = 0 := by
  obtain ⟨result, hresult, hmin⟩ := h
  have : result = value := Option.some.inj (hresult.symm.trans hvalue)
  subst result
  have hkey := (Prod.Lex.toLex_le_toLex'.mp (hmin other otherValue hother)).2 htie
  simp only [heven, mul_zero, zero_add] at hkey
  split_ifs at hkey <;> omega

end FloatLib.Floats.Formats.OCP.MX.Standard.Element
