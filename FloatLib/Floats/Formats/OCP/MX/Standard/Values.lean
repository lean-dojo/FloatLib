/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Format

/-!
# Finite values of OCP MX element profiles

For the element profiles of OCP MX v1.0 §5.3, the constants give the zero threshold, relative
error coefficient and finite
endpoints. `Profile.sorted` lists finite words in value order, and `Profile.values` forgets
their encodings. `Profile.values_adjacent` kernel-checks the endpoints and error gaps used
by the rounding and error-bound arguments.

`exists_adjacent_bracket` is the shared ordered-list argument, valid over any linear order
without a sortedness hypothesis. `Profile.toReal_ofNatBits` connects a floating profile's
word encoding with its rational value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics FloatLib.Floats.Formats

variable {ι γ : Type} [Fintype ι] [DecidableEq γ]

/-- Half the least positive element value of a profile: the largest magnitude its codec stores
as zero. -/
def Profile.zeroThreshold : Profile → ℚ
  | .e5m2 => 1 / 131072
  | .e4m3 => 1 / 1024
  | .e3m2 => 1 / 32
  | .e2m3 => 1 / 16
  | .e2m1 => 1 / 4
  | .int8 => 1 / 128

/-- Relative error of a profile's element codec: `2 ^ (-precision)`, and zero for INT8. -/
def Profile.unitRoundoff : Profile → ℚ
  | .e5m2 | .e3m2 => 1 / 8
  | .e4m3 | .e2m3 => 1 / 16
  | .e2m1 => 1 / 4
  | .int8 => 0

/-- Largest positive element value of a profile. -/
def Profile.maxMagnitude : Profile → ℚ
  | .e5m2 => 57344
  | .e4m3 => 448
  | .e3m2 => 28
  | .e2m3 => 15 / 2
  | .e2m1 => 6
  | .int8 => 127 / 64

/-- Least element value of a profile: minus the largest one, and `-2` for INT8. -/
def Profile.lowest : Profile → ℚ
  | .int8 => -2
  | profile => -profile.maxMagnitude

/-- The finite element words of a profile with their values, in increasing order of value: the
words with the sign bit set, largest magnitude first, then the other words in code order. -/
def Profile.sorted (profile : Profile) : List (Element profile × ℚ) :=
  let positive := (Element.candidates profile).takeWhile fun c => !Element.negative c.1
  let negative := (Element.candidates profile).dropWhile fun c => !Element.negative c.1
  (if profile = .int8 then negative else negative.reverse) ++ positive

/-- The finite element values of a profile in increasing order. -/
def Profile.values (profile : Profile) : List ℚ :=
  profile.sorted.map Prod.snd

/-- The sorted words of a profile are its finite words. -/
theorem Profile.mem_sorted (profile : Profile) {c : Element profile × ℚ} :
    c ∈ profile.sorted ↔ c ∈ Element.candidates profile := by
  have happend := List.takeWhile_append_dropWhile
    (p := fun c : Element profile × ℚ => !Element.negative c.1) (l := Element.candidates profile)
  simp only [Profile.sorted]
  constructor
  · intro hc
    rcases List.mem_append.mp hc with hneg | hpos
    · have hdrop : c ∈ (Element.candidates profile).dropWhile fun c => !Element.negative c.1 := by
        split_ifs at hneg
        · exact hneg
        · exact List.mem_reverse.mp hneg
      exact (List.dropWhile_sublist _).subset hdrop
    · exact (List.takeWhile_sublist _).subset hpos
  · intro hc
    rw [← happend] at hc
    rcases List.mem_append.mp hc with hpos | hneg
    · exact List.mem_append.mpr (Or.inr hpos)
    · refine List.mem_append.mpr (Or.inl ?_)
      split_ifs
      · exact hneg
      · exact List.mem_reverse.mpr hneg

/-- The facts about the sorted element values of a profile that its error budget rests on: the
least and the largest value, and for every two adjacent values that half their gap is within the
budget at the smaller magnitude and that they do not straddle zero. -/
theorem Profile.values_adjacent (profile : Profile) :
    profile.values.head? = some profile.lowest ∧
      profile.values.getLast? = some profile.maxMagnitude ∧
      ∀ p ∈ profile.values.zip profile.values.tail,
        (p.2 - p.1) / 2 ≤ profile.unitRoundoff * min |p.1| |p.2| + profile.zeroThreshold ∧
          (0 ≤ p.1 ∨ p.2 ≤ 0) := by
  cases profile <;> decide +kernel

/-- A point between a list's first and last entries either is its first entry or lies
between two consecutive entries. The list need not be sorted. -/
theorem exists_adjacent_bracket {K : Type*} [LinearOrder K] :
    ∀ (l : List K) (a q hi : K),
    (a :: l).getLast? = some hi → a ≤ q → q ≤ hi →
      (∃ p ∈ (a :: l).zip l, p.1 ≤ q ∧ q ≤ p.2) ∨ q = a
  | [], a, q, hi, hlast, h1, h2 => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    exact Or.inr (le_antisymm h2 h1)
  | b :: l, a, q, hi, hlast, h1, h2 => by
    by_cases hb : q ≤ b
    · exact Or.inl ⟨(a, b), by simp, h1, hb⟩
    · have hlast' : (b :: l).getLast? = some hi := by
        rwa [List.getLast?_cons_cons] at hlast
      rcases exists_adjacent_bracket l b q hi hlast' (le_of_not_ge hb) h2 with
        ⟨p, hp, hp1, hp2⟩ | rfl
      · exact Or.inl ⟨p, List.mem_cons_of_mem _ hp, hp1, hp2⟩
      · exact absurd le_rfl hb

/-- The binary word with the bits of an element code of a floating profile has the code's
rational value. A code with no finite value has the value zero on both sides. -/
theorem Profile.toReal_ofNatBits (profile : Profile) {fmt : BinaryInterchange.FloatFormat}
    (hfmt : profile.floatFormat? = some fmt) (word : Element profile) :
    BinaryInterchange.Model.toReal (BinaryInterchange.Model.ofNatBits (fmt := fmt) word.toNat) =
      ((Block.finiteValue (Element.decode word) : ℚ) : ℝ) := by
  have hdecode : Element.decode word =
      Element.decodeFloat (BinaryInterchange.Model.ofNatBits (fmt := fmt) word.toNat) := by
    cases profile <;>
      simp only [Profile.floatFormat?, Option.some.injEq, reduceCtorEq] at hfmt <;>
      subst hfmt <;> rfl
  rw [hdecode, ← BinaryInterchange.Model.cast_toRat_eq_toReal]
  congr 1
  simp only [Element.decodeFloat, BinaryInterchange.Model.toRat?]
  cases h : BinaryInterchange.Model.toDyadic?
      (BinaryInterchange.Model.ofNatBits (fmt := fmt) word.toNat) with
  | some d => simp [Block.finiteValue]
  | none =>
    by_cases hinf : BinaryInterchange.Model.isInfinite
        (BinaryInterchange.Model.ofNatBits (fmt := fmt) word.toNat) <;>
      simp [Block.finiteValue, hinf]

end FloatLib.Floats.Formats.OCP.MX.Standard
