/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Values

/-!
# Saturating nearest-even rounding of OCP MX elements

Every saturating profile codec rounds to a nearest finite word, with ties to the even word.
The zero threshold characterizes precisely the inputs rounded to zero. The midpoint and
endpoint results prove that the codec agrees with another nearest rounding whenever they
agree on the finite words, adjacent midpoints and the two tails.

The six profiles satisfy these premises for their real roundings. The resulting equality
also applies to a stored position under any block format and selection policy.

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.3 and 6.3.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics FloatLib.Floats.Formats

variable {ι γ : Type}

/-- With SAT conversion, the element codec of a profile is at least as close to every input as
any finite element word. -/
theorem Profile.abs_codec_round_sub_le (profile : Profile) (y : ℚ) {other : Element profile}
    {q : ℚ} (hother : Element.toRat? other = some q) :
    |(profile.codec .saturate).rounding.round y - y| ≤ |q - y| := by
  have hq := Element.quantize_quantizesWith profile .saturate (SignedRat.ofRat y)
  simp only [Element.QuantizesWith, reduceCtorEq, false_and, ite_false] at hq
  obtain ⟨value, hvalue, -⟩ := id hq
  have h := Element.Quantizes.error_le hq hvalue hother
  have hround : (profile.codec .saturate).rounding.round y = value :=
    Element.finiteValue_decode hvalue
  rw [hround]
  simpa using h

/-- The facts about the finite words of a profile that its zero set rests on: twice the threshold
and its negative are element values, no nonzero element value is smaller in magnitude, and the
words of these two values are odd. -/
private theorem Profile.zeroThreshold_words (profile : Profile) :
    (∃ c ∈ Element.candidates profile, c.2 = 2 * profile.zeroThreshold) ∧
      (∃ c ∈ Element.candidates profile, c.2 = -(2 * profile.zeroThreshold)) ∧
      (∀ c ∈ Element.candidates profile, c.2 = 0 ∨ 2 * profile.zeroThreshold ≤ |c.2|) ∧
      ∀ c ∈ Element.candidates profile, |c.2| = 2 * profile.zeroThreshold →
        c.1.toNat % 2 = 1 := by
  cases profile <;> decide +kernel

/--
Flush to zero of the element codec of every profile, on exact rationals: with SAT conversion an
input is stored as zero exactly when its magnitude is at most half the least positive element
value. The tie goes to zero, because the zero word is even.
-/
theorem Profile.codec_round_eq_zero_iff (profile : Profile) (q : ℚ) :
    (profile.codec .saturate).rounding.round q = 0 ↔ |q| ≤ profile.zeroThreshold := by
  obtain ⟨⟨⟨wp, vp⟩, hp, hpv⟩, ⟨⟨wn, vn⟩, hn, hnv⟩, hgap, hodd⟩ := profile.zeroThreshold_words
  have hq := Element.quantize_quantizesWith profile .saturate (SignedRat.ofRat q)
  simp only [Element.QuantizesWith, reduceCtorEq, false_and, ite_false] at hq
  obtain ⟨value, hvalue, -⟩ := id hq
  have hround : (profile.codec .saturate).rounding.round q = value :=
    Element.finiteValue_decode hvalue
  have hτ : 0 < profile.zeroThreshold := by
    cases profile <;> norm_num [Profile.zeroThreshold]
  have ep := Element.Quantizes.error_le hq hvalue (Element.mem_candidates.mp hp)
  have en := Element.Quantizes.error_le hq hvalue (Element.mem_candidates.mp hn)
  have e0 := Element.Quantizes.error_le hq hvalue (Element.toRat?_zero profile)
  simp only [SignedRat.value_ofRat] at ep en e0
  dsimp only at hpv hnv
  rw [hpv] at ep
  rw [hnv] at en
  rw [hround]
  constructor
  · rintro rfl
    rw [zero_sub, abs_neg] at ep en
    rcases le_total 0 q with h | h
    · rw [abs_of_nonneg h] at ep ⊢
      by_contra hlt
      rcases le_total q (2 * profile.zeroThreshold) with h2 | h2
      · rw [abs_of_nonneg (by linarith)] at ep
        linarith
      · rw [abs_of_nonpos (by linarith)] at ep
        linarith
    · rw [abs_of_nonpos h] at en ⊢
      by_contra hlt
      rcases le_total (-(2 * profile.zeroThreshold)) q with h2 | h2
      · rw [abs_of_nonpos (by linarith)] at en
        linarith
      · rw [abs_of_nonneg (by linarith)] at en
        linarith
  · intro hle
    rw [zero_sub, abs_neg] at e0
    have hv : |value| ≤ 2 * profile.zeroThreshold := by
      have h1 := Numerics.Backward.abs_add_le_add (e0.trans hle) hle
      simpa only [sub_add_cancel, two_mul] using h1
    rcases hgap _ (Element.mem_candidates.mpr hvalue) with h0 | hm
    · exact h0
    · have habs : |value| = 2 * profile.zeroThreshold := le_antisymm hv hm
      have hlow : |value| - |q| ≤ |value - q| := abs_sub_abs_le_abs_sub value q
      have htie : |value - (SignedRat.ofRat q).value| = |0 - (SignedRat.ofRat q).value| := by
        rw [SignedRat.value_ofRat, zero_sub, abs_neg]
        linarith
      have heven := Element.Quantizes.even_of_tie hq hvalue (Element.toRat?_zero profile) htie
        (by simp)
      have hodd' := hodd _ (Element.mem_candidates.mpr hvalue) habs
      dsimp only at hodd'
      omega

/-- With SAT conversion the element codec of a profile is a nearest rounding onto its values. -/
theorem Profile.codec_nearest (profile : Profile) :
    (profile.codec .saturate).rounding.Nearest := by
  intro x y
  have hq := Element.quantize_quantizesWith profile .saturate (SignedRat.ofRat y)
  simp only [Element.QuantizesWith, reduceCtorEq, false_and, ite_false] at hq
  obtain ⟨value, hvalue, -⟩ := id hq
  rw [show (profile.codec .saturate).rounding.round y = value from
    Element.finiteValue_decode hvalue]
  exact profile.abs_codec_round_sub_le x hvalue

/-- The element codec stores the value of every finite word exactly. -/
theorem Profile.codec_round_of_mem_sorted (profile : Profile) {c : Element profile × ℚ}
    (hc : c ∈ profile.sorted) : (profile.codec .saturate).rounding.round c.2 = c.2 := by
  have hq := Element.quantize_quantizesWith profile .saturate (SignedRat.ofRat c.2)
  simp only [Element.QuantizesWith, reduceCtorEq, false_and, ite_false] at hq
  obtain ⟨value, hvalue, -⟩ := id hq
  rw [show (profile.codec .saturate).rounding.round c.2 = value from
    Element.finiteValue_decode hvalue]
  have h := Element.Quantizes.exact hq hvalue (other := c.1)
    (by rw [SignedRat.value_ofRat]; exact Element.mem_candidates.mp (profile.mem_sorted.mp hc))
  rwa [SignedRat.value_ofRat] at h

/-- The saturating codec fixes every listed finite value. -/
theorem Profile.codec_round_of_mem_values (profile : Profile) {q : ℚ}
    (hq : q ∈ profile.values) : (profile.codec .saturate).rounding.round q = q := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
  exact profile.codec_round_of_mem_sorted hc

/-- Facts about the sorted words of a profile that the kernel checks. Two adjacent words increase
in value or are the two zeros, and their codes have different parity unless they are the two
zeros. A word of value zero has an even code. Every value lies between the least and the largest
one. -/
private theorem Profile.sorted_words (profile : Profile) :
    (∀ p ∈ profile.sorted.zip profile.sorted.tail,
        (p.1.2 < p.2.2 ∨ (p.1.2 = 0 ∧ p.2.2 = 0)) ∧
          ((p.1.2 = 0 ∧ p.2.2 = 0) ∨ p.1.1.toNat % 2 ≠ p.2.1.toNat % 2)) ∧
      (∀ c ∈ profile.sorted, c.2 = 0 → c.1.toNat % 2 = 0) ∧
      ∀ c ∈ profile.sorted, profile.lowest ≤ c.2 ∧ c.2 ≤ profile.maxMagnitude := by
  cases profile <;> decide +kernel

/-- Every saturating rounded value lies between the least and greatest finite values. -/
theorem Profile.codec_round_mem_Icc (profile : Profile) (q : ℚ) :
    (profile.codec .saturate).rounding.round q ∈
      Set.Icc profile.lowest profile.maxMagnitude := by
  have hq := Element.quantize_quantizesWith profile .saturate (SignedRat.ofRat q)
  simp only [Element.QuantizesWith, reduceCtorEq, false_and, ite_false] at hq
  obtain ⟨value, hvalue, -⟩ := hq
  rw [show (profile.codec .saturate).rounding.round q = value from
    Element.finiteValue_decode hvalue]
  exact profile.sorted_words.2.2 _ (profile.mem_sorted.mpr (Element.mem_candidates.mpr hvalue))

/-- Two adjacent entries of a list split it around them. -/
private theorem exists_append_of_mem_zip_tail {α : Type} :
    ∀ (l : List α) (p : α × α), p ∈ l.zip l.tail → ∃ l₁ l₂, l = l₁ ++ p.1 :: p.2 :: l₂
  | [], p, h => by simp at h
  | [a], p, h => by simp at h
  | a :: b :: t, p, h => by
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨[], t, rfl⟩
    · obtain ⟨l₁, l₂, hl⟩ := exists_append_of_mem_zip_tail (b :: t) p h
      exact ⟨a :: l₁, l₂, by rw [hl]; rfl⟩

/-- A transitive relation that holds between adjacent entries holds between all ordered pairs. -/
private theorem pairwise_of_forall_mem_zip_tail {α : Type} {R : α → α → Prop}
    (hR : ∀ a b c, R a b → R b c → R a c) :
    ∀ l : List α, (∀ p ∈ l.zip l.tail, R p.1 p.2) → l.Pairwise R := by
  let : Trans R R R := ⟨hR _ _ _⟩
  intro l h
  apply List.IsChain.pairwise
  rw [List.isChain_iff_getElem]
  intro i hi
  exact h (l[i], l[i + 1]) (List.mem_iff_getElem?.mpr ⟨i, List.getElem?_zip_eq_some.mpr
    ⟨by simp [Nat.lt_of_succ_lt hi], by simp [hi]⟩⟩)

/-- The sorted words of a profile increase in value, except for the two zeros. -/
private theorem Profile.sorted_pairwise (profile : Profile) :
    profile.sorted.Pairwise fun x y => x.2 < y.2 ∨ (x.2 = 0 ∧ y.2 = 0) :=
  pairwise_of_forall_mem_zip_tail
    (fun a b c hab hbc => by
      rcases hab with hab | ⟨ha, hb⟩ <;> rcases hbc with hbc | ⟨hb', hc⟩
      · exact Or.inl (lt_trans hab hbc)
      · exact Or.inl (by rw [hc, ← hb']; exact hab)
      · exact Or.inl (by rw [ha, ← hb]; exact hbc)
      · exact Or.inr ⟨ha, hc⟩)
    _ fun p hp => (profile.sorted_words.1 p hp).1

/--
Ties go to the even code. At the midpoint of two adjacent finite words of different values, the
codec of every profile stores the value of the word with the even code.
-/
theorem Profile.codec_round_midpoint (profile : Profile) {x y : Element profile × ℚ}
    (hp : (x, y) ∈ profile.sorted.zip profile.sorted.tail) (hlt : x.2 < y.2) :
    (profile.codec .saturate).rounding.round ((x.2 + y.2) / 2) =
      if x.1.toNat % 2 = 0 then x.2 else y.2 := by
  have hpar : x.1.toNat % 2 ≠ y.1.toNat % 2 :=
    (profile.sorted_words.1 _ hp).2.resolve_left fun h => by
      dsimp only at h
      rw [h.1, h.2] at hlt
      exact lt_irrefl _ hlt
  obtain ⟨l₁, l₂, hl⟩ := exists_append_of_mem_zip_tail _ _ hp
  dsimp only at hl
  have hpw := profile.sorted_pairwise
  rw [hl] at hpw
  obtain ⟨-, hpw2, hcross⟩ := List.pairwise_append.mp hpw
  obtain ⟨-, hpw3⟩ := List.pairwise_cons.mp hpw2
  obtain ⟨hy2, -⟩ := List.pairwise_cons.mp hpw3
  have hxs : x ∈ profile.sorted := by rw [hl]; simp
  have hys : y ∈ profile.sorted := by rw [hl]; simp
  have hxc := Element.mem_candidates.mp (profile.mem_sorted.mp hxs)
  have hyc := Element.mem_candidates.mp (profile.mem_sorted.mp hys)
  have hzero := (Profile.sorted_words profile).2.1
  have hq := Element.quantize_quantizesWith profile .saturate
    (SignedRat.ofRat ((x.2 + y.2) / 2))
  simp only [Element.QuantizesWith, reduceCtorEq, false_and, ite_false] at hq
  obtain ⟨v, hvalue, -⟩ := id hq
  rw [show (profile.codec .saturate).rounding.round ((x.2 + y.2) / 2) = v from
    Element.finiteValue_decode hvalue]
  have ex := Element.Quantizes.error_le hq hvalue hxc
  have hxm : |x.2 - (x.2 + y.2) / 2| = (y.2 - x.2) / 2 := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hym : |y.2 - (x.2 + y.2) / 2| = (y.2 - x.2) / 2 := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [SignedRat.value_ofRat, hxm] at ex
  obtain ⟨hv1, hv2⟩ := abs_le.mp ex
  -- The selected word is one of the sorted words. Its position gives its value.
  have hws := profile.mem_sorted.mpr (Element.mem_candidates.mpr hvalue)
  rw [hl] at hws
  generalize Element.quantize profile
    (NumericalValue.finite (SignedRat.ofRat ((x.2 + y.2) / 2))) OverflowMode.saturate = w
    at hq hvalue hws
  have hpos : (w, v) ∈ l₁ ∨ (w, v) = x ∨ (w, v) = y ∨ (w, v) ∈ l₂ := by
    simpa only [List.mem_append, List.mem_cons] using hws
  have hvalues : v = x.2 ∨ v = y.2 := by
    rcases hpos with h | h | h | h
    · rcases hcross _ h x (by simp) with h' | ⟨h', h''⟩
      · exact absurd h' (by dsimp only; linarith)
      · exact Or.inl (by dsimp only at h'; rw [h', h''])
    · exact Or.inl (by rw [← h])
    · exact Or.inr (by rw [← h])
    · rcases hy2 _ h with h' | ⟨h', h''⟩
      · exact absurd h' (by dsimp only; linarith)
      · exact Or.inr (by dsimp only at h''; rw [h', h''])
  by_cases hxe : x.1.toNat % 2 = 0
  · simp only [hxe, ↓reduceIte]
    by_contra hne
    have hvy : v = y.2 := hvalues.resolve_left hne
    have htie : |v - (SignedRat.ofRat ((x.2 + y.2) / 2)).value| =
        |x.2 - (SignedRat.ofRat ((x.2 + y.2) / 2)).value| := by
      rw [SignedRat.value_ofRat, hvy, hym, hxm]
    have heven := Element.Quantizes.even_of_tie hq hvalue hxc htie hxe
    rcases hpos with h | h | h | h
    · rcases hcross _ h x (by simp) with h' | ⟨h', h''⟩
      · exact absurd h' (by dsimp only; linarith)
      · exact hne (by dsimp only at h'; rw [h', h''])
    · exact hne (by rw [← h])
    · rw [← h] at hpar
      dsimp only at hpar
      omega
    · rcases hy2 _ h with h' | ⟨h', _⟩
      · exact absurd h' (by dsimp only; linarith)
      · have := hzero y hys h'
        omega
  · simp only [hxe, ↓reduceIte]
    by_contra hne
    have hvx : v = x.2 := hvalues.resolve_right hne
    have hye : y.1.toNat % 2 = 0 := by omega
    have htie : |v - (SignedRat.ofRat ((x.2 + y.2) / 2)).value| =
        |y.2 - (SignedRat.ofRat ((x.2 + y.2) / 2)).value| := by
      rw [SignedRat.value_ofRat, hvx, hym, hxm]
    have heven := Element.Quantizes.even_of_tie hq hvalue hyc htie hye
    rcases hpos with h | h | h | h
    · rcases hcross _ h x (by simp) with h' | ⟨_, h''⟩
      · exact absurd h' (by dsimp only; linarith)
      · exact hxe (hzero x hxs h'')
    · rw [← h] at hxe
      exact hxe heven
    · exact hne (by rw [← h])
    · rcases hy2 _ h with h' | ⟨h', h''⟩
      · exact absurd h' (by dsimp only; linarith)
      · dsimp only at h''
        linarith

/--
The codec of a profile is determined among nearest roundings by finitely many values. Let `R` be
a nearest rounding over an ordered field that stores every input at or beyond the largest and the
least element value as that value, stores the value of each finite word exactly, and stores the
midpoint of two adjacent words as the value of the word with the even code. Then `R` is the
profile's codec with SAT conversion on every rational.
-/
theorem Profile.codec_round_eq_of_nearest (profile : Profile) {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] {R : Block.Rounding K} (hR : R.Nearest)
    (hhigh : ∀ q : ℚ, profile.maxMagnitude ≤ q →
      R.round (q : K) = ((profile.maxMagnitude : ℚ) : K))
    (hlow : ∀ q : ℚ, q ≤ profile.lowest → R.round (q : K) = ((profile.lowest : ℚ) : K))
    (hadj : ∀ p ∈ profile.sorted.zip profile.sorted.tail,
      R.round ((p.1.2 : ℚ) : K) = ((p.1.2 : ℚ) : K) ∧
        R.round ((p.2.2 : ℚ) : K) = ((p.2.2 : ℚ) : K) ∧
        (p.1.2 < p.2.2 → R.round (((p.1.2 + p.2.2) / 2 : ℚ) : K) =
          ((if p.1.1.toNat % 2 = 0 then p.1.2 else p.2.2 : ℚ) : K)))
    (q : ℚ) : (((profile.codec .saturate).rounding.round q : ℚ) : K) = R.round (q : K) := by
  obtain ⟨hhead, hlast, -⟩ := profile.values_adjacent
  rcases le_or_gt profile.maxMagnitude q with hbig | hlt
  · -- at or above the largest value
    rw [profile.codec_nearest.round_eq_of_ge
      (profile.codec_round_of_mem_values (List.mem_of_mem_getLast? (Option.mem_def.mpr hlast)))
      (fun x => (profile.codec_round_mem_Icc x).2) hbig, hhigh q hbig]
  rcases le_or_gt q profile.lowest with hsmall | hgt
  · -- at or below the least value
    rw [profile.codec_nearest.round_eq_of_le
      (profile.codec_round_of_mem_values (List.mem_of_mem_head? (Option.mem_def.mpr hhead)))
      (fun x => (profile.codec_round_mem_Icc x).1) hsmall, hlow q hsmall]
  · -- strictly inside the range: between two adjacent words
    obtain ⟨a, l, hvals⟩ : ∃ a l, profile.values = a :: l := by
      cases hl : profile.values with
      | nil => simp [hl] at hhead
      | cons a l => exact ⟨a, l, rfl⟩
    have ha : a = profile.lowest := by simpa [hvals] using hhead
    rw [hvals] at hlast
    rcases exists_adjacent_bracket l a q _ hlast (ha ▸ hgt.le) hlt.le with ⟨p, hp, h1, h2⟩ | rfl
    · have hp' : p ∈ profile.values.zip profile.values.tail := by
        rw [hvals]
        exact hp
      rw [Profile.values, ← List.map_tail, List.zip_map] at hp'
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := List.mem_map.mp hp'
      dsimp only [Prod.map] at h1 h2
      obtain ⟨hRx, hRy, hRm⟩ := hadj _ hxy
      dsimp only at hRx hRy hRm
      have hCx := profile.codec_round_of_mem_sorted (List.of_mem_zip hxy).1
      have hCy := profile.codec_round_of_mem_sorted
        (List.mem_of_mem_tail (List.of_mem_zip hxy).2)
      rcases (profile.sorted_words.1 _ hxy).1 with hlt' | ⟨hx0, hy0⟩
      · dsimp only at hlt'
        have hRm' := hRm hlt'
        have hcast : (((x.2 + y.2) / 2 : ℚ) : K) = ((x.2 : K) + (y.2 : K)) / 2 := by
          push_cast
          rfl
        have hCm := profile.codec_round_midpoint hxy hlt'
        have hmC : (profile.codec .saturate).rounding.round ((x.2 + y.2) / 2) = x.2 ∨
            (profile.codec .saturate).rounding.round ((x.2 + y.2) / 2) = y.2 := by
          rw [hCm]
          split_ifs
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hmR : R.round (((x.2 : K) + (y.2 : K)) / 2) = (x.2 : K) ∨
            R.round (((x.2 : K) + (y.2 : K)) / 2) = (y.2 : K) := by
          rw [← hcast, hRm']
          split_ifs
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases lt_trichotomy q ((x.2 + y.2) / 2) with hqm | rfl | hqm
        · rw [profile.codec_nearest.round_eq_left hCx hmC h1 hqm,
            hR.round_eq_left hRx hmR (by exact_mod_cast h1)
              (by rw [← hcast]; exact_mod_cast hqm)]
        · rw [hCm, hRm']
        · rw [profile.codec_nearest.round_eq_right hCy hmC hqm h2,
            hR.round_eq_right hRy hmR (by rw [← hcast]; exact_mod_cast hqm)
              (by exact_mod_cast h2)]
      · dsimp only at hx0 hy0
        obtain rfl : q = x.2 := by
          rw [hx0]
          exact le_antisymm (hy0 ▸ h2) (hx0 ▸ h1)
        rw [hCx, hRx]
    · exact absurd hgt (by rw [ha]; exact lt_irrefl _)

/--
The real rounding of a profile's element format: saturating nearest-even rounding of the binary
descriptor for the floating profiles, and for INT8 nearest-even fixed point with six fractional
bits clipped to `[-2, 127 / 64]`.
-/
noncomputable def Profile.real : Profile → Block.Rounding ℝ
  | .e5m2 => Block.Rounding.saturating .e5m2
  | .e4m3 => Block.Rounding.saturating .e4m3
  | .e3m2 => Block.Rounding.saturating .e3m2
  | .e2m3 => Block.Rounding.saturating .e2m3
  | .e2m1 => Block.Rounding.saturating .e2m1
  | .int8 => Block.Rounding.fixed 6 (-2) (127 / 64)

/--
The check, by integer arithmetic on the sorted finite words of a profile, of the premises of
`Profile.codec_round_eq_of_nearest` for the real rounding of the profile. For every two adjacent
words, the real rounding stores both values exactly, and when the values differ it stores their
midpoint as the value of the word with the even code. The real rounding is evaluated by
`Block.Rounding.RoundsTo` for a floating profile and by `Block.Rounding.fixedRat` for INT8.
-/
def Profile.midpointsAgree (profile : Profile) : Bool :=
  (profile.sorted.zip profile.sorted.tail).all fun p =>
    match profile.floatFormat? with
    | some fmt =>
        decide (Block.Rounding.RoundsTo fmt profile.maxMagnitude p.1.2 p.1.2 ∧
          Block.Rounding.RoundsTo fmt profile.maxMagnitude p.2.2 p.2.2 ∧
          (p.1.2 < p.2.2 → Block.Rounding.RoundsTo fmt profile.maxMagnitude
            ((p.1.2 + p.2.2) / 2) (if p.1.1.toNat % 2 = 0 then p.1.2 else p.2.2)))
    | none =>
        decide ((Block.Rounding.fixedRat 6 (-2) (127 / 64)).round p.1.2 = p.1.2 ∧
          (Block.Rounding.fixedRat 6 (-2) (127 / 64)).round p.2.2 = p.2.2 ∧
          (p.1.2 < p.2.2 → (Block.Rounding.fixedRat 6 (-2) (127 / 64)).round
            ((p.1.2 + p.2.2) / 2) = if p.1.1.toNat % 2 = 0 then p.1.2 else p.2.2))

/-- The check passes for every profile. The kernel evaluates it. -/
theorem Profile.midpointsAgree_eq_true (profile : Profile) : profile.midpointsAgree = true := by
  cases profile <;> decide +kernel

/-- The largest finite value of the descriptor of a floating profile is the profile's largest
element value. -/
private theorem Profile.toReal_posMaxFinite (profile : Profile)
    {fmt : BinaryInterchange.FloatFormat} (hfmt : profile.floatFormat? = some fmt) :
    BinaryInterchange.Model.toReal (BinaryInterchange.Model.posMaxFinite fmt) =
      (profile.maxMagnitude : ℝ) := by
  cases profile <;>
    simp only [Profile.floatFormat?, Option.some.injEq, reduceCtorEq] at hfmt <;> subst hfmt
  · rw [BinaryInterchange.Model.toReal_posMaxFinite_of_eq .e5m2 (significand := 7)
      (exponent := 13) (by decide) (by decide)]
    norm_num [Profile.maxMagnitude]
  · rw [BinaryInterchange.Model.toReal_posMaxFinite_of_eq .e4m3 (significand := 14)
      (exponent := 5) (by decide) (by decide)]
    norm_num [Profile.maxMagnitude]
  · rw [BinaryInterchange.Model.toReal_posMaxFinite_of_eq .e3m2 (significand := 7)
      (exponent := 2) (by decide) (by decide)]
    norm_num [Profile.maxMagnitude]
  · rw [BinaryInterchange.Model.toReal_posMaxFinite_of_eq .e2m3 (significand := 15)
      (exponent := -1) (by decide) (by decide)]
    norm_num [Profile.maxMagnitude]
  · rw [BinaryInterchange.Model.toReal_posMaxFinite_of_eq .e2m1 (significand := 3)
      (exponent := 1) (by decide) (by decide)]
    norm_num [Profile.maxMagnitude]

/-- A floating profile's codec is the saturating nearest-even rounding of its descriptor. -/
private theorem Profile.codec_round_eq_saturating (profile : Profile)
    {fmt : BinaryInterchange.FloatFormat} (hfmt : profile.floatFormat? = some fmt) (q : ℚ) :
    (((profile.codec .saturate).rounding.round q : ℚ) : ℝ) =
      (Block.Rounding.saturating fmt).round (q : ℝ) := by
  have hM := profile.toReal_posMaxFinite hfmt
  have hlowest : profile.lowest = -profile.maxMagnitude := by
    cases profile <;> first | rfl | simp [Profile.floatFormat?] at hfmt
  have hfacts := profile.midpointsAgree_eq_true
  simp only [Profile.midpointsAgree, hfmt, List.all_eq_true, decide_eq_true_eq] at hfacts
  refine profile.codec_round_eq_of_nearest (Block.Rounding.saturating_nearest fmt) ?_ ?_ ?_ q
  · intro q hq
    rw [Block.Rounding.saturating_round_of_le (by rw [hM]; exact_mod_cast hq), hM]
  · intro q hq
    rw [hlowest] at hq
    rw [Block.Rounding.saturating_round_of_le_neg (by rw [hM]; exact_mod_cast hq), hM, hlowest]
    push_cast
    rfl
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := hfacts p hp
    exact ⟨h1.round_eq hM, h2.round_eq hM, fun hlt => (h3 hlt).round_eq hM⟩

/-- The INT8 codec is nearest-even fixed point with six fractional bits clipped to
`[-2, 127 / 64]`, computed over the rationals. -/
private theorem Profile.int8_codec_round_eq_fixedRat (q : ℚ) :
    (Profile.int8.codec .saturate).rounding.round q =
      (Block.Rounding.fixedRat 6 (-2) (127 / 64)).round q := by
  have hnearest : (Block.Rounding.fixedRat 6 (-2) (127 / 64)).Nearest := by
    have h := Block.Rounding.fixedRat_nearest 6 (a := -128) (b := 127) (by norm_num)
    have ha : ((-128 : ℤ) : ℚ) * 2 ^ (-(6 : ℤ)) = -2 := by norm_num
    have hb : ((127 : ℤ) : ℚ) * 2 ^ (-(6 : ℤ)) = 127 / 64 := by norm_num
    rwa [ha, hb] at h
  have hfacts := Profile.midpointsAgree_eq_true .int8
  simp only [Profile.midpointsAgree, Profile.floatFormat?, List.all_eq_true,
    decide_eq_true_eq] at hfacts
  have hle : ∀ x, (Block.Rounding.fixedRat 6 (-2) (127 / 64)).round x ≤ 127 / 64 := fun x =>
    max_le (by norm_num) (min_le_left _ _)
  have hge : ∀ x, -2 ≤ (Block.Rounding.fixedRat 6 (-2) (127 / 64)).round x := fun x =>
    le_max_left _ _
  have h := Profile.int8.codec_round_eq_of_nearest (K := ℚ) hnearest
    (fun q hq => by
      simp only [Rat.cast_id]
      exact hnearest.round_eq_of_ge
        (show (Block.Rounding.fixedRat 6 (-2) (127 / 64)).round (127 / 64) = 127 / 64 by
          decide +kernel) hle hq)
    (fun q hq => by
      simp only [Rat.cast_id]
      exact hnearest.round_eq_of_le
        (show (Block.Rounding.fixedRat 6 (-2) (127 / 64)).round (-2) = -2 by decide +kernel)
        hge hq)
    (fun p hp => by simpa only [Rat.cast_id] using hfacts p hp) q
  simpa only [Rat.cast_id] using h

/--
The element codec of every profile is the real rounding of the value theory. For each of the six
profiles and every rational `q`, the value the executable codec stores with SAT conversion is
`profile.real` at `q`: the saturating nearest-even rounding of the binary descriptor for E5M2,
E4M3, E3M2, E2M3 and E2M1, and nearest-even fixed point clipped to `[-2, 127 / 64]` for INT8. So
every theorem about these real roundings holds for the stored element codes.

Both maps are nearest roundings onto the same finite values, so they agree away from the
midpoints of adjacent values and beyond the ends (`Profile.codec_round_eq_of_nearest`). At each
midpoint the codec's rule (the even code) and the real rule (the even significand or integer)
give the same value, which the kernel checks on the word list (`Profile.midpointsAgree`).
-/
theorem Profile.codec_round_eq_real (profile : Profile) (q : ℚ) :
    (((profile.codec .saturate).rounding.round q : ℚ) : ℝ) = profile.real.round (q : ℝ) := by
  cases hfmt : profile.floatFormat? with
  | some fmt =>
    have hreal : profile.real = Block.Rounding.saturating fmt := by
      cases profile <;>
        simp only [Profile.floatFormat?, Option.some.injEq, reduceCtorEq] at hfmt <;>
        subst hfmt <;> rfl
    rw [hreal]
    exact profile.codec_round_eq_saturating hfmt q
  | none =>
    obtain rfl : profile = .int8 := by
      cases profile <;> first | rfl | simp [Profile.floatFormat?] at hfmt
    rw [Profile.int8_codec_round_eq_fixedRat q]
    have h := Block.Rounding.fixed_round_ratCast 6 (-2) (127 / 64) q
    have hlo : ((-2 : ℚ) : ℝ) = -2 := by norm_num
    have hhi : ((127 / 64 : ℚ) : ℝ) = 127 / 64 := by norm_num
    rw [hlo, hhi] at h
    exact h.symm

/--
Stored elements are real roundings. In any block format whose elements round as the codec of a
profile with SAT conversion, the stored value of a position is the real rounding `profile.real`
of the input in units of the position's stored total scale. This holds for every level structure,
scale format and selection policy, with no premise on the scale.
-/
theorem Profile.value_quantize_eq_real (profile : Profile) (F : Block.CodedFormat ι γ)
    (hF : F.element.rounding = (profile.codec .saturate).rounding)
    (selection : Block.Policy ι γ) (x : ι → SignedRat) (i : ι) :
    (((F.quantize selection x).value i : ℚ) : ℝ) =
      (profile.real.scaled (((F.quantize selection x).scale i : ℚ) : ℝ)).round
        (((x i).value : ℚ) : ℝ) := by
  have helement : (F.toFormat selection).element i = (profile.codec .saturate).rounding := hF
  rw [Block.CodedFormat.value_quantize, Block.Format.reconstruct_eq, helement,
    Block.CodedFormat.scale_quantize, Block.Rounding.scaled_round, Block.Rounding.scaled_round]
  push_cast
  rw [← Rat.cast_div, profile.codec_round_eq_real]

end FloatLib.Floats.Formats.OCP.MX.Standard
