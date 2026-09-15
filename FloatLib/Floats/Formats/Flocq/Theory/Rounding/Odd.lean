/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Order

/-!
# Round to Odd

For an inexact real input, `oddRound` selects the odd member of the two adjacent integers.
Exact integers are unchanged.  Applied to a binary scaled mantissa, this is the usual round-to-odd
or jamming rule: discarded information is recorded by setting the least-significant retained bit.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Preserve integers; otherwise select the odd integer among `floor x` and `floor x + 1`. -/
noncomputable def oddRound (x : ℝ) : ℤ :=
  let f := ⌊x⌋
  if x = (f : ℝ) then f else if Odd f then f else f + 1

/-- Round-to-odd always selects one of the two adjacent integers. -/
theorem oddRound_bounds (x : ℝ) :
    ⌊x⌋ ≤ oddRound x ∧ oddRound x ≤ ⌊x⌋ + 1 := by
  simp only [oddRound]
  split_ifs <;> simp

/-- Exact integers are fixed by round-to-odd. -/
@[simp] theorem oddRound_intCast (n : ℤ) : oddRound (n : ℝ) = n := by
  simp [oddRound]

/-- An inexact input receives an odd integer result. -/
theorem oddRound_odd_of_inexact {x : ℝ} (hx : x ≠ (⌊x⌋ : ℝ)) :
    Odd (oddRound x) := by
  simp only [oddRound, hx, ite_false]
  by_cases hodd : Odd ⌊x⌋
  · simp [hodd]
  · rw [ite_eq_right hodd]
    exact odd_add_one.mpr (Int.not_odd_iff_even.mp hodd)

/-- Round-to-odd is monotone and fixes every integer. -/
instance oddRoundValid : ValidRnd oddRound where
  id := oddRound_intCast
  monotone := by
    intro x y hxy
    have hfloor : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy
    rcases hfloor.eq_or_lt with hfloorEq | hfloorLt
    · by_cases hxInt : x = (⌊x⌋ : ℝ)
      · rw [hxInt, oddRound_intCast]
        rw [hfloorEq]
        exact (oddRound_bounds y).1
      · have hyInt : y ≠ (⌊y⌋ : ℝ) := by
          intro hy
          have hxfloor : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
          have hxyFloor : x ≤ (⌊x⌋ : ℝ) := by simpa [hfloorEq] using hxy.trans_eq hy
          exact hxInt (le_antisymm hxyFloor hxfloor)
        have hxIntY : x ≠ (⌊y⌋ : ℝ) := by simpa [← hfloorEq] using hxInt
        simp only [oddRound, hxIntY, hyInt, ite_false, hfloorEq]
        exact le_rfl
    · exact (oddRound_bounds x).2.trans
        ((Int.add_one_le_iff.mpr hfloorLt).trans (oddRound_bounds y).1)

/-- An input below an even integer rounds to an integer strictly below it. -/
theorem oddRound_lt_even {x : ℝ} {n : ℤ} (hxn : x < (n : ℝ)) (hn : Even n) :
    oddRound x < n := by
  have hle : oddRound x ≤ n := by
    have hmono := ValidRnd.monotone (rnd := oddRound) x (n : ℝ) hxn.le
    simpa using hmono
  apply lt_of_le_of_ne hle
  intro heq
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have hround : oddRound x = ⌊x⌋ := by
      unfold oddRound
      rw [ite_eq_left hx]
    have : x = (n : ℝ) := by rw [hx, ← hround, heq]
    exact hxn.ne this
  · have hodd : Odd n := by simpa [heq] using oddRound_odd_of_inexact hx
    exact (Int.not_even_iff_odd.mpr hodd) hn

/-- An input above an even integer rounds to an integer strictly above it. -/
theorem even_lt_oddRound {x : ℝ} {n : ℤ} (hnx : (n : ℝ) < x) (hn : Even n) :
    n < oddRound x := by
  have hle : n ≤ oddRound x := by
    have hmono := ValidRnd.monotone (rnd := oddRound) (n : ℝ) x hnx.le
    simpa using hmono
  apply lt_of_le_of_ne hle
  intro heq
  by_cases hx : x = (⌊x⌋ : ℝ)
  · have hround : oddRound x = ⌊x⌋ := by
      unfold oddRound
      rw [ite_eq_left hx]
    have : (n : ℝ) = x := by rw [hx, ← hround, ← heq]
    exact hnx.ne this
  · have hodd : Odd n := by simpa [← heq] using oddRound_odd_of_inexact hx
    exact (Int.not_even_iff_odd.mpr hodd) hn

/--
Round-to-odd with at least two extra binary digits prevents nearest-even double rounding on the
integer grid.  `roundAtScale_nearestEven_after_odd_binary_extra` transports this to any fixed grid;
no floating-point (exponent-dependent) version is proved in this library.
-/
theorem nearestEven_roundOdd_binary_extra (extra : ℕ) (x : ℝ) :
    nearestEven
        ((oddRound (x * (2 : ℝ) ^ (extra + 2)) : ℝ) /
          (2 : ℝ) ^ (extra + 2)) =
      nearestEven x := by
  set n : ℤ := ⌊x⌋ with hn
  set K : ℤ := (2 : ℤ) ^ (extra + 2) with hK
  set H : ℤ := (2 : ℤ) ^ (extra + 1) with hH
  have hKtwo : K = 2 * H := by
    rw [hK, hH, pow_succ]
    ring
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    rw [hK]
    positivity
  have hKEven : Even K := ⟨H, by rw [hKtwo]; ring⟩
  have hKcast : (2 : ℝ) ^ (extra + 2) = (K : ℝ) := by
    rw [hK]
    push_cast
    rfl
  rw [hKcast]
  set z : ℝ := x * (K : ℝ) with hz
  set a : ℤ := oddRound z with ha
  set y : ℝ := (a : ℝ) / (K : ℝ) with hy
  set M : ℤ := n * K + H with hM
  have hMEven : Even M := ⟨n * H + (2 : ℤ) ^ extra, by rw [hM, hKtwo, hH, pow_succ]; ring⟩
  have haLower : n * K ≤ a := by
    have hmono := ValidRnd.monotone (rnd := oddRound) ((n * K : ℤ) : ℝ) z
      (by push_cast; exact mul_le_mul_of_nonneg_right (Int.floor_le x) hKpos.le)
    rwa [oddRound_intCast] at hmono
  have haUpper : a < (n + 1) * K :=
    oddRound_lt_even (by push_cast; nlinarith [Int.lt_floor_add_one x]) (hKEven.mul_left _)
  have hyFloor : ⌊y⌋ = n := by
    rw [Int.floor_eq_iff, le_div_iff₀ hKpos, div_lt_iff₀ hKpos]
    exact ⟨by exact_mod_cast haLower, by exact_mod_cast haUpper⟩
  have hK0 : (K : ℝ) ≠ 0 := hKpos.ne'
  have hzM : z - (M : ℝ) = (K : ℝ) * (x - n - 1 / 2) := by
    rw [hz, hM, hKtwo]
    push_cast
    ring
  have hyM : y - n - 1 / 2 = ((a : ℝ) - M) / (K : ℝ) := by
    rw [hy, eq_div_iff hK0]
    field_simp
    rw [hM, hKtwo]
    push_cast
    ring
  have hyLt : y - n < 1 / 2 ↔ a < M := by
    rw [← sub_neg, hyM, div_lt_iff₀ hKpos, zero_mul, sub_neg, Int.cast_lt]
  have hyGt : 1 / 2 < y - n ↔ M < a := by
    rw [← sub_pos, hyM, lt_div_iff₀ hKpos, zero_mul, sub_pos, Int.cast_lt]
  have hzLt : x - n < 1 / 2 → a < M := fun h =>
    oddRound_lt_even (by nlinarith) hMEven
  have hzGt : 1 / 2 < x - n → M < a := fun h =>
    even_lt_oddRound (by nlinarith) hMEven
  have hzGe : 1 / 2 ≤ x - n → M ≤ a := fun h => by
    have hmono := ValidRnd.monotone (rnd := oddRound) (M : ℝ) z (by nlinarith)
    rwa [oddRound_intCast] at hmono
  have hzLe : x - n ≤ 1 / 2 → a ≤ M := fun h => by
    have hmono := ValidRnd.monotone (rnd := oddRound) z (M : ℝ) (by nlinarith)
    rwa [oddRound_intCast] at hmono
  refine nearestEven_congr (hyFloor.trans hn) ?_ ?_
  · rw [hyFloor, ← hn, hyLt]
    exact ⟨fun h => not_le.1 fun h' => absurd (hzGe h') (not_le.2 h), hzLt⟩
  · rw [hyFloor, ← hn, gt_iff_lt, gt_iff_lt, hyGt]
    exact ⟨fun h => not_le.1 fun h' => absurd (hzLe h') (not_le.2 h), hzGt⟩

/--
Round-to-odd on a finer binary grid prevents nearest-even double rounding on a coarser grid.

The coarse grid has positive spacing `step`; the intermediate grid is finer by `extra + 2` binary
digits. Both grids are fixed, so the theorem applies to fixed-point and affine-quantization grids.
It does not cover floating-point formats, whose spacing depends on the exponent of the value.
-/
theorem roundAtScale_nearestEven_after_odd_binary_extra
    (extra : ℕ) (step x : ℝ) (hstep : 0 < step) :
    roundAtScale nearestEven step hstep
        (roundAtScale oddRound
          (step / (2 : ℝ) ^ (extra + 2)) (div_pos hstep (by positivity)) x) =
      roundAtScale nearestEven step hstep x := by
  let K : ℝ := (2 : ℝ) ^ (extra + 2)
  have hK : K ≠ 0 := by
    dsimp [K]
    positivity
  have hinput : x / (step / K) = (x / step) * K := by
    field_simp [ne_of_gt hstep]
  have hnormalize :
      (oddRound (x / (step / K)) : ℝ) * (step / K) / step =
        (oddRound ((x / step) * K) : ℝ) / K := by
    rw [hinput]
    field_simp [ne_of_gt hstep]
  unfold roundAtScale
  rw [show (2 : ℝ) ^ (extra + 2) = K by rfl]
  rw [hnormalize, nearestEven_roundOdd_binary_extra extra (x / step)]

/-- If `x` is not representable, round-to-odd selects an odd scaled integer mantissa. -/
theorem oddRound_scaled_mantissa_odd_of_not_generic
    {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp] {x : ℝ}
    (hx : ¬genericFormat β fexp x) :
    Odd (oddRound (scaledMantissa β fexp x)) := by
  apply oddRound_odd_of_inexact
  intro hs
  apply hx
  apply generic_format_of_scaled_mantissa_int
    (n := ⌊scaledMantissa β fexp x⌋)
  exact hs

/-- Round-to-odd produces a value in the selected generic format. -/
theorem generic_format_round_odd
    {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp] (x : ℝ) :
    genericFormat β fexp
      (round (β := β) (fexp := fexp) oddRound x) :=
  generic_format_round oddRound x

/--
Semantic round-to-odd specification.  An exact input is unchanged.  An inexact result is a
directed neighbor and has an odd integer mantissa at an explicit radix exponent.
-/
def RoundOddPoint (β : Numerics.Radix) (F : ℝ → Prop) (x f : ℝ) : Prop :=
  F f ∧
    (f = x ∨
      ((RoundDownPoint F x f ∨ RoundUpPoint F x f) ∧
        ∃ m : ℤ, ∃ e : ℤ, f = (m : ℝ) * bpow β e ∧ Odd m))

/-- Generic rounding with `oddRound` satisfies the round-to-odd point specification. -/
theorem round_odd_point
    {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp] (x : ℝ) :
    RoundOddPoint β (genericFormat β fexp) x
      (round (β := β) (fexp := fexp) oddRound x) := by
  refine ⟨generic_format_round_odd x, ?_⟩
  by_cases hx : genericFormat β fexp x
  · exact Or.inl (round_preserves_generic oddRound x hx)
  · right
    constructor
    · rcases round_eq_floor_or_ceil
        (β := β) (fexp := fexp) oddRound x with hfloor | hceil
      · exact Or.inl (by simpa [hfloor] using
          (round_floor_point (β := β) (fexp := fexp) x))
      · exact Or.inr (by simpa [hceil] using
          (round_ceil_point (β := β) (fexp := fexp) x))
    · refine ⟨oddRound (scaledMantissa β fexp x),
        cexp β fexp x, rfl, ?_⟩
      exact oddRound_scaled_mantissa_odd_of_not_generic hx

end FloatLib.Floats.Formats.Flocq
