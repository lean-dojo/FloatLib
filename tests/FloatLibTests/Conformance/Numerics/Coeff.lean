/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Coeff.Trig
public import FloatLib.Numerics.Packed.Literal

/-!
# Bounds on cosine polynomials

The cosine polynomial `R(u) = ∑ k < 64, rₖ cos (k u)` has random integer coefficients below `2 ^ 71`
that decay like `1.08 ^ (-k)`, drawn by Python's `random` with seed `20261107`, and `r₀ = 0`. Its
`l1` norm is `13763340627163358185920`, while on a grid of 400,000 points `|R|` reaches only
`6.339045557498547e21`, so the `l1` bound is 2.17 times the supremum. Two sum-of-squares
certificates, the spectral factors of `kc ± 2 R` computed with python-flint and rounded to
integers, prove `|2 R(u)| ≤ kc` for every `u`, with `kc / 2` within `4e-7` of the grid maximum.
The generator is untrusted: the kernel checks the certificates, and a wrong one fails the check.

## Main statements

* `sup_check` runs the range checks of the half row and of the empty sine row and both
  sum-of-squares checks, in lanes of 88 bits: two reversals, two autocorrelations and four `l1`
  norms on rows of 127 lanes. The factors are real, so their imaginary parts have no lanes.
* `sup_bound` is the bound on the circle, `chebyshev_bound` the same bound for the Chebyshev series
  on `[0, 2]`, and `deriv_cos` the derivative, whose row `Packed.ramp` computes.
* `l1_bounds`, `deriv_bound` and `hilbert_bound` are the `l1` bounds on the row, its derivative and
  its Hilbert transform, each from one `absSum`, and `small_product` multiplies two packed rows.
* Negative control: a bound just below the grid maximum has no certificate, and the kernel refuses
  the factor for it.

## Implementation notes

Every check runs under `set_option maxHeartbeats` at about three times the heartbeats it uses, so
the build fails if its kernel cost grows. These tests apply the library theorems by hand, with
every lane width and headroom spelled out, which is what `interval` does for you; they pin down
the library API that the tactic sits on.

## References

* Bogdan Dumitrescu, *Positive Trigonometric Polynomials and Signal Processing Applications*,
  Springer (2007), <https://doi.org/10.1007/978-1-4020-5125-8>, for spectral factors.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Coeff

open FloatLib.Numerics.Packed FloatLib.Numerics.Coeff Finset

/-- The coefficients `r₀, …, r₆₃`. -/
packed_row half (width := 88) := [
    0, -430491109920098222080, -812977157858212184064, -1078465232642568749056,
    185595937206744678400, 1523155569046755475456, 725300208932234592256, 276610244891559788544,
    -689297766547476840448, -76786083024208904192, 1198871336240566239232, 1585542936572415180800,
    371544765327135342592, 394104797587720830976, 576178048841751527424, -89960052647525203968,
    -116764856590601355264, -791679692261974081536, -936533471956429045760, -155596014007412359168,
    144301690275665952768, -294094259174170951680, 21829155491952095232, 71245912093215973376,
    -87861405433996394496, 8223861110734295040, -9545657312892995584, 128780564315848589312,
    -113206089254673514496, 127556212085172764672, 23116437185859493888, -8998123946421433344,
    -8972878180595715072, 8479130724968088576, 56206179825484939264, 1288453561438275072,
    39165855252504657920, -92491132217139396608, 61032468390378283008, 90527646898716377088,
    -9267753684293277696, -25049560035554770944, 33429972648819052544, -2720593171062329344,
    196258760685254080, -2664816835638090752, -27072646679273488384, -34150546009544413184,
    -18433914187652270080, -17697684005156933632, 18040614978633793536, -38787129937742348288,
    6661985088270398464, -3792416395428142592, -11606091012866447360, 4279884653968055808,
    24770291342506274816, -8036166038911267840, -4432694122771114496, -20807697160174583808,
    11106899222109274112, -9443929466652792832, -5875900098008811520, 12636786792414212096]

/-- The spectral factor for `kc + 2 R`. -/
packed_row lower (width := 88) := [
    103881875708, -16349121435, -12907020749, -10787446655, 2871059982, 14349101938, 7549233100,
    6456247884, -196266884, 5537295321, 17520547787, 19620335907, 6839951854, 5277601575,
    4389902549, -3332429203, -3619432975, -8904336245, -9227144798, -1503350193, 1106755744,
    -2607254703, 135449970, 549535394, -960159086, -175310527, -127459628, 920783151, -1403271589,
    774571781, 287177, -231766171, -104632698, 66193634, 486573477, 197216126, 601534241,
    -544911501, 848213524, 991539548, 42356262, -93235181, 361020815, -52783697, -57232029,
    -131615974, -302346137, -320577271, -166523441, -176087599, 114213148, -379036574, 74034543,
    -16751647, -69633230, 49451895, 193645188, -106760068, -85976930, -201638177, 102045762,
    -81685128, -37418455, 121645732]

/-- The spectral factor for `kc - 2 R`. -/
packed_row upper (width := 88) := [
    -105693041482, 1782955761, -12990062904, -16478068840, 2223447913, 19106322093, 8958389658,
    -1113203762, -10126000383, 47306965, 12096182562, 12731569499, 296943399, 2393003085,
    6538457805, 1272348212, -529564542, -7766573507, -8276928532, -906010312, 1228569945,
    -3177077369, 232182950, 904853011, -435481812, 153333132, -535045230, 856395206, -701199237,
    1696530837, 194612839, -404962456, -316936393, 268730161, 841283421, -10250393, 50857237,
    -1020897084, 605499503, 895749745, -96213199, -297212910, 202200208, -57315093, 63113521,
    84819460, -227601532, -359556915, -230752558, -159589778, 199146624, -296875434, 63604659,
    -78475976, -144682145, 49386106, 239413269, -71258497, -19201162, -171562680, 91260588,
    -104950737, -53577111, 119561199]

set_option maxHeartbeats 1000 in
/-- The range checks of the half row and of the empty sine row, and the two sum-of-squares checks,
each with a real factor of 64 lanes. -/
theorem sup_check :
    guard 88 71 64 half = true ∧ guard 88 71 0 0 = true ∧
      sosCheck 88 71 37 64 64 0 1 12678095618596721917952 1
        (ofInt 88 (2 * 64 - 1) (shift 88 (64 - 64) (unfold 88 64 half)))
        (ofInt 88 (2 * 64 - 1) (shift 88 (64 - 0) (unfold 88 0 0 true))) lower 0 = true ∧
      sosCheck 88 71 37 64 64 0 (-1) 12678095618596721917952 1
        (ofInt 88 (2 * 64 - 1) (shift 88 (64 - 64) (unfold 88 64 half)))
        (ofInt 88 (2 * 64 - 1) (shift 88 (64 - 0) (unfold 88 0 0 true))) upper 0 = true := by
  decide +kernel

/-- The sharp two-sided bound on the circle, one side from each check. -/
theorem sup_bound (u : ℝ) :
    |2 * ∑ k ∈ range 64, (entry 88 k half : ℝ) * Real.cos (k * u)| ≤ 12678095618596721917952 := by
  obtain ⟨hA, hB, hlo, hhi⟩ := sup_check
  have h1 := trig_sosCheck hA hB (by norm_num) le_rfl (by norm_num) hlo u
  have h2 := trig_sosCheck hA hB (by norm_num) le_rfl (by norm_num) hhi u
  simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h1 h2
  rw [abs_le]
  push_cast at h1 h2 ⊢
  constructor <;> linarith

set_option maxHeartbeats 200 in
/-- The `l1` bound from one `absSum`, 2.17 times larger. -/
theorem l1_value : absSum 88 64 (toInt 88 64 half) = 13763340627163358185920 := by decide +kernel

/-- The same bound for the Chebyshev series in `x - 1` on `[0, 2]`. -/
theorem chebyshev_bound :
    ∀ x ∈ Set.Icc (0 : ℝ) 2,
      |2 * ∑ k ∈ range 64, (entry 88 k half : ℝ) * (Polynomial.Chebyshev.T ℝ k).eval (x - 1)| ≤
        12678095618596721917952 := by
  refine forall_Icc_of_cos fun u => ?_
  have h := sup_bound u
  rw [← chebyshev_cos] at h
  convert h using 6
  ring

set_option maxHeartbeats 2000 in
/-- The derivative of `R` is the sine polynomial of the row that `ramp` computes; lane `3` of that
row is `3 r₃`. -/
theorem deriv_cos (u : ℝ) :
    HasDerivAt (fun u => ∑ k ∈ range 64, 1 * entry 88 k half * Real.cos (k * u))
        (-∑ k ∈ range 64, 1 * entry 88 k (ofInt 88 64 (ramp 88 64 half)) * Real.sin (k * u)) u ∧
      entry 88 3 (ofInt 88 64 (ramp 88 64 half)) = 3 * entry 88 3 half := by
  refine ⟨hasDerivAt_cos_ramp sup_check.1 (by norm_num) 1 u, by decide +kernel⟩

/-- The `l1` bound on the unit circle from one `absSum`, for the Laurent polynomial of the row and
for the cosine polynomial. -/
theorem l1_bounds (u : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖laurent (entries 88 64 half) 0 z‖ ≤ 13763340627163358185920 ∧
      |∑ k ∈ range (entries 88 64 half).length,
          ((entries 88 64 half).getD k 0 : ℝ) * Real.cos (k * u)| ≤ 13763340627163358185920 := by
  have h1 := norm_laurent_le_absSum sup_check.1 (by norm_num) hz 0
  have h2 := abs_cos_sum_le (entries 88 64 half) u
  rw [← absSum_toInt sup_check.1 (by norm_num), l1_value] at h2
  rw [l1_value] at h1
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

set_option maxHeartbeats 4000 in
/-- The derivative row passes a range check, and its `absSum` bounds `|R'|` on the circle. -/
theorem deriv_bound (u : ℝ) :
    |∑ k ∈ range (entries 88 64 (ofInt 88 64 (ramp 88 64 half))).length,
        ((entries 88 64 (ofInt 88 64 (ramp 88 64 half))).getD k 0 : ℝ) * Real.sin (k * u)| ≤
      165650867296204044620544 := by
  have hg : guard 88 75 64 (ofInt 88 64 (ramp 88 64 half)) = true ∧
      absSum 88 64 (toInt 88 64 (ofInt 88 64 (ramp 88 64 half))) = 165650867296204044620544 := by
    decide +kernel
  have h := abs_sin_sum_le (entries 88 64 (ofInt 88 64 (ramp 88 64 half))) u
  rw [← absSum_toInt hg.1 (by norm_num), hg.2] at h
  exact_mod_cast h

/-- The Hilbert transform of `2 R` is the sine polynomial of the same row, so it obeys the same
`l1` bound. -/
theorem hilbert_bound (u : ℝ) :
    ‖hilbert (mirror (entries 88 64 half)) 63 (Complex.exp (u * Complex.I))‖ ≤
      2 * 13763340627163358185920 := by
  have h := hilbert_mirror (entries 88 64 half) u
  rw [length_entries] at h
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
  have h3 := abs_sin_sum_le (entries 88 64 half) u
  rw [← absSum_toInt sup_check.1 (by norm_num), l1_value, length_entries] at h3
  push_cast at h3 ⊢
  linarith

/-- The Hilbert transform of a sine row and the derivative of a sine polynomial, on the half row
`[5, 2, 1]`. -/
theorem small_hilbert_and_deriv (u : ℝ) :
    hilbert (mirror [5, 2, 1] true) 2 (Complex.exp (u * Complex.I)) =
        -Complex.I * ((2 * ∑ k ∈ range 3,
          ((([5, 2, 1] : List ℤ).set 0 0).getD k 0 : ℝ) * Real.cos (k * u) : ℝ) : ℂ) ∧
      HasDerivAt (fun u => ∑ k ∈ range 3, (([5, 2, 1] : List ℤ).getD k 0 : ℝ) * Real.sin (k * u))
        (∑ k ∈ range 3, k * (([5, 2, 1] : List ℤ).getD k 0 : ℝ) * Real.cos (k * u)) u :=
  ⟨hilbert_mirror_odd [5, 2, 1] u, hasDerivAt_sin_sum _ 3 u⟩

/-- `[1, -2, 3]` and `[4, -5]` in lanes of 16 bits. -/
packed_row small (width := 16) := [1, -2, 3]

/-- `[4, -5]` in lanes of 16 bits. -/
packed_row small' (width := 16) := [4, -5]

set_option maxHeartbeats 1000 in
/-- The Kronecker product of the two rows is the product of their Laurent polynomials, here
`(z⁻¹ - 2 + 3 z) (4 - 5 z)`. -/
theorem small_product {z : ℂ} (hz : z ≠ 0) :
    laurent (entries 16 4 (ofInt 16 4 (toInt 16 3 small * toInt 16 2 small'))) (1 + 0) z =
      laurent (entries 16 3 small) 1 z * laurent (entries 16 2 small') 0 z := by
  have hg : guard 16 2 3 small = true ∧ guard 16 3 2 small' = true := by decide +kernel
  exact laurent_entries_mul hg.1 hg.2 (by norm_num) (by norm_num) (by norm_num) hz 1 0

set_option maxHeartbeats 400 in
/-- A bound below the grid maximum of `-2 R` is false, so no certificate can pass for it: the
kernel refuses the factor `lower` at `12678091114997094547454`. -/
theorem below_sup_refused :
    sosCheck 88 71 37 64 64 0 1 12678091114997094547454 1
      (ofInt 88 (2 * 64 - 1) (shift 88 (64 - 64) (unfold 88 64 half)))
      (ofInt 88 (2 * 64 - 1) (shift 88 (64 - 0) (unfold 88 0 0 true))) lower 0 = false := by
  decide +kernel

end FloatLibTests.Conformance.Numerics.Coeff
