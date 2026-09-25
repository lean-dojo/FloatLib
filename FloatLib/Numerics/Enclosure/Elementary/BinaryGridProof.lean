/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime
public import FloatLib.Numerics.Enclosure.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Interval.BinaryGridProof

/-!
# Soundness of binary-grid exponential and logarithm enclosures

Rounded Horner steps and rectangular splitting contain the exponential and odd logarithm Taylor
polynomials. Rounded powers and exact scalar factors enclose their remainder bounds. Mathlib's real
estimates therefore apply at every grid precision, including zero.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.BinaryGrid

open Interval.BinaryGrid

/-- Decoding the final grid endpoints preserves real containment. -/
theorem contains_toRationalInterval (precision : Nat) (I : Interval Int) (x : ℝ) :
    (toRationalInterval precision I).Contains x ↔
      I.ContainsReal (decode precision) x := by
  simp [toRationalInterval, RationalInterval.Contains]

private theorem value_scaleRat_bounds (precision : Nat) (z : Int) (factor : ℚ) :
    value precision (divBounds (z * factor.num) factor.den).lo ≤
        (factor : ℝ) * value precision z ∧
      (factor : ℝ) * value precision z ≤
        value precision (divBounds (z * factor.num) factor.den).hi := by
  have hs : (0 : ℝ) ≤ scale precision := by exact_mod_cast (scale_pos precision).le
  have h := divBounds_bounds (α := ℝ) (z * factor.num) factor.den
    (by exact_mod_cast factor.den_nz)
  simp only [Int.cast_natCast] at h
  have hfactor : (factor.num : ℝ) / factor.den = (factor : ℝ) := by
    exact_mod_cast factor.num_div_den
  have hq : (((z * factor.num : Int) : ℝ) / factor.den) / (scale precision : ℝ) =
      (factor : ℝ) * value precision z := by
    rw [← hfactor]
    simp only [Int.cast_mul, value]
    ring
  constructor
  · have hl := div_le_div_of_nonneg_right h.1 hs
    rw [hq] at hl
    exact hl
  · have hh := div_le_div_of_nonneg_right h.2 hs
    rw [hq] at hh
    exact hh

/-- Scalar rounding encloses the exact rational multiple of every real input member. -/
theorem containsReal_scaleRat (precision : Nat) {I : Interval Int} {x : ℝ}
    (hx : I.ContainsReal (decode precision) x) (factor : ℚ) :
    (scaleRat I factor).ContainsReal (decode precision) ((factor : ℝ) * x) := by
  rw [containsReal_iff] at hx ⊢
  have hlo := value_scaleRat_bounds precision I.lo factor
  have hhi := value_scaleRat_bounds precision I.hi factor
  by_cases hfactor : 0 ≤ factor
  · have hreal : (0 : ℝ) ≤ factor := by exact_mod_cast hfactor
    simp only [scaleRat, hfactor, ↓reduceIte]
    exact ⟨hlo.1.trans (mul_le_mul_of_nonneg_left hx.1 hreal),
      (mul_le_mul_of_nonneg_left hx.2 hreal).trans hhi.2⟩
  · have hreal : (factor : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hfactor
    simp only [scaleRat, hfactor, ↓reduceIte]
    exact ⟨hhi.1.trans (mul_le_mul_of_nonpos_left hx.2 hreal),
      (mul_le_mul_of_nonpos_left hx.1 hreal).trans hlo.2⟩

/-- Natural scalar division rounds outward without requiring a grid divisor interval. -/
theorem containsReal_divideNat (precision : Nat) {I : Interval Int} {x : ℝ}
    (hx : I.ContainsReal (decode precision) x) (n : Nat) :
    (divideNat I n).ContainsReal (decode precision) (x / n) := by
  simpa [divideNat, div_eq_mul_inv, mul_comm] using
    containsReal_scaleRat precision hx (1 / (n : ℚ))

/-- Midpoint and radius enclosures turn an absolute-error estimate into grid containment. -/
theorem containsReal_around (precision : Nat) {midpoint radius : Interval Int} {m r x : ℝ}
    (hm : midpoint.ContainsReal (decode precision) m)
    (hr : radius.ContainsReal (decode precision) r) (herror : |x - m| ≤ r) :
    (around midpoint radius).ContainsReal (decode precision) x := by
  rw [containsReal_iff] at hm hr ⊢
  simp only [around, value_sub, value_add]
  rcases abs_le.mp herror with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- Each rounded exponential Horner step contains the corresponding exact polynomial tail. -/
theorem containsReal_expHorner (precision : Nat) {X : Interval Int} {x : ℚ}
    (hx : X.ContainsReal (decode precision) (x : ℝ)) (start n : Nat) :
    (expHorner precision X start n).ContainsReal (decode precision)
      (Taylor.horner (Taylor.expStep x) start n 0 : ℝ) := by
  induction n generalizing start with
  | zero => simp [expHorner, Taylor.horner, Interval.point]
  | succ n ih =>
    have hone : (Interval.point (scale precision)).ContainsReal (decode precision) (1 : ℝ) := by
      simp [Interval.point]
    have h := containsReal_add precision hone
      (containsReal_divideNat precision
        (containsReal_mul precision hx (ih (start + 1))) (start + 1))
    simpa [expHorner, Taylor.horner, Taylor.eval_expStep, div_mul_eq_mul_div] using h

/-- Rounded odd Horner steps enclose the corresponding tail of the logarithm polynomial. -/
theorem containsReal_logOddHorner (precision : Nat) {X Q : Interval Int} {x : ℝ}
    (hx : X.ContainsReal (decode precision) x)
    (hq : Q.ContainsReal (decode precision) (x ^ 2)) (start n : Nat) :
    (logOddHorner precision X Q start n).ContainsReal (decode precision)
      (∑ i ∈ Finset.range n, x ^ (2 * i + 1) / ((2 * (start + i) + 1 : Nat) : ℝ)) := by
  induction n generalizing start with
  | zero => simp [logOddHorner, Interval.point]
  | succ n ih =>
    have h := containsReal_add precision (containsReal_divideNat precision hx (2 * start + 1))
      (containsReal_mul precision hq (ih (start + 1)))
    rw [logOddHorner]
    convert h using 1
    rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, pow_one]
    rw [Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_div_assoc]
    congr 1
    · simp only [Nat.mul_add, Nat.mul_one, pow_add]
      ring
    · congr 1
      omega

/-- The rounded exponential radius contains the original rational Taylor remainder bound. -/
theorem containsReal_expRadius (precision : Nat) {X : Interval Int} {x : ℚ}
    (hx : X.ContainsReal (decode precision) (x : ℝ)) (n : Nat) :
    (expRadius precision X n).ContainsReal (decode precision) (Enclosure.expRadius x n : ℝ) := by
  have h := containsReal_scaleRat precision
    (containsReal_pow precision (containsReal_abs precision hx) n)
    (((n + 1 : Nat) : ℚ) / ((n.factorial : ℚ) * n))
  simpa [expRadius, Enclosure.expRadius, mul_div_assoc, mul_comm] using h

/-- The original exponential Taylor estimate remains valid after outward grid evaluation. -/
theorem containsReal_expSmall (x : ℚ) (degree precision : Nat) (hx : |x| ≤ 1) :
    (expSmall x degree precision).ContainsReal (decode precision) (Real.exp (x : ℝ)) := by
  have hgrid := containsReal_enclose precision x
  have hpoly :
      (expHorner precision (enclose precision x) 0 (degree + 1)).ContainsReal (decode precision)
        (Enclosure.expTaylor x (degree + 1) : ℝ) := by
    simpa [Taylor.horner_expStep, Nat.one_ascFactorial, Enclosure.expTaylor] using
      containsReal_expHorner precision hgrid 0 (degree + 1)
  exact containsReal_around precision hpoly (containsReal_expRadius precision hgrid (degree + 1))
    (Enclosure.abs_exp_sub_expTaylor_le x degree hx)

/-- Rounded repeated squaring contains the matching power of every real input member. -/
theorem containsReal_squareRepeat (precision : Nat) {I : Interval Int} {x : ℝ}
    (hx : I.ContainsReal (decode precision) x) (n : Nat) :
    (squareRepeat precision I n).ContainsReal (decode precision) (x ^ (2 ^ n)) := by
  induction n with
  | zero => simpa [squareRepeat] using hx
  | succ n ih =>
    simpa only [squareRepeat, pow_succ (2 : Nat) n, pow_mul] using containsReal_square precision ih

private theorem abs_div_expScale_add_lt_one (x : ℚ) (extra : Nat) :
    |x / (2 : ℚ) ^ (Enclosure.expScale x + extra)| < 1 := by
  rw [pow_add, ← div_div, abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ extra)]
  exact (div_lt_one (by positivity)).mpr
    ((Enclosure.abs_div_expScale_lt_one x).trans_le (one_le_pow₀ (by norm_num)))

private theorem exp_div_pow_two_pow (x : ℚ) (n : Nat) :
    Real.exp ((x / 2 ^ n : ℚ) : ℝ) ^ (2 ^ n) = Real.exp (x : ℝ) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- Extra range reduction and its compensating grid bits preserve exponential containment. -/
theorem contains_exp (x : ℚ) (degree precision : Nat) :
    (exp x degree precision).Contains (Real.exp (x : ℝ)) := by
  let extra := expExtraScale x degree precision
  have hsmall := containsReal_expSmall (x / 2 ^ (Enclosure.expScale x + extra)) degree
    (precision + extra) (abs_div_expScale_add_lt_one x extra).le
  have h := containsReal_squareRepeat (precision + extra) hsmall (Enclosure.expScale x + extra)
  simpa only [exp, contains_toRationalInterval, exp_div_pow_two_pow] using h

namespace LogPolynomial

/-- The table extension adds exactly its requested powers. -/
theorem size_powerTableAux (precision : Nat) (Q : Interval Int) (n : Nat)
    (current : Interval Int) (powers : Array (Interval Int)) :
    (powerTableAux precision Q n current powers).size = powers.size + n + 1 := by
  induction n generalizing current powers with
  | zero => simp [powerTableAux]
  | succ n ih => simp [powerTableAux, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A power table includes the zeroth power and its requested final power. -/
theorem size_powerTable (precision : Nat) (Q : Interval Int) (n : Nat) :
    (powerTable precision Q n).size = n + 1 := by
  simp [powerTable, size_powerTableAux]

private theorem containsReal_push (precision : Nat) {powers : Array (Interval Int)}
    {current : Interval Int} {q : ℝ}
    (hpowers : ∀ (i : Nat) (hi : i < powers.size),
      powers[i].ContainsReal (decode precision) (q ^ i))
    (hcurrent : current.ContainsReal (decode precision) (q ^ powers.size)) :
    ∀ (i : Nat) (hi : i < (powers.push current).size),
      (powers.push current)[i].ContainsReal (decode precision) (q ^ i) := by
  intro i hi
  by_cases hlt : i < powers.size
  · simpa only [Array.getElem_push_lt hlt] using hpowers i hlt
  · have heq : i = powers.size := by
      simp only [Array.size_push] at hi
      omega
    subst i
    simpa only [Array.getElem_push_eq] using hcurrent

/-- Extending a table preserves containment of each power, including the appended powers. -/
theorem containsReal_powerTableAux (precision : Nat) {Q : Interval Int} {q : ℝ}
    (hq : Q.ContainsReal (decode precision) q) (n : Nat)
    (current : Interval Int) (powers : Array (Interval Int))
    (hpowers : ∀ (i : Nat) (hi : i < powers.size),
      powers[i].ContainsReal (decode precision) (q ^ i))
    (hcurrent : current.ContainsReal (decode precision) (q ^ powers.size)) :
    ∀ (i : Nat) (hi : i < (powerTableAux precision Q n current powers).size),
      (powerTableAux precision Q n current powers)[i].ContainsReal (decode precision)
        (q ^ i) := by
  induction n generalizing current powers with
  | zero => exact containsReal_push precision hpowers hcurrent
  | succ n ih =>
    apply ih _ _ (containsReal_push precision hpowers hcurrent)
    simpa only [Array.size_push, pow_succ] using
      containsReal_mul precision hcurrent hq

/-- Every stored interval encloses its real power, at every grid precision. -/
theorem containsReal_powerTable (precision : Nat) {Q : Interval Int} {q : ℝ}
    (hq : Q.ContainsReal (decode precision) q) (n i : Nat) (hi : i ≤ n) :
    ((powerTable precision Q n)[i]'(by rw [size_powerTable]; omega)).ContainsReal
      (decode precision) (q ^ i) := by
  apply containsReal_powerTableAux precision hq
  · intro i hi
    simp at hi
  · simp [Interval.point]

/-- The even-power sum before multiplication by the odd logarithm argument. -/
noncomputable def evenSum (q : ℝ) (start n : Nat) : ℝ :=
  ∑ i ∈ Finset.range n, q ^ i / ((2 * (start + i) + 1 : Nat) : ℝ)

/-- Splitting a range factors the first omitted power from the remaining terms. -/
theorem evenSum_add (q : ℝ) (start a b : Nat) :
    evenSum q start (a + b) =
      evenSum q start a + q ^ a * evenSum q (start + a) b := by
  simp only [evenSum, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add, ← mul_div_assoc]
  congr 2
  omega

/-- A block accumulator contains the exact partial sum plus its incoming real value. -/
theorem containsReal_blockSumAux (precision : Nat) {powers : Array (Interval Int)} {q : ℝ}
    (hpowers : ∀ (i : Nat) (hi : i < powers.size),
      powers[i].ContainsReal (decode precision) (q ^ i))
    (start n : Nat) (hn : n ≤ powers.size) (total : Interval Int) {a : ℝ}
    (htotal : total.ContainsReal (decode precision) a) :
    (blockSumAux powers start n total).ContainsReal (decode precision)
      (evenSum q start n + a) := by
  induction n generalizing total a with
  | zero => simpa [blockSumAux, evenSum] using htotal
  | succ n ih =>
    have hlt : n < powers.size := by omega
    have hpower : (powers[n]?.getD (Interval.point 0)).ContainsReal
        (decode precision) (q ^ n) := by
      simpa only [getElem?_pos powers n hlt, Option.getD_some] using hpowers n hlt
    have hterm := containsReal_divideNat precision hpower (2 * (start + n) + 1)
    have hsum := ih (by omega) _ (containsReal_add precision hterm htotal)
    simpa only [blockSumAux, evenSum, Finset.sum_range_succ, add_assoc] using hsum

/-- Each scalar block encloses the corresponding even-power polynomial. -/
theorem containsReal_blockSum (precision : Nat) {powers : Array (Interval Int)} {q : ℝ}
    (hpowers : ∀ (i : Nat) (hi : i < powers.size),
      powers[i].ContainsReal (decode precision) (q ^ i))
    (start n : Nat) (hn : n ≤ powers.size) :
    (blockSum powers start n).ContainsReal (decode precision) (evenSum q start n) := by
  simpa only [blockSum, add_zero] using containsReal_blockSumAux precision hpowers start n hn
    (Interval.point 0) (a := 0) (by simp [Interval.point])

/-- Block Horner evaluation encloses a full prefix and its appropriately shifted tail. -/
theorem containsReal_blockHorner (precision : Nat) {powers : Array (Interval Int)} {q : ℝ}
    (hpowers : ∀ (i : Nat) (hi : i < powers.size),
      powers[i].ContainsReal (decode precision) (q ^ i))
    {stride : Interval Int} (start blockSize blocks : Nat)
    (hstride : stride.ContainsReal (decode precision) (q ^ blockSize))
    (hsize : blockSize ≤ powers.size)
    (tail : Interval Int) {a : ℝ} (htail : tail.ContainsReal (decode precision) a) :
    (blockHorner precision powers stride start blockSize blocks tail).ContainsReal
      (decode precision)
      (evenSum q start (blockSize * blocks) + q ^ (blockSize * blocks) * a) := by
  induction blocks generalizing tail a with
  | zero => simpa [blockHorner, Internal.reverseHorner, evenSum] using htail
  | succ blocks ih =>
    have hblock := containsReal_blockSum precision hpowers
      (start + blockSize * blocks) blockSize hsize
    have hnext := containsReal_add precision hblock (containsReal_mul precision hstride htail)
    have h := ih _ hnext
    have hvalue :
        evenSum q start (blockSize * blocks) +
            q ^ (blockSize * blocks) *
              (evenSum q (start + blockSize * blocks) blockSize + q ^ blockSize * a) =
          evenSum q start (blockSize * (blocks + 1)) +
            q ^ (blockSize * (blocks + 1)) * a := by
      rw [Nat.mul_succ, evenSum_add, pow_add]
      ring
    rw [hvalue] at h
    simpa only [blockHorner, Internal.reverseHorner, Nat.zero_add] using h

/-- Multiplying the even-power sum by its argument gives the reference odd polynomial. -/
theorem mul_evenSum_sq (x : ℝ) (start n : Nat) :
    x * evenSum (x ^ 2) start n =
      ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / ((2 * (start + i) + 1 : Nat) : ℝ) := by
  rw [evenSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_div_assoc, ← pow_mul, pow_add, pow_one, mul_comm x]

/-- Rectangular splitting encloses the same odd polynomial for every positive block size. -/
theorem containsReal_logOddRectangular (precision : Nat) {X Q : Interval Int} {x : ℝ}
    (hx : X.ContainsReal (decode precision) x)
    (hq : Q.ContainsReal (decode precision) (x ^ 2))
    (start n blockSize : Nat) (hblock : 0 < blockSize) :
    (logOddRectangular precision X Q start n blockSize).ContainsReal (decode precision)
      (∑ i ∈ Finset.range n, x ^ (2 * i + 1) / ((2 * (start + i) + 1 : Nat) : ℝ)) := by
  let powers := powerTable precision Q blockSize
  have hpowers : ∀ (i : Nat) (hi : i < powers.size),
      powers[i].ContainsReal (decode precision) ((x ^ 2) ^ i) := by
    intro i hi
    apply containsReal_powerTable precision hq
    simpa only [powers, size_powerTable, Nat.lt_succ_iff] using hi
  have hsize : blockSize < powers.size := by
    simp only [powers, size_powerTable, Nat.lt_succ_self]
  have hstride : (powers[blockSize]?.getD (Interval.point 0)).ContainsReal
      (decode precision) ((x ^ 2) ^ blockSize) := by
    simpa only [getElem?_pos powers blockSize hsize, Option.getD_some] using
      hpowers blockSize hsize
  have htail := containsReal_blockSum precision hpowers
    (start + blockSize * (n / blockSize)) (n % blockSize)
    ((Nat.mod_lt n hblock).le.trans hsize.le)
  have hpoly := containsReal_blockHorner precision hpowers start blockSize (n / blockSize)
    hstride hsize.le _ htail
  rw [← evenSum_add, Nat.div_add_mod] at hpoly
  simpa only [logOddRectangular, powers, mul_evenSum_sq] using
    containsReal_mul precision hx hpoly

end LogPolynomial

/-- Both logarithm evaluation strategies enclose the reference odd polynomial. -/
theorem containsReal_logOddPolynomial (precision : Nat) {X Q : Interval Int} {x : ℝ}
    (hx : X.ContainsReal (decode precision) x)
    (hq : Q.ContainsReal (decode precision) (x ^ 2)) (start n : Nat) :
    (logOddPolynomial precision X Q start n).ContainsReal (decode precision)
      (∑ i ∈ Finset.range n, x ^ (2 * i + 1) / ((2 * (start + i) + 1 : Nat) : ℝ)) := by
  dsimp only [logOddPolynomial]
  split
  · exact containsReal_logOddHorner precision hx hq start n
  · exact LogPolynomial.containsReal_logOddRectangular precision hx hq start n (max 1 n.sqrt)
      (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))

/-- The grid remainder encloses the odd logarithm series error bound. -/
theorem containsReal_logOddRadius (precision : Nat) {X Q : Interval Int} {x : ℚ}
    (hx : X.ContainsReal (decode precision) (x : ℝ))
    (hq : Q.ContainsReal (decode precision) ((x : ℝ) ^ 2)) (n : Nat) :
    (logOddRadius precision X Q x n).ContainsReal (decode precision)
      (|(x : ℝ)| ^ (2 * n + 1) / (1 - (x : ℝ) ^ 2)) := by
  have h := containsReal_scaleRat precision
    (containsReal_mul precision (containsReal_pow precision hq n)
      (containsReal_abs precision hx)) (1 / (1 - x ^ 2))
  have hpower : |(x : ℝ)| ^ (2 * n + 1) = ((x : ℝ) ^ 2) ^ n * |(x : ℝ)| := by
    rw [pow_add, pow_one, pow_mul, sq_abs]
  rw [hpower]
  simpa [logOddRadius, div_eq_mul_inv, mul_comm] using h

/-- The transformed grid series encloses the logarithm of every positive rational. -/
theorem containsReal_logSeries (x : ℚ) (degree precision : Nat) (hx : 0 < x) :
    (logSeries x degree precision).ContainsReal (decode precision) (Real.log (x : ℝ)) := by
  let t : ℚ := (x - 1) / (x + 1)
  have ht : |t| < 1 := Enclosure.abs_log_argument_lt_one x hx
  have hreal : |(t : ℝ)| < 1 := by exact_mod_cast ht
  have hgrid := containsReal_enclose precision t
  have hsquare := containsReal_square precision hgrid
  have hpoly := containsReal_logOddPolynomial precision hgrid hsquare 0 ((degree + 1) / 2)
  have hradius := containsReal_logOddRadius precision hgrid hsquare ((degree + 1) / 2)
  have herror := Real.sum_range_sub_log_div_le hreal ((degree + 1) / 2)
  have hidentity : Real.log ((1 + (t : ℝ)) / (1 - (t : ℝ))) = Real.log (x : ℝ) := by
    rw [Real.log_div (by linarith [(abs_lt.mp hreal).1])
      (by linarith [(abs_lt.mp hreal).2])]
    exact Enclosure.log_argument_identity x hx
  rw [hidentity] at herror
  simp only [Nat.zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hpoly
  have hhalf := containsReal_around precision hpoly hradius herror
  have h := containsReal_add precision hhalf hhalf
  have htwo : (1 / 2 : ℝ) * Real.log (x : ℝ) + 1 / 2 * Real.log (x : ℝ) =
      Real.log (x : ℝ) := by ring
  simpa only [logSeries, t, htwo] using h

/-- Binary reduction and the rounded multiple of `log 2` preserve logarithm containment. -/
theorem containsReal_logLarge (x : ℚ) (degree precision : Nat) (hx : 0 < x) :
    (logLarge x degree precision).ContainsReal (decode precision) (Real.log (x : ℝ)) := by
  dsimp only [logLarge]
  split
  · exact containsReal_logSeries x degree precision hx
  · have hfirst := containsReal_logSeries (x / 2 ^ Enclosure.logScale x) degree precision
      (by positivity)
    have hsecond := containsReal_scaleRat precision
      (containsReal_logSeries 2 degree precision (by norm_num)) (Enclosure.logScale x : ℚ)
    simpa only [Rat.cast_natCast, Rat.cast_ofNat, Enclosure.log_reduction_identity x hx]
      using containsReal_add precision hfirst hsecond

/-- Binary-grid logarithm evaluation encloses the exact logarithm at every precision. -/
theorem contains_log (x : ℚ) (degree precision : Nat) (hx : 0 < x) :
    (log x degree precision).Contains (Real.log (x : ℝ)) := by
  rw [log, contains_toRationalInterval]
  split
  · have h := containsReal_neg precision
      (containsReal_logLarge x⁻¹ degree precision (inv_pos.mpr hx))
    simpa only [Rat.cast_inv, Real.log_inv, neg_neg] using h
  · exact containsReal_logLarge x degree precision hx

end FloatLib.Numerics.Enclosure.BinaryGrid
