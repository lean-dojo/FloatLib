/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.Addition

/-!
# Carry and same-sign addition paths

`addCarry` handles a sum that carries into the next exponent. `addSame` handles a same-sign sum
whose exponent is retained. `addShort` selects by operand signs and each path falls back to the
preceding verified adder. The final addition and subtraction theorems cover every descriptor,
rounding direction and operand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Numerics.Kernel (bitLength bitLength_eq searchLength searchLength_eq)

/--
The carry path of addition, for two operands of one sign whose sum carries into the next
exponent: the sum of the two significands is halved, its low bit joins the remainder, and the
result takes the exponent field of the larger operand plus one. One comparison decides whether
the result stands: the signs agree, the sum carried, the format has no zero NaN, and the word
is at most the largest finite one. Every other case gives `fallback`.
-/
def addCarryWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b fallback : Nat) :
    Nat :=
  (fun ua ub =>
    (fun D =>
      (fun big small =>
        (fun hb hs =>
          (fun g ms =>
            (fun sh =>
              (fun M =>
                (fun q =>
                  (fun w =>
                    Bool.casesOn (motive := fun _ => Nat)
                      (Nat.ble
                        (Nat.add w
                          (Nat.mul
                            (Nat.add
                              (Nat.add (Nat.shiftRight (Nat.xor a b) (signPos fmt))
                                (Nat.sub 1 (Nat.shiftRight (Nat.shiftRight M fmt.fracWidth) 1)))
                              (negZeroNaN fmt))
                            (maxFiniteSucc fmt)))
                        (maxFinite fmt))
                      fallback
                      (Nat.add (Nat.sub a ua) w))
                    (Nat.add (Nat.shiftLeft (Nat.succ hb) fmt.fracWidth)
                      (Nat.add q
                        (roundUp mode (Nat.shiftRight a (signPos fmt)) q
                          (Nat.add (Nat.shiftLeft (Nat.sub M (Nat.shiftLeft q 1)) g)
                            (Nat.sub ms (Nat.shiftLeft sh g)))
                          (Nat.pow 2 (Nat.succ g))))))
                  (Nat.shiftRight M 1))
                (Nat.add (Nat.sub big (Nat.shiftLeft hb fmt.fracWidth)) sh))
              (Nat.shiftRight ms g))
            ((fun c => Nat.sub c (Nat.sub c (Nat.sub hb hs))) (Nat.add fmt.fracWidth 2))
            (Nat.sub small (Nat.shiftLeft hs fmt.fracWidth)))
          (Nat.sub (Nat.shiftRight big fmt.fracWidth) 1)
          (Nat.sub (Nat.shiftRight small fmt.fracWidth) 1))
        (Nat.add ub D) (Nat.sub ua D))
      (Nat.sub ua ub))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/--
The shortest path of addition, on the words themselves, for two operands of one sign whose sum
keeps the exponent of the larger one: the smaller significand is shifted by the exponent gap and
added to the exponent and fraction fields of the larger operand, and the rounding increment is
added to that word. One comparison decides whether the result stands: the exponent field did not
move past that of the larger operand (a sum of two subnormal numbers may reach the first normal
binade), the sum is not zero, the format has no zero NaN, and the word is at most the largest
finite one. Every other case gives `carry`. The result is meant for operands of one sign only
(`addSameWith_eq`).
-/
def addSameWith (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b carry : Nat) : Nat :=
  (fun ua ub =>
    (fun D =>
      (fun big small =>
        (fun hb hs =>
          (fun g ms =>
            (fun sh =>
              (fun w0 =>
                (fun w =>
                  Bool.casesOn (motive := fun _ => Nat)
                    (Nat.ble
                      (Nat.add w
                        (Nat.mul
                          (Nat.add
                            (Nat.add (Nat.sub (Nat.shiftRight w0 fmt.fracWidth) (Nat.succ hb))
                              (negZeroNaN fmt))
                            (Nat.sub 1 w0))
                          (maxFiniteSucc fmt)))
                      (maxFinite fmt))
                    carry
                    (Nat.add (Nat.sub a ua) w))
                  (Nat.add w0
                    (roundUpShift mode (Nat.shiftRight a (signPos fmt)) w0
                      (Nat.sub ms (Nat.shiftLeft sh g)) g)))
                (Nat.add big sh))
              (Nat.shiftRight ms g))
            (Nat.sub hb hs) (Nat.sub small (Nat.shiftLeft hs fmt.fracWidth)))
          (Nat.sub (Nat.shiftRight big fmt.fracWidth) 1)
          (Nat.sub (Nat.shiftRight small fmt.fracWidth) 1))
        (Nat.add ub D) (Nat.sub ua D))
      (Nat.sub ua ub))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/--
Selection by the signs of two encodings: `same` when the sign bits of `a` and `b` agree,
`different` otherwise. The two results are separate calls, so that the kernel instantiates the
code of one path only.
-/
def bySign (fmt : FloatFormat) (a b same different : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Nat.beq (Nat.shiftRight (Nat.xor a b) (signPos fmt)) 0) different same

/--
Encoding of the sum of the values encoded by `a` and `b`, rounded in the direction `mode`: the
carry path `addCarryWith`, and `addFast` in every case that leaves it (`addCarry_eq`).
-/
def addCarry (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  addCarryWith fmt mode a b (addFast fmt mode a b)

/--
Encoding of the sum of two values of one sign, rounded in the direction `mode`: the shortest
path `addSameWith`, and `addCarry` in every case that leaves it. On operands of one sign it is
`addFast` (`addSame_eq`).
-/
def addSame (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  addSameWith fmt mode a b (addCarry fmt mode a b)

/--
Encoding of the sum of the values encoded by `a` and `b`, rounded in the direction `mode`:
`addSame` for operands of one sign and `addFast` for operands of different signs
(`addShort_eq`).
-/
def addShort (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  bySign fmt a b (addSame fmt mode a b) (addFast fmt mode a b)

/-- Encoding of the difference rounded in the direction `mode`, through `addShort`. -/
def subShort (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  addShort fmt mode a (neg fmt b)

/--
`sumOrdered` on two operands of one sign in the lowest binade whose sum stays below the normal
range: the word is the sum of the two significands, which is exact.
-/
theorem sumOrdered_tiny (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sbig mb ms hs special : Nat) (hsum : mb + ms < 2 ^ fmt.fracWidth) (hpos : mb + ms ≠ 0) :
    sumOrdered fmt mode sbig 0 mb 0 ms hs 0 special = sbig * 2 ^ signPos fmt + (mb + ms) := by
  have hfw := fmt.fracWidth_pos
  unfold sumOrdered
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq',
    Nat.pow_eq, Nat.zero_sub, Nat.zero_mul, Nat.sub_zero, Nat.zero_add, Nat.shiftLeft_zero]
  have hu : (mb + ms) >>> (fmt.fracWidth - 1) ≤ 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    have hlt : mb + ms < 2 * 2 ^ (fmt.fracWidth - 1) := by
      have : 2 * 2 ^ (fmt.fracWidth - 1) = 2 ^ fmt.fracWidth := by
        rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hfw]
      omega
    exact Nat.le_of_lt_succ
      ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (fmt.fracWidth - 1))).2 hlt)
  have hk : 1 - (1 - (mb + ms) >>> (fmt.fracWidth - 1) >>> 1) +
      (mb + ms) >>> (fmt.fracWidth - 1) >>> 2 = 0 := by
    generalize (mb + ms) >>> (fmt.fracWidth - 1) = u at hu ⊢
    obtain rfl | rfl : u = 0 ∨ u = 1 := by omega
    · decide
    · decide
  rw [hk, Nat.mul_zero, show Nat.beq 0 0 = true from rfl]
  change packExact fmt mode sbig sbig (mb + ms) 0 (1 - (mb + ms)) special
    (bitLength (Nat.succ fmt.fracWidth) (mb + ms)) = _
  rw [show 1 - (mb + ms) = 0 by omega]
  have hbits : mb + ms < 2 ^ addBits fmt :=
    lt_of_lt_of_le hsum (Nat.pow_le_pow_right (by decide) (by unfold addBits; omega))
  have hlog : (mb + ms).log2 < fmt.fracWidth := (Nat.log2_lt hpos).2 hsum
  rw [packExact_eq_round fmt mode (addBits fmt) sbig sbig (mb + ms) 0 special special
    (lt_of_lt_of_le hsum (Nat.pow_le_pow_right (by decide) (by omega)))
    (by unfold addBits; omega)]
  unfold round
  rw [roundAt_def]
  unfold roundQuotient
  rw [bitLength_eq hbits, ite_eq_right hpos]
  simp only [pack_eq, Nat.add_eq, Nat.sub_eq, div_def, mod_def, Nat.pow_eq, Nat.shiftLeft_eq',
    Nat.add_zero, Nat.zero_add, ne_eq, not_true_eq_false, ite_false]
  rw [show (mb + ms).log2 + 1 - (fmt.fracWidth + 1) = 0 by omega]
  simp only [Nat.sub_zero, Nat.shiftLeft_zero, Nat.pow_zero, Nat.div_one, Nat.mod_one,
    Nat.zero_mul, Nat.zero_add]
  rw [roundUp_exact mode sbig _ 1, Nat.add_zero]
  have hfin : mb + ms ≤ maxFinite fmt := by
    have h := (le_maxFinite_iff fmt 0 (mb + ms) hsum).mpr (Or.inl fmt.maxFiniteExpField_pos)
    rwa [Nat.zero_mul, Nat.zero_add] at h
  rw [ite_eq_right hpos, ite_eq_left hfin]

/--
`sumOrdered` on two operands of one sign whose sum keeps the exponent of the larger one: the
word is the fields of the larger operand plus the shifted smaller significand and the rounding
increment, when that word is at most the largest finite one.
-/
theorem sumOrdered_short (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sbig mb hb ms hs special : Nat) (hms : ms < 2 ^ (fmt.fracWidth + 1))
    (hv : (mb + ms >>> (hb - hs)) >>> fmt.fracWidth = 1)
    (hle : hb * 2 ^ fmt.fracWidth + (mb + ms >>> (hb - hs) +
        roundUp mode sbig (mb + ms >>> (hb - hs)) (ms - (ms >>> (hb - hs)) <<< (hb - hs))
          (2 ^ (hb - hs))) ≤ maxFinite fmt) :
    sumOrdered fmt mode sbig 0 mb hb ms hs 0 special =
      sbig * 2 ^ signPos fmt + (hb * 2 ^ fmt.fracWidth + (mb + ms >>> (hb - hs) +
        roundUp mode sbig (mb + ms >>> (hb - hs)) (ms - (ms >>> (hb - hs)) <<< (hb - hs))
          (2 ^ (hb - hs)))) := by
  have hFpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hsplit := Nat.two_pow_succ fmt.fracWidth
  have hlow : 2 ^ fmt.fracWidth ≤ mb + ms >>> (hb - hs) := by
    by_contra hlt
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)] at hv
    omega
  have hremainder : ∀ k : Nat, ms - (ms >>> k) <<< k = ms % 2 ^ k := by
    intro k
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have := Nat.div_add_mod' ms (2 ^ k)
    omega
  unfold sumOrdered roundQuotient
  simp only [pack_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq',
    Nat.pow_eq, div_def, mod_def, Nat.zero_mul, Nat.sub_zero, Nat.zero_add]
  rw [hremainder] at hle ⊢
  generalize hd : hb - hs = d at hv hle hlow ⊢
  generalize hg : d - (d - addGap fmt) = g
  -- The quotient and the remainder of the aligned sum at the clamped gap are those at the gap.
  have hquot : (mb <<< g + ms) / 2 ^ g = mb + ms >>> d := by
    rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos g),
      Nat.add_comm, Nat.shiftRight_eq_div_pow]
    by_cases hclamp : d ≤ addGap fmt
    · have : g = d := by omega
      rw [this]
    · have hgG : g = addGap fmt := by omega
      have hbig : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ g :=
        Nat.pow_le_pow_right (by decide) (by rw [hgG]; unfold addGap; omega)
      have hbig' : 2 ^ (fmt.fracWidth + 1) ≤ 2 ^ d :=
        Nat.pow_le_pow_right (by decide) (by unfold addGap at hclamp; omega)
      rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  have hrem : (mb <<< g + ms) % 2 ^ g = ms % 2 ^ g := by
    rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.add_mul_mod_self_right]
  have hup : roundUp mode sbig (mb + ms >>> d) (ms % 2 ^ g) (2 ^ g) =
      roundUp mode sbig (mb + ms >>> d) (ms % 2 ^ d) (2 ^ d) := by
    by_cases hclamp : d ≤ addGap fmt
    · have : g = d := by omega
      rw [this]
    · have hgG : g = addGap fmt := by omega
      have hbig : 2 ^ (fmt.fracWidth + 2) ≤ 2 ^ g :=
        Nat.pow_le_pow_right (by decide) (by rw [hgG]; unfold addGap; omega)
      have hbig' : 2 ^ (fmt.fracWidth + 2) ≤ 2 ^ d :=
        Nat.pow_le_pow_right (by decide) (by unfold addGap at hclamp; omega)
      have hsplit2 : 2 ^ (fmt.fracWidth + 2) = 2 * 2 ^ (fmt.fracWidth + 1) := by
        rw [Nat.pow_succ]; omega
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact roundUp_far mode sbig _ ms _ _ (by omega) (by omega)
  have hmant : mb + ms >>> d + roundUp mode sbig (mb + ms >>> d) (ms % 2 ^ d) (2 ^ d) ≠ 0 := by
    omega
  have hfw := fmt.fracWidth_pos
  have hhigh : mb + ms >>> d < 2 ^ (fmt.fracWidth + 0 + 1) := by
    rw [Nat.shiftRight_eq_div_pow] at hv
    have h2 : (mb + ms >>> d) / 2 ^ fmt.fracWidth < 2 := by omega
    have := (Nat.div_lt_iff_lt_mul hFpos).1 h2
    rw [Nat.add_zero, hsplit]
    omega
  obtain ⟨hne, hk⟩ := offset_of_significand (c := 0) hfw (by omega) hlow hhigh
  have htop : (mb <<< g + ms) >>> (g + fmt.fracWidth - 1) =
      (mb + ms >>> d) >>> (fmt.fracWidth - 1) := by
    rw [show g + fmt.fracWidth - 1 = g + (fmt.fracWidth - 1) by omega, Nat.shiftRight_add,
      Nat.shiftRight_eq_div_pow (mb <<< g + ms), hquot]
  have hbeq : Nat.beq ((mb + ms >>> d) >>> (fmt.fracWidth - 1) * (g + (0 + 1))) 0 = false := by
    cases h : Nat.beq ((mb + ms >>> d) >>> (fmt.fracWidth - 1) * (g + (0 + 1))) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) (Nat.mul_ne_zero hne (by omega))
  rw [htop, hk, hbeq]
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  rw [hquot, hrem, hup]
  simp only [ne_eq, not_true_eq_false, ite_false, hmant, hle, ite_true]

/-- A selection whose chosen branch agrees with the other branch is that branch. -/
private theorem select_eq (c : Bool) (fallback result : Nat)
    (h : c = true → result = fallback) :
    Bool.casesOn (motive := fun _ => Nat) c fallback result = fallback := by
  cases c
  · rfl
  · exact h rfl

/--
The one comparison of a short path: a word plus a guard times `maxFiniteSucc` is at most the
largest finite word only when the guard is zero.
-/
private theorem guard_eq_zero {fmt : FloatFormat} {word guard : Nat}
    (h : word + guard * maxFiniteSucc fmt ≤ maxFinite fmt) : guard = 0 := by
  by_contra hne
  have hlow := Nat.le_mul_of_pos_left (maxFiniteSucc fmt) (Nat.pos_of_ne_zero hne)
  unfold maxFiniteSucc at hlow h
  omega

/-- A word is at least its exponent field less one, put back in place. -/
private theorem field_pred_shiftLeft_le (word width : Nat) :
    (word >>> width - 1) <<< width ≤ word := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  exact le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.div_mul_le_self _ _)

/-- The sign bit of a word, in place. -/
private theorem signWord_eq (fmt : FloatFormat) (a : Nat) :
    a - (a &&& magnitudeMask fmt) = a >>> signPos fmt * 2 ^ signPos fmt := by
  unfold magnitudeMask signPos
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have := Nat.div_add_mod' a (2 ^ (fmt.expWidth + fmt.fracWidth))
  omega

/--
`sumOrdered` on two operands of one sign whose sum carries: the word is the next exponent field
with half the sum of the significands and the rounding increment, when that word is at most the
largest finite one.
-/
theorem sumOrdered_carry (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sbig mb hb ms hs special : Nat) (hms : ms < 2 ^ (fmt.fracWidth + 1))
    (hmb : mb < 2 ^ (fmt.fracWidth + 1))
    (hv : ((mb + ms >>> (hb - hs)) >>> fmt.fracWidth) >>> 1 = 1)
    (hle : (hb + 1) * 2 ^ fmt.fracWidth + ((mb + ms >>> (hb - hs)) >>> 1 +
        roundUp mode sbig ((mb + ms >>> (hb - hs)) >>> 1)
          ((mb + ms >>> (hb - hs) - ((mb + ms >>> (hb - hs)) >>> 1) <<< 1) <<< (hb - hs) +
            (ms - (ms >>> (hb - hs)) <<< (hb - hs)))
          (2 ^ (hb - hs + 1))) ≤ maxFinite fmt) :
    sumOrdered fmt mode sbig 0 mb hb ms hs 0 special =
      sbig * 2 ^ signPos fmt + ((hb + 1) * 2 ^ fmt.fracWidth + ((mb + ms >>> (hb - hs)) >>> 1 +
        roundUp mode sbig ((mb + ms >>> (hb - hs)) >>> 1)
          ((mb + ms >>> (hb - hs) - ((mb + ms >>> (hb - hs)) >>> 1) <<< 1) <<< (hb - hs) +
            (ms - (ms >>> (hb - hs)) <<< (hb - hs)))
          (2 ^ (hb - hs + 1)))) := by
  have hsplit := Nat.two_pow_succ fmt.fracWidth
  have hremainder : ∀ k : Nat, ms - (ms >>> k) <<< k = ms % 2 ^ k := by
    intro k
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    exact Nat.mod_eq_sub_div_mul.symm
  rw [hremainder] at hle ⊢
  generalize hd : hb - hs = d at hv hle ⊢
  generalize hM : mb + ms >>> d = M at hv hle ⊢
  -- The sum carried, so the smaller operand reaches into the larger one: the gap is small.
  have hMlow : 2 ^ (fmt.fracWidth + 1) ≤ M := by
    have h : 1 ≤ M / 2 ^ (fmt.fracWidth + 1) := by
      rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_add]
      exact hv.ge
    simpa only [Nat.one_mul] using (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mp h
  have hshNe : ms >>> d ≠ 0 := by omega
  have hdle : d ≤ fmt.fracWidth := by
    by_contra hgt
    apply hshNe
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hms (Nat.pow_le_pow_right (by decide) (by omega)))
  have hg : d - (d - addGap fmt) = d := by unfold addGap; omega
  have hhalf : M - (M >>> 1) <<< 1 = M % 2 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.pow_one]
    exact Nat.mod_eq_sub_div_mul.symm
  rw [hhalf] at hle ⊢
  unfold sumOrdered roundQuotient
  simp only [pack_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq',
    Nat.pow_eq, div_def, mod_def, Nat.zero_mul, Nat.sub_zero, Nat.zero_add, hd, hg]
  have hquot : (mb <<< d + ms) / 2 ^ d = M := by
    rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos d),
      Nat.add_comm, ← Nat.shiftRight_eq_div_pow, hM]
  have hrem : (mb <<< d + ms) % 2 ^ d = ms % 2 ^ d := by
    rw [Nat.shiftLeft_eq, Nat.add_comm, Nat.add_mul_mod_self_right]
  have hfw := fmt.fracWidth_pos
  have hMhigh : M < 2 ^ (fmt.fracWidth + 1 + 1) := by
    have hsh : ms >>> d ≤ ms := Nat.shiftRight_le _ _
    omega
  obtain ⟨hne, hk⟩ := offset_of_significand (c := 1) hfw (by omega) hMlow hMhigh
  have htop : (mb <<< d + ms) >>> (d + fmt.fracWidth - 1) = M >>> (fmt.fracWidth - 1) := by
    rw [show d + fmt.fracWidth - 1 = d + (fmt.fracWidth - 1) by omega, Nat.shiftRight_add,
      Nat.shiftRight_eq_div_pow (mb <<< d + ms), hquot]
  have hbeq : Nat.beq (M >>> (fmt.fracWidth - 1) * (d + (1 + 1))) 0 = false := by
    cases h : Nat.beq (M >>> (fmt.fracWidth - 1) * (d + (1 + 1))) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) (Nat.mul_ne_zero hne (by omega))
  have hquot1 : (mb <<< d + ms) / 2 ^ (d + 1) = M >>> 1 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hquot, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hrem1 : (mb <<< d + ms) % 2 ^ (d + 1) = (M % 2) <<< d + ms % 2 ^ d := by
    rw [Nat.mod_pow_succ, hrem, hquot, Nat.shiftLeft_eq, Nat.add_comm, Nat.mul_comm]
  rw [htop, hk, hbeq]
  simp only [show hb + (1 + 1) - 1 = hb + 1 by omega, show d + (1 + 1) - 1 = d + 1 by omega]
  rw [hquot1, hrem1]
  have hmant : M >>> 1 + roundUp mode sbig (M >>> 1) ((M % 2) <<< d + ms % 2 ^ d)
      (2 ^ (d + 1)) ≠ 0 := by
    have hq : 2 ^ fmt.fracWidth ≤ M >>> 1 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      omega
    omega
  simp only [ne_eq, not_true_eq_false, ite_false, hmant, hle, ite_true]

/--
The exponent gap of the carry path is cut at `fracWidth + 2`: a significand
`ms < 2 ^ (fracWidth + 1)` shifted further is zero either way, and what it leaves behind rounds
the same way. The path then never builds a power of two of the size of an exponent difference.
-/
theorem gap_clamped (mode : Model.IEEERoundingMode) (sign q bit ms F d : Nat)
    (hms : ms < 2 ^ (F + 1)) (hbit : bit ≤ 1) :
    ms >>> (F + 2 - (F + 2 - d)) = ms >>> d ∧
      roundUp mode sign q
          (bit <<< (F + 2 - (F + 2 - d)) + (ms - (ms >>> d) <<< (F + 2 - (F + 2 - d))))
          (2 ^ (F + 2 - (F + 2 - d) + 1)) =
        roundUp mode sign q (bit <<< d + (ms - (ms >>> d) <<< d)) (2 ^ (d + 1)) := by
  by_cases hd : d ≤ F + 2
  · rw [show F + 2 - (F + 2 - d) = d by omega]
    exact ⟨rfl, rfl⟩
  · have hg : F + 2 - (F + 2 - d) = F + 2 := by omega
    have hpow : 2 ^ (F + 1) + 2 ^ (F + 1) = 2 ^ (F + 2) := by
      rw [← Nat.two_mul, ← Nat.pow_succ']
    have hle : 2 ^ (F + 2) ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    have hz1 : ms >>> (F + 2) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (by omega)
    have hz2 : ms >>> d = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (by omega)
    rw [hg, hz1, hz2]
    simp only [Nat.zero_shiftLeft, Nat.sub_zero]
    exact ⟨trivial, roundUp_carry mode sign q bit ms _ _ hbit (by omega) (by omega)⟩

/--
`addCarryWith` computes `addFastWith`, on all natural numbers: when its comparison succeeds,
its word is the result of the short path of `addFastWith`.
-/
theorem addCarryWith_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b special : Nat) :
    addCarryWith fmt mode a b (addFastWith fmt mode a b special) =
      addFastWith fmt mode a b special := by
  have hF : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  unfold addCarryWith
  refine select_eq _ _ _ (fun htest => ?_)
  have hle := Nat.le_of_ble_eq_true htest
  unfold addFastWith
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.land_eq, Nat.xor_eq, Nat.shiftLeft_eq',
    Nat.shiftRight_eq', Nat.pow_eq, Nat.succ_eq_add_one] at hle ⊢
  rw [signWord_eq]
  generalize a &&& magnitudeMask fmt = ua at hle ⊢
  generalize b &&& magnitudeMask fmt = ub at hle ⊢
  generalize ub + (ua - ub) = big at hle ⊢
  generalize ua - (ua - ub) = small at hle ⊢
  have hbigLe := field_pred_shiftLeft_le big fmt.fracWidth
  have hms := significand_lt fmt.fracWidth small
  have hmb := significand_lt fmt.fracWidth big
  generalize big >>> fmt.fracWidth - 1 = hb at hle hbigLe hmb ⊢
  generalize small >>> fmt.fracWidth - 1 = hs at hle hms ⊢
  generalize small - hs <<< fmt.fracWidth = ms at hle hms ⊢
  generalize hmbDef : big - hb <<< fmt.fracWidth = mb at hle hmb ⊢
  have hbigEq : big = hb * 2 ^ fmt.fracWidth + mb := by
    rw [Nat.shiftLeft_eq] at hbigLe hmbDef
    omega
  -- The gap is cut at `fracWidth + 2`, which changes neither the shifted significand nor the
  -- rounding.
  rw [(gap_clamped mode 0 0 0 ms fmt.fracWidth (hb - hs) hms (Nat.zero_le 1)).1] at hle ⊢
  have hbit : mb + ms >>> (hb - hs) - ((mb + ms >>> (hb - hs)) >>> 1) <<< 1 ≤ 1 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.pow_one]
    omega
  rw [(gap_clamped mode _ _ _ ms fmt.fracWidth (hb - hs) hms hbit).2] at hle ⊢
  -- The comparison says that every guard is zero and that the word is finite.
  have hguard : (a ^^^ b) >>> signPos fmt +
      (1 - ((mb + ms >>> (hb - hs)) >>> fmt.fracWidth) >>> 1) + negZeroNaN fmt = 0 :=
    guard_eq_zero hle
  rw [hguard, Nat.zero_mul, Nat.add_zero] at hle
  obtain ⟨hrest, hnzn⟩ := Nat.eq_zero_of_add_eq_zero hguard
  obtain ⟨hx, hcarry⟩ := Nat.eq_zero_of_add_eq_zero hrest
  have hsame : a >>> signPos fmt ^^^ b >>> signPos fmt = 0 := by
    rw [← Nat.shiftRight_xor_distrib]
    exact hx
  have hv : ((mb + ms >>> (hb - hs)) >>> fmt.fracWidth) >>> 1 = 1 := by
    have hvle : (mb + ms >>> (hb - hs)) >>> fmt.fracWidth < 4 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply (Nat.div_lt_iff_lt_mul hF).2
      have hsh : ms >>> (hb - hs) ≤ ms := Nat.shiftRight_le _ _
      omega
    generalize (mb + ms >>> (hb - hs)) >>> fmt.fracWidth = v at hcarry hvle
    rw [Nat.shiftRight_eq_div_pow] at hcarry ⊢
    omega
  have hfinite : big - maxFinite fmt + negZeroNaN fmt = 0 := by
    have hMlow : 2 ^ (fmt.fracWidth + 1) ≤ mb + ms >>> (hb - hs) := by
      have h : 1 ≤ (mb + ms >>> (hb - hs)) / 2 ^ (fmt.fracWidth + 1) := by
        rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_add]
        exact hv.ge
      simpa only [Nat.one_mul] using (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mp h
    have hhalf : 2 ^ fmt.fracWidth ≤ (mb + ms >>> (hb - hs)) >>> 1 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      omega
    have hbigFinite : big ≤ maxFinite fmt := by
      have hexpand : (hb + 1) <<< fmt.fracWidth =
          hb * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
        rw [Nat.shiftLeft_eq, Nat.add_mul, Nat.one_mul]
      rw [hexpand] at hle
      omega
    rw [Nat.sub_eq_zero_of_le hbigFinite, hnzn]
  rw [hsame, hfinite, Nat.zero_and, Nat.xor_zero]
  have hexpand : (hb + 1) <<< fmt.fracWidth = (hb + 1) * 2 ^ fmt.fracWidth := Nat.shiftLeft_eq _ _
  rw [hexpand] at hle ⊢
  rw [sumOrdered_carry fmt mode _ mb hb ms hs special hms hmb hv hle]

/-- `addCarry` computes `addFast`, on all natural numbers. -/
theorem addCarry_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) :
    addCarry fmt mode a b = addFast fmt mode a b :=
  addCarryWith_eq fmt mode a b (add fmt mode a b)

/--
`addSameWith` computes `addFastWith` on natural numbers whose sign bits agree: when its
comparison succeeds, its word is the result of the short path of `addFastWith`.
-/
theorem addSameWith_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b special : Nat) (hx : (a ^^^ b) >>> signPos fmt = 0) :
    addSameWith fmt mode a b (addFastWith fmt mode a b special) =
      addFastWith fmt mode a b special := by
  have hF : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hfw := fmt.fracWidth_pos
  unfold addSameWith
  refine select_eq _ _ _ (fun htest => ?_)
  have hle := Nat.le_of_ble_eq_true htest
  unfold addFastWith
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.land_eq, Nat.xor_eq, Nat.shiftLeft_eq',
    Nat.shiftRight_eq', Nat.succ_eq_add_one] at hle ⊢
  rw [signWord_eq]
  generalize a &&& magnitudeMask fmt = ua at hle ⊢
  generalize b &&& magnitudeMask fmt = ub at hle ⊢
  generalize ub + (ua - ub) = big at hle ⊢
  generalize ua - (ua - ub) = small at hle ⊢
  have hbigLe := field_pred_shiftLeft_le big fmt.fracWidth
  have hms := significand_lt fmt.fracWidth small
  generalize hhb : big >>> fmt.fracWidth - 1 = hb at hle hbigLe ⊢
  generalize small >>> fmt.fracWidth - 1 = hs at hle hms ⊢
  generalize hmsDef : small - hs <<< fmt.fracWidth = ms at hle hms ⊢
  generalize hmbDef : big - hb <<< fmt.fracWidth = mb
  have hbigEq : big = hb * 2 ^ fmt.fracWidth + mb := by
    rw [Nat.shiftLeft_eq] at hbigLe hmbDef
    omega
  -- The rounding increment is taken with a shift, over the denominator `2 ^ (hb - hs)`.
  rw [roundUpShift_eq] at hle ⊢
  -- The comparison says that every guard is zero and that the word is finite.
  have hguard : ((big + ms >>> (hb - hs)) >>> fmt.fracWidth - (hb + 1) + negZeroNaN fmt) +
      (1 - (big + ms >>> (hb - hs))) = 0 :=
    guard_eq_zero hle
  rw [hguard, Nat.zero_mul, Nat.add_zero] at hle
  obtain ⟨hrest, hpos⟩ := Nat.eq_zero_of_add_eq_zero hguard
  obtain ⟨hcarry, hnzn⟩ := Nat.eq_zero_of_add_eq_zero hrest
  have hsame : a >>> signPos fmt ^^^ b >>> signPos fmt = 0 := by
    rw [← Nat.shiftRight_xor_distrib]
    exact hx
  have hparity : (big + ms >>> (hb - hs)) % 2 = (mb + ms >>> (hb - hs)) % 2 := by
    simp [hbigEq, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hfw.ne']
  rw [roundUp_parity mode _ _ _ _ _ hparity] at hle ⊢
  have hfinite : big - maxFinite fmt + negZeroNaN fmt = 0 := by
    have hbigFinite : big ≤ maxFinite fmt :=
      le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hle
    rw [Nat.sub_eq_zero_of_le hbigFinite, hnzn]
  rw [hsame, hfinite, Nat.zero_and, Nat.xor_zero]
  by_cases htop : (big + ms >>> (hb - hs)) >>> fmt.fracWidth = hb + 1
  · -- The exponent field of the larger operand stays.
    have hv : (mb + ms >>> (hb - hs)) >>> fmt.fracWidth = 1 := by
      rw [hbigEq, Nat.add_assoc, Nat.shiftRight_eq_div_pow, Nat.add_comm,
        Nat.add_mul_div_right _ _ hF] at htop
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [hbigEq, Nat.add_assoc (hb * 2 ^ fmt.fracWidth) mb,
      Nat.add_assoc (hb * 2 ^ fmt.fracWidth)] at hle
    rw [sumOrdered_short fmt mode _ mb hb ms hs special hms hv hle, hbigEq]
    omega
  · -- Both operands are subnormal and so is their sum, which is exact.
    have hfield : big >>> fmt.fracWidth ≤ (big + ms >>> (hb - hs)) >>> fmt.fracWidth := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_div_right (Nat.le_add_right _ _)
    have hb0 : hb = 0 := by omega
    subst hb0
    have hzero : (big + ms >>> (0 - hs)) >>> fmt.fracWidth = 0 := by
      generalize (big + ms >>> (0 - hs)) >>> fmt.fracWidth = top at hcarry htop ⊢
      omega
    have hmb : big = mb := by rw [hbigEq, Nat.zero_mul, Nat.zero_add]
    simp only [Nat.zero_sub, Nat.shiftRight_zero, Nat.shiftLeft_zero, Nat.sub_self,
      Nat.pow_zero, hmb] at hzero hpos ⊢
    rw [roundUp_exact mode _ _ 1, Nat.add_zero]
    have hsum : mb + ms < 2 ^ fmt.fracWidth :=
      Kernel.lt_two_pow_of_shiftRight_eq_zero hzero
    rw [sumOrdered_tiny fmt mode _ mb ms hs special hsum (by omega)]

/-- `addSame` computes `addFast` on natural numbers whose sign bits agree. -/
theorem addSame_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat)
    (hx : (a ^^^ b) >>> signPos fmt = 0) :
    addSame fmt mode a b = addFast fmt mode a b := by
  unfold addSame
  rw [addCarry_eq]
  exact addSameWith_eq fmt mode a b (add fmt mode a b) hx

/-- `addShort` computes `addFast`, on all natural numbers. -/
theorem addShort_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) :
    addShort fmt mode a b = addFast fmt mode a b := by
  unfold addShort bySign
  exact select_eq _ _ _ (fun hsigns => addSame_eq fmt mode a b (Nat.eq_of_beq_eq_true hsigns))

/--
`addShort` computes the encoding of the reference addition `Model.add x y (mode := mode)`, for
every format descriptor, every rounding direction and all operands.
-/
theorem addShort_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    addShort fmt mode x.toNatBits y.toNatBits = (Model.add x y (mode := mode)).toNatBits := by
  rw [addShort_eq, addFast_eq_spec]

/--
`subShort` computes the encoding of the reference subtraction `Model.sub x y (mode := mode)`,
for every format descriptor, every rounding direction and all operands.
-/
theorem subShort_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    subShort fmt mode x.toNatBits y.toNatBits = (Model.sub x y (mode := mode)).toNatBits := by
  unfold subShort
  rw [sub_eq_add_neg, neg_eq_spec, addShort_eq_spec]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
