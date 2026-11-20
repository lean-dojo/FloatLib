/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Classification
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Predicates
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Scale
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Numerics.Kernel.Log2
public import FloatLib.Numerics.Kernel.Z

/-!
# Exact values of encodings, and their rounding, for Lean's kernel

Many operations of the reference are written in three steps: they decode their operands to
exact values (`Model.toDyadic?`, `Model.exactValue`), compute on those values, and round the
result once (`Model.Internal.Directed.roundDyadic`). The first and the last step go through the
bit-vector model, which Lean's kernel reduces slowly. This module gives both steps on
natural-number encodings:

* `decode fmt a` is the exact dyadic value of the finite word `a`, built from shifts and masks
  (`toDyadic?_eq_decode`, `toDyadic?_eq`), and `exactValue fmt a` is the complete exact value
  of any word (`exactValue_eq`).
* `roundDyadic fmt mode d` is the encoding of the dyadic `d` rounded in the direction `mode`
  (`roundDyadic_eq`), `KernelPath.round` at the exponent of `d`.
* `addExact`, `subExact` and `mulExact` are the exact sum, difference and product of two
  dyadic values with the alignment and the signed sum on natural numbers (`addExact_eq`,
  `subExact_eq`, `mulExact_eq`): the middle step of the sums and products of the reference.

An operation written in the three steps then has a kernel form with the same middle step, and
its refinement proof rewrites the two ends. Every statement holds for every format descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The exact value of the finite word `a` (`toDyadic?_eq_decode`): the sign bit, the significand
with its implicit bit, and the exponent `e - bias - fracWidth` of a normal word with exponent
field `e`, the least subnormal exponent of a subnormal word, and zero for a zero.
-/
def decode (fmt : FloatFormat) (a : Nat) : Numerics.Dyadic :=
  (fun u =>
    (fun e =>
      { negative := Nat.beq (Nat.shiftRight a (signPos fmt)) 1
        significand := Nat.sub u (Nat.shiftLeft (Nat.sub e 1) fmt.fracWidth)
        exponent :=
          Bool.casesOn (motive := fun _ => Int) (Nat.beq e 0)
            (Int.subNatNat e (Nat.add fmt.exponentBias fmt.fracWidth))
            (Bool.casesOn (motive := fun _ => Int) (Nat.beq u 0)
              (Int.subNatNat 1 (Nat.add fmt.exponentBias fmt.fracWidth)) (Int.ofNat 0)) })
      (Nat.shiftRight u fmt.fracWidth))
    (Nat.land a (magnitudeMask fmt))

/--
The complete exact value of the word `a` (`exactValue_eq`): the dyadic value of a finite word,
an infinity with its sign, and a NaN with its sign, signaling state and fraction field.
-/
def exactValue (fmt : FloatFormat) (a : Nat) : Model.ExactValue :=
  Bool.casesOn (motive := fun _ => Model.ExactValue) (Nat.beq (finiteCode fmt a) 1)
    (Bool.casesOn (motive := fun _ => Model.ExactValue) (Nat.beq (infCode fmt a) 1)
      (.nan (Nat.beq (signCode fmt a) 1) (Nat.beq (signalingCode fmt a) 1) (fracCode fmt a))
      (.infinity (Nat.beq (signCode fmt a) 1)))
    (.finite (decode fmt a))

/--
Encoding of the exact dyadic `d` rounded into `fmt` in the direction `mode`
(`roundDyadic_eq`): `KernelPath.round` of its significand at its exponent, counted from the
least subnormal exponent of the format.
-/
def roundDyadic (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (d : Numerics.Dyadic) :
    Nat :=
  (fun e =>
    round fmt mode (Numerics.Kernel.size d.significand) (signNat d.negative)
      (signNat d.negative) d.significand (Kernel.Z.toNat e) (Kernel.Z.toNat (Kernel.Z.neg e))
      0 0)
    (Kernel.Z.add d.exponent
      (Int.ofNat (Nat.sub (Nat.add fmt.exponentBias fmt.fracWidth) 1)))

/-- The least subnormal exponent, as a difference of natural numbers. -/
theorem subNatNat_minSubnormalExponent (fmt : FloatFormat) :
    Int.subNatNat 1 (fmt.exponentBias + fmt.fracWidth) = fmt.minSubnormalExponent := by
  rw [Int.subNatNat_eq_coe]
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast]
  omega

/-- `decode` is the exact value that the reference reads off a finite word. -/
theorem toDyadic?_eq_decode {fmt : FloatFormat} (x : Model fmt)
    (hfinite : Model.isFinite x = true) :
    Model.toDyadic? x = some (decode fmt x.toNatBits) := by
  have he := Model.expField_lt_pow2 x
  have hf := Model.fracField_lt_pow2 x
  have hdecode := Model.toDyadic?_ofFields_of_isFinite fmt (Model.signBit x)
    (Model.expField x) (Model.fracField x) he hf
    (by rw [Model.ofFields_signBit_expField_fracField]; exact hfinite)
  rw [Model.ofFields_signBit_expField_fracField] at hdecode
  rw [hdecode]
  unfold decode
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    sign_toNatBits, magnitude_toNatBits, fields_shiftRight _ _ _ hf, fields_sub_shiftLeft,
    beq_flag]
  by_cases hexp : Model.expField x = 0
  · by_cases hfrac : Model.fracField x = 0
    · simp only [hexp, hfrac, ite_true, Nat.zero_mul, Nat.add_zero]
      rfl
    · have hfields : Nat.beq (0 * 2 ^ fmt.fracWidth + Model.fracField x) 0 = false :=
        beq_zero_eq_false (by omega)
      simp only [hexp, hfrac, ite_true, ite_false, hfields, subNatNat_minSubnormalExponent]
      rfl
  · have hbeq : Nat.beq (Model.expField x) 0 = false := beq_zero_eq_false hexp
    simp only [hexp, ite_false, hbeq, Model.pow2_eq_two_pow, Int.subNatNat_eq_coe,
      Int.ofNat_eq_natCast]
    congr 2
    push_cast
    omega

/-- The exact value of any word: none for a word that is not finite, and `decode` otherwise. -/
theorem toDyadic?_eq {fmt : FloatFormat} (x : Model fmt) :
    Model.toDyadic? x = someWhen (finiteCode fmt x.toNatBits) (decode fmt x.toNatBits) := by
  unfold someWhen
  rw [finiteCode_eq]
  cases hfinite : Model.isFinite x
  · exact toDyadic?_eq_none_of_isFinite_eq_false x hfinite
  · exact toDyadic?_eq_decode x hfinite

/-- `exactValue` computes the complete exact value of an encoding. -/
theorem exactValue_eq {fmt : FloatFormat} (x : Model fmt) :
    exactValue fmt x.toNatBits = Model.exactValue x := by
  unfold exactValue Model.exactValue
  rw [finiteCode_eq, infCode_eq, signCode_eq, signalingCode_eq, fracCode_eq]
  cases hfinite : Model.isFinite x
  · rw [toDyadic?_eq_none_of_isFinite_eq_false x hfinite]
    cases Model.isInfinite x <;> rfl
  · rw [toDyadic?_eq_decode x hfinite]

/--
`roundDyadic` computes the encoding of the reference rounding of an exact dyadic, for every
format descriptor, rounding direction and dyadic.
-/
theorem roundDyadic_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (d : Numerics.Dyadic) :
    roundDyadic fmt mode d = (Model.Internal.Directed.roundDyadic fmt mode d).toNatBits := by
  have hbias := fmt.exponentBias_pos
  unfold roundDyadic
  simp only [Kernel.Z.add_eq, Kernel.Z.toNat_eq, Kernel.Z.neg_eq]
  refine round_eq fmt mode _ _ _ _ _ _ _ d ?_ rfl rfl ?_ (fun _ => rfl)
  · rw [Numerics.Kernel.size_eq]
    exact Nat.lt_size_self _
  · intro _
    change d.exponent =
      ((d.exponent + ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int)).toNat : Int) -
          ((-(d.exponent + ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int))).toNat : Int) +
        fmt.minSubnormalExponent
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega

/-- In the nearest-even direction `roundDyadic` is the encoding of `Model.roundDyadic`. -/
theorem roundDyadic_nearest_eq (fmt : FloatFormat) (d : Numerics.Dyadic) :
    roundDyadic fmt .nearest d = (Model.roundDyadic fmt d).toNatBits :=
  roundDyadic_eq fmt .nearest d

/-- The signed sum of two nonzero magnitudes on one exponent, as the reference forms it. -/
theorem signedSum_eq (an bn : Bool) (ma mb : Nat) (e : Int) (_hma : ma ≠ 0) (_hmb : mb ≠ 0) :
    (if ((if an then -Int.ofNat ma else Int.ofNat ma) +
          (if bn then -Int.ofNat mb else Int.ofNat mb)) == 0 then
        ({ negative := an && bn, significand := 0, exponent := 0 } : Numerics.Dyadic)
      else
        { negative := ((if an then -Int.ofNat ma else Int.ofNat ma) +
            (if bn then -Int.ofNat mb else Int.ofNat mb)) < 0
          significand := ((if an then -Int.ofNat ma else Int.ofNat ma) +
            (if bn then -Int.ofNat mb else Int.ofNat mb)).natAbs
          exponent := e }) =
      Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Bool.xor an bn)
        (⟨an, Nat.add ma mb, e⟩ : Numerics.Dyadic)
        (Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Nat.beq ma mb)
          (Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Nat.ble mb ma)
            ⟨bn, Nat.sub mb ma, e⟩ ⟨an, Nat.sub ma mb, e⟩)
          ⟨Bool.and an bn, 0, 0⟩) := by
  have hbeq : Nat.beq ma mb = decide (ma = mb) := by
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]
  have hble : Nat.ble mb ma = decide (mb ≤ ma) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  rw [hbeq, hble]
  rcases an with _ | _ <;> rcases bn with _ | _ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_true, Bool.and_self,
      Int.ofNat_eq_natCast, beq_iff_eq, Nat.add_eq, Nat.sub_eq]
  · rw [ite_eq_right (by omega)]
    congr 1
  · by_cases h : ma = mb
    · subst h
      simp
    · rw [ite_eq_right (by omega), decide_eq_false h]
      by_cases h2 : mb ≤ ma
      · rw [decide_eq_true h2]
        simp only []
        congr 1 <;> first | exact decide_eq_false (by omega) | omega
      · rw [decide_eq_false h2]
        simp only []
        congr 1 <;> first | exact decide_eq_true (by omega) | omega
  · by_cases h : ma = mb
    · subst h
      simp
    · rw [ite_eq_right (by omega), decide_eq_false h]
      by_cases h2 : mb ≤ ma
      · rw [decide_eq_true h2]
        simp only []
        congr 1 <;> first | exact decide_eq_true (by omega) | omega
      · rw [decide_eq_false h2]
        simp only []
        congr 1 <;> first | exact decide_eq_false (by omega) | omega
  · rw [ite_eq_right (by omega)]
    congr 1 <;> first | exact decide_eq_true (by omega) | omega

/--
The exact sum of two dyadic values, for Lean's kernel (`addExact_eq`): `Numerics.Dyadic.add`
with the two significands aligned by shifts of natural numbers and the signed sum formed
without an integer.
-/
def addExact (a b : Numerics.Dyadic) : Numerics.Dyadic :=
  Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Nat.beq a.significand 0)
    (Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Nat.beq b.significand 0)
      ((fun above below =>
          (fun ma mb exponent =>
            Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Bool.xor a.negative b.negative)
              (⟨a.negative, Nat.add ma mb, exponent⟩ : Numerics.Dyadic)
              (Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Nat.beq ma mb)
                (Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Nat.ble mb ma)
                  ⟨b.negative, Nat.sub mb ma, exponent⟩ ⟨a.negative, Nat.sub ma mb, exponent⟩)
                ⟨Bool.and a.negative b.negative, 0, 0⟩))
            (Nat.shiftLeft a.significand above) (Nat.shiftLeft b.significand below)
            (Bool.casesOn (motive := fun _ => Int) (Nat.beq above 0) b.exponent a.exponent))
        (Kernel.Z.toNat (Kernel.Z.sub a.exponent b.exponent))
        (Kernel.Z.toNat (Kernel.Z.sub b.exponent a.exponent)))
      a)
    (Bool.casesOn (motive := fun _ => Numerics.Dyadic) (Nat.beq b.significand 0) b
      ⟨Bool.and a.negative b.negative, 0, 0⟩)

/-- `addExact` is the exact sum of the reference. -/
theorem addExact_eq (a b : Numerics.Dyadic) : addExact a b = Numerics.Dyadic.add a b := by
  obtain ⟨an, as, ae⟩ := a
  obtain ⟨bn, bs, be⟩ := b
  unfold addExact Numerics.Dyadic.add Numerics.Dyadic.addFields
  simp only [Kernel.Z.sub_eq, Kernel.Z.toNat_eq]
  by_cases ha : as = 0
  · subst ha
    by_cases hb : bs = 0
    · subst hb
      rfl
    · simp only [beq_zero_eq_false hb, beq_self_eq_true, ite_true, show (bs == 0) = false from by
        simpa using hb, Bool.false_eq_true, ite_false]
      rfl
  · have hsa : (as == 0) = false := by simpa using ha
    by_cases hb : bs = 0
    · subst hb
      simp only [beq_zero_eq_false ha, hsa, beq_self_eq_true, ite_true, Bool.false_eq_true,
        ite_false]
      rfl
    · have hsb : (bs == 0) = false := by simpa using hb
      simp only [beq_zero_eq_false ha, beq_zero_eq_false hb, hsa, hsb, Bool.false_eq_true,
        ite_false]
      by_cases hle : ae ≤ be
      · have habove : (ae - be).toNat = 0 := by omega
        have hma : as <<< 0 ≠ 0 := by simpa using ha
        have hmb : bs <<< (be - ae).toNat ≠ 0 := by simp [Nat.shiftLeft_eq, hb]
        rw [ite_eq_left hle, habove]
        exact (signedSum_eq an bn (as <<< 0) (bs <<< (be - ae).toNat) ae hma hmb).symm
      · have habove : (ae - be).toNat ≠ 0 := by omega
        have hbelow : (be - ae).toNat = 0 := by omega
        have hma : as <<< (ae - be).toNat ≠ 0 := by simp [Nat.shiftLeft_eq, ha]
        have hmb : bs <<< 0 ≠ 0 := by simpa using hb
        rw [ite_eq_right hle, hbelow, beq_zero_eq_false habove]
        exact (signedSum_eq an bn (as <<< (ae - be).toNat) (bs <<< 0) be hma hmb).symm

/--
The exact difference of two dyadic values, for Lean's kernel (`subExact_eq`): `addExact` of
the second value with its sign changed.
-/
def subExact (a b : Numerics.Dyadic) : Numerics.Dyadic :=
  addExact a ⟨Bool.not b.negative, b.significand, b.exponent⟩

/-- `subExact` is the exact difference of the reference. -/
theorem subExact_eq (a b : Numerics.Dyadic) : subExact a b = Numerics.Dyadic.sub a b := by
  unfold subExact
  rw [addExact_eq]
  rfl

/--
The exact product of two dyadic values, for Lean's kernel (`mulExact_eq`): the product of the
significands at the sum of the exponents.
-/
def mulExact (a b : Numerics.Dyadic) : Numerics.Dyadic :=
  ⟨Bool.xor a.negative b.negative, Nat.mul a.significand b.significand,
    Kernel.Z.add a.exponent b.exponent⟩

/-- `mulExact` is the exact product of the reference. -/
theorem mulExact_eq (a b : Numerics.Dyadic) : mulExact a b = Numerics.Dyadic.mul a b := by
  unfold mulExact Numerics.Dyadic.mul Numerics.Dyadic.mulFields
  rw [Kernel.Z.add_eq]
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
