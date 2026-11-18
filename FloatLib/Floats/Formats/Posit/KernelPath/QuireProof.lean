/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.KernelPath.Flat
public import FloatLib.Floats.Formats.Posit.KernelPath.Standard
public import FloatLib.Floats.Formats.Posit.Quire.Arithmetic.Proof
public import FloatLib.Tactic.KernelOptimize

/-!
# The kernel quire operations compute the Posit Standard quire operations

For every Posit Standard (2022) width and every operand, the functions of `KernelPath.Quire` on
encodings are the encodings of the reference operations of `Quire.Model` (§5.11):

* `quireAccumulate_eq`: the checked sum of an ordinary quire and a signed integer increment is
  `Model.ofCoefficient` of the exact sum, NaR on overflow included;
* `qAddP_eq_kernel`, `qSubP_eq_kernel`, `qMulAdd_eq_kernel`, `qMulSub_eq_kernel`,
  `qAddQ_eq_kernel`, `qSubQ_eq_kernel`, `pToQ_eq_kernel`, `qNegate_eq_kernel`, `qAbs_eq_kernel`:
  the accumulations, the conversion, negation and absolute value;
* `qToP_eq_kernel`: the rounding of a quire to its posit.

Each of the last group is tagged `@[kernel_optimize]`, so `float_decide` evaluates a quire
computation on natural numbers.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel FloatLib.Numerics.Representations
open FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-! ## Quire words -/

/-- The kernel quire width is the quire width of the format. -/
theorem quireWidth_eq (format : Format) : quireWidth format.payloadBits = Quire.width format := by
  unfold quireWidth Quire.width
  kernel_notation
  rw [bits_eq]

/-- The kernel quire NaR word is `2 ^ (width - 1)`. -/
theorem quireNar_eq (format : Format) :
    quireNar format.payloadBits = 2 ^ (Quire.width format - 1) := by
  unfold quireNar
  kernel_notation
  rw [quireWidth_eq]

/-- The quire modulus is twice the NaR word. -/
theorem two_pow_width (format : Format) :
    2 ^ Quire.width format = 2 * 2 ^ (Quire.width format - 1) := by
  have h := Quire.width_pos format
  rw [← Nat.pow_succ']
  congr 1
  omega

/-- A quire word is below the modulus. -/
theorem quire_toNatBits_lt (q : Quire.Model format) :
    q.toNatBits < 2 * 2 ^ (Quire.width format - 1) := by
  rw [← two_pow_width]
  exact q.word.bits.isLt

/-- The coefficient of a quire, from its word: the word below the NaR word, and the word minus
the modulus from it on. -/
theorem coefficient_eq (q : Quire.Model format) :
    q.coefficient =
      if q.toNatBits < 2 ^ (Quire.width format - 1) then (q.toNatBits : Int)
      else (q.toNatBits : Int) - ((2 * 2 ^ (Quire.width format - 1) : Nat) : Int) := by
  have h := two_pow_width format
  change q.word.bits.toInt = _
  rw [BitVec.toInt_eq_toNat_cond, h]
  change (if 2 * q.toNatBits < _ then (q.toNatBits : Int) else _) = _
  by_cases hlt : q.toNatBits < 2 ^ (Quire.width format - 1)
  · rw [ite_eq_left (by omega), ite_eq_left hlt]
  · rw [ite_eq_right (by omega), ite_eq_right hlt]
    rfl

/-- The quire NaR word is `2 ^ (width - 1)`. -/
theorem quire_nar_toNatBits (format : Format) :
    (Quire.Model.nar format).toNatBits = 2 ^ (Quire.width format - 1) := by
  change (BitVec.intMin (Quire.width format)).toNat = _
  rw [BitVec.toNat_intMin]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide)
    (Nat.sub_lt (Quire.width_pos format) (by decide)))

/-- A quire is NaR exactly when its word is the NaR word. -/
theorem quire_eq_nar_iff (q : Quire.Model format) :
    q = Quire.Model.nar format ↔ q.toNatBits = 2 ^ (Quire.width format - 1) := by
  constructor
  · rintro rfl
    exact quire_nar_toNatBits format
  · intro h
    rw [← Quire.Model.ofNatBits_toNatBits q, h, ← quire_nar_toNatBits,
      Quire.Model.ofNatBits_toNatBits]

/-- The NaR test on a quire word decides whether the quire is NaR. -/
theorem beq_quireNar (q : Quire.Model format) :
    Nat.beq q.toNatBits (quireNar format.payloadBits) = q.isNaR := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, Quire.Model.isNaR_eq_true_iff, quireNar_eq, quire_eq_nar_iff]

/--
The word of a checked coefficient: for `K = c + 2 * H` with `H` the NaR word, the coefficient
`c` is ordinary exactly when `H < K < 3 * H`, and then its word is `K % (2 * H)`.
-/
theorem toNatBits_ofCoefficient (c : Int) (K : Nat)
    (hK : (K : Int) = c + ((2 * 2 ^ (Quire.width format - 1) : Nat) : Int)) :
    (Quire.Model.ofCoefficient format c).toNatBits =
      if 2 ^ (Quire.width format - 1) < K ∧ K < 3 * 2 ^ (Quire.width format - 1) then
        K % (2 * 2 ^ (Quire.width format - 1))
      else 2 ^ (Quire.width format - 1) := by
  have hcast : ((2 : Int) ^ (Quire.width format - 1)) =
      ((2 ^ (Quire.width format - 1) : Nat) : Int) := by push_cast; rfl
  have hiff : Quire.Model.OrdinaryCoefficient format c ↔
      -((2 ^ (Quire.width format - 1) : Nat) : Int) < c ∧
        c ≤ ((2 ^ (Quire.width format - 1) : Nat) : Int) - 1 := by
    rw [Quire.Model.OrdinaryCoefficient, FixedInt.minValue_eq (Quire.width_pos format),
      FixedInt.maxValue_eq, hcast]
  unfold Quire.Model.ofCoefficient
  by_cases hord : Quire.Model.OrdinaryCoefficient format c
  · have hord' := hiff.1 hord
    rw [ite_eq_left hord, ite_eq_left (by omega)]
    change (BitVec.ofInt (Quire.width format) c).toNat = _
    rw [BitVec.toNat_ofInt, two_pow_width]
    have hc : c = (K : Int) + (-1) * ((2 * 2 ^ (Quire.width format - 1) : Nat) : Int) := by omega
    rw [hc, Int.add_mul_emod_self_right]
    exact_mod_cast Int.toNat_natCast _
  · have hord' := mt hiff.2 hord
    rw [ite_eq_right hord, ite_eq_right (by omega)]
    exact quire_nar_toNatBits format

/-- The key of an ordinary quire: its coefficient plus the NaR word, strictly inside the
modulus. -/
theorem quire_key (q : Quire.Model format) (hq : q.isNaR = false) :
    (((q.toNatBits + 2 ^ (Quire.width format - 1)) % (2 * 2 ^ (Quire.width format - 1)) : Nat) :
        Int) = q.coefficient + ((2 ^ (Quire.width format - 1) : Nat) : Int) ∧
      0 < (q.toNatBits + 2 ^ (Quire.width format - 1)) % (2 * 2 ^ (Quire.width format - 1)) ∧
      (q.toNatBits + 2 ^ (Quire.width format - 1)) % (2 * 2 ^ (Quire.width format - 1)) <
        2 * 2 ^ (Quire.width format - 1) := by
  have hlt := quire_toNatBits_lt q
  have hne : q.toNatBits ≠ 2 ^ (Quire.width format - 1) := fun h =>
    Bool.false_ne_true (hq.symm.trans ((Quire.Model.isNaR_eq_true_iff q).2
      ((quire_eq_nar_iff q).2 h)))
  have hpos := Nat.two_pow_pos (Quire.width format - 1)
  rw [coefficient_eq]
  generalize 2 ^ (Quire.width format - 1) = H at hlt hne hpos ⊢
  by_cases hsmall : q.toNatBits < H
  · rw [ite_eq_left hsmall, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> omega
  · rw [ite_eq_right hsmall, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> omega

/--
Posit Standard (2022), §5.11: `quireAccumulate` on the word of an ordinary quire is the word of
the checked sum of its coefficient and the signed increment, quire NaR on overflow, for every
width.
-/
theorem quireAccumulate_eq (q : Quire.Model format) (hq : q.isNaR = false) (s : Bool) (c : Nat) :
    quireAccumulate format.payloadBits q.toNatBits (if s then 1 else 0) c =
      (Quire.Model.ofCoefficient format
        (q.coefficient + if s then -(c : Int) else (c : Int))).toNatBits := by
  obtain ⟨hkey, hkeyPos, hkeyLt⟩ := quire_key q hq
  have hpos := Nat.two_pow_pos (Quire.width format - 1)
  unfold quireAccumulate
  kernel_notation
  simp only [quireNar_eq, Bool.and_eq_true, Nat.ble_eq, Nat.pow_one,
    Nat.mul_comm (2 ^ (Quire.width format - 1)) 2]
  generalize (q.toNatBits + 2 ^ (Quire.width format - 1)) % (2 * 2 ^ (Quire.width format - 1)) =
    key at hkey hkeyPos hkeyLt ⊢
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [toNatBits_ofCoefficient (q.coefficient + (c : Int))
      (key + 2 ^ (Quire.width format - 1) + c) (by omega)]
    generalize 2 ^ (Quire.width format - 1) = H at hpos ⊢
    by_cases h : H + 1 ≤ key + H + c ∧ key + H + c + 1 ≤ 3 * H
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  · simp only [↓reduceIte, Nat.one_ne_zero]
    by_cases hc : c ≤ key + 2 ^ (Quire.width format - 1)
    · rw [toNatBits_ofCoefficient (q.coefficient + -(c : Int))
        (key + 2 ^ (Quire.width format - 1) - c) (by omega)]
      generalize 2 ^ (Quire.width format - 1) = H at hpos hc ⊢
      by_cases h : H + 1 ≤ key + H - c ∧ key + H - c + 1 ≤ 3 * H
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
    · have hnot : ¬Quire.Model.OrdinaryCoefficient format (q.coefficient + -(c : Int)) := by
        rw [Quire.Model.OrdinaryCoefficient, FixedInt.minValue_eq (Quire.width_pos format)]
        have hcast : ((2 : Int) ^ (Quire.width format - 1)) =
            ((2 ^ (Quire.width format - 1) : Nat) : Int) := by push_cast; rfl
        rw [hcast]
        omega
      rw [Quire.Model.ofCoefficient_eq_nar_of_not_ordinary hnot, quire_nar_toNatBits]
      generalize 2 ^ (Quire.width format - 1) = H at hpos hc ⊢
      rw [ite_eq_right (by omega)]

/-- Checking the coefficient of an ordinary quire returns the quire. -/
theorem ofCoefficient_coefficient (q : Quire.Model format) (hq : q.isNaR = false) :
    Quire.Model.ofCoefficient format q.coefficient = q := by
  unfold Quire.Model.ofCoefficient
  rw [ite_eq_left ((Quire.Model.ordinaryCoefficient_iff_isNaR_eq_false q).2 hq)]
  cases q
  simp [Quire.Model.coefficient, FixedInt.ofInt_toInt]

/-- The quire scale exponent in terms of the payload width. -/
theorem scaleExponent_eq (format : Format) :
    Quire.scaleExponent format = 16 - 8 * ((format.payloadBits + 1 : Nat) : Int) := by
  unfold Quire.scaleExponent
  rw [bits_eq]
  rfl

/-- The exponent of the smallest positive posit is at least the quire scale exponent, and twice
it is exactly that exponent. -/
theorem minPositive_exponent (format : Format) :
    (DyadicRounding.minPositive format).exponent =
      -(4 * ((format.payloadBits - 1 : Nat) : Int)) := by
  rw [DyadicRounding.minPositive_eq_fields]
  rfl

/--
Posit Standard (2022), §5.11: adding a dyadic increment whose quire coefficient is
`(-1) ^ s * c` to an ordinary quire is `quireAccumulate` on the word, for every width.
-/
theorem addDyadic_eq (acc : Quire.Model format) (d : FloatLib.Numerics.Dyadic) (s : Bool)
    (c : Nat) (hacc : acc.isNaR = false) (hscale : Quire.scaleExponent format ≤ d.exponent)
    (hcoef : Quire.Model.coefficientOfDyadic format d = if s then -(c : Int) else (c : Int)) :
    (Quire.Model.addDyadic acc d).toNatBits =
      quireAccumulate format.payloadBits acc.toNatBits (if s then 1 else 0) c := by
  unfold Quire.Model.addDyadic
  rw [ite_eq_right (by simp [hacc]), ite_eq_right (by omega), hcoef,
    quireAccumulate_eq acc hacc]

/-- The quire coefficient of the dyadic of a posit word, with an optional sign flip. -/
theorem coefficient_fields (x : Model format) (flip : Bool) :
    Quire.Model.coefficientOfDyadic format (if flip then (fields x).neg else fields x) =
      if (Bool.xor x.signBit flip) then
        -(((significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits) *
          2 ^ (exponent format.payloadBits 2 x.magnitudeBits
              (tailLength format.payloadBits x.magnitudeBits) + 8 * (format.payloadBits + 1) -
            (bias format.payloadBits 2 + 16)) : Nat)) : Int)
      else
        (((significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits) *
          2 ^ (exponent format.payloadBits 2 x.magnitudeBits
              (tailLength format.payloadBits x.magnitudeBits) + 8 * (format.payloadBits + 1) -
            (bias format.payloadBits 2 + 16)) : Nat)) : Int) := by
  have hshift : Int.toNat (((exponent format.payloadBits 2 x.magnitudeBits
        (tailLength format.payloadBits x.magnitudeBits) : Nat) : Int) -
        ((bias format.payloadBits 2 : Nat) : Int) - Quire.scaleExponent format) =
      exponent format.payloadBits 2 x.magnitudeBits
          (tailLength format.payloadBits x.magnitudeBits) + 8 * (format.payloadBits + 1) -
        (bias format.payloadBits 2 + 16) := by
    rw [scaleExponent_eq]
    omega
  cases flip <;> cases hs : x.signBit <;>
    simp [Quire.Model.coefficientOfDyadic, FloatLib.Numerics.Dyadic.signedSignificand, fields,
      hs, hshift]

/-- The exponent of the dyadic of a posit word is at least the exponent of the smallest positive
posit. -/
theorem minPositive_le_fields (x : Model format) (hnar : x ≠ Model.nar format)
    (hzero : x ≠ Model.zero format) :
    (DyadicRounding.minPositive format).exponent ≤ (fields x).exponent :=
  Quire.Model.minPositive_exponent_le_exponent_of_toDyadic?_eq_some x (fields x)
    (toDyadic?_eq x hnar hzero)

/-! ## Accumulation -/

/-- The exclusive or of two sign bits, as numbers. -/
theorem xor_sign (a b : Bool) :
    Nat.xor (if a = true then 1 else 0) (if b = true then 1 else 0) =
      if (Bool.xor a b) = true then 1 else 0 := by
  cases a <;> cases b <;> rfl

/-- A word other than NaR decodes to a dyadic. -/
theorem exists_toDyadic? (x : Model format) (hnar : x ≠ Model.nar format) :
    ∃ d, x.toDyadic? = some d := by
  by_cases hzero : x = Model.zero format
  · exact ⟨_, hzero ▸ toDyadic?_zero format⟩
  · exact ⟨_, toDyadic?_eq x hnar hzero⟩

/-- The quire scale exponent is at most twice the exponent of the smallest positive posit, which
is at most that exponent. -/
theorem scaleExponent_le (format : Format) :
    Quire.scaleExponent format = 2 * (DyadicRounding.minPositive format).exponent ∧
      (DyadicRounding.minPositive format).exponent ≤ 0 := by
  have hp := format.payloadBits_pos
  rw [scaleExponent_eq, minPositive_exponent]
  omega

/-- Adding a zero increment at or above the quire scale to an ordinary quire returns it. -/
theorem addDyadic_zero (acc : Quire.Model format) (d : FloatLib.Numerics.Dyadic)
    (hacc : acc.isNaR = false) (hscale : Quire.scaleExponent format ≤ d.exponent)
    (hzero : d.significand = 0) : Quire.Model.addDyadic acc d = acc := by
  have hcoef : Quire.Model.coefficientOfDyadic format d = 0 := by
    cases hn : d.negative <;>
      simp [Quire.Model.coefficientOfDyadic, FloatLib.Numerics.Dyadic.signedSignificand, hn, hzero]
  unfold Quire.Model.addDyadic
  rw [ite_eq_right (by simp [hacc]), ite_eq_right (by omega), hcoef, Int.add_zero,
    ofCoefficient_coefficient acc hacc]

/--
Posit Standard (2022), §5.11: `quireAddPosit` on the words of a quire and a posit is the word of
the quire plus the posit (`flip = false`, `qAddP`) or minus it (`flip = true`, `qSubP`), for
every width and all operands.
-/
theorem quireAddPosit_eq (acc : Quire.Model format) (x : Model format) (flip : Bool) :
    quireAddPosit format.payloadBits acc.toNatBits x.toNatBits (if flip then 1 else 0) =
      (match x.toDyadic? with
        | some d => Quire.Model.addDyadic acc (if flip then d.neg else d)
        | none => Quire.Model.nar format).toNatBits := by
  obtain ⟨hscale, hminPos⟩ := scaleExponent_le format
  unfold quireAddPosit
  simp only [beq_quireNar, beq_nar, beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite
    Iff.rfl), Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : x = Model.nar format
  · subst hx
    simp [quireNar_eq, quire_nar_toNatBits]
  by_cases hacc : acc.isNaR = true
  · obtain ⟨d, hd⟩ := exists_toDyadic? x hx
    simp [hd, hacc, Quire.Model.addDyadic, quireNar_eq, quire_nar_toNatBits]
  have hacc' : acc.isNaR = false := Bool.eq_false_of_not_eq_true hacc
  rw [ite_eq_right (by tauto)]
  by_cases hx0 : x = Model.zero format
  · subst hx0
    rw [ite_eq_left rfl, toDyadic?_zero]
    change _ = (Quire.Model.addDyadic acc _).toNatBits
    rw [addDyadic_zero acc _ hacc' (by cases flip <;> simp <;> omega) (by cases flip <;> rfl)]
  rw [ite_eq_right hx0, toDyadic?_eq x hx hx0]
  change _ = (Quire.Model.addDyadic acc _).toNatBits
  have hexp : (if flip then (fields x).neg else fields x).exponent = (fields x).exponent := by
    cases flip <;> rfl
  have hmin := minPositive_le_fields x hx hx0
  rw [addDyadic_eq acc _ (Bool.xor x.signBit flip) _ hacc' (by omega) (coefficient_fields x flip)]
  simp only [magnitude_eq, sign_eq, xor_sign]
  kernel_notation

/-- The quire coefficient of the product of the dyadics of two posit words, with an optional
sign flip. -/
theorem coefficient_mul_fields (x y : Model format) (flip : Bool) :
    Quire.Model.coefficientOfDyadic format
        (if flip then (FloatLib.Numerics.Dyadic.mul (fields x) (fields y)).neg
          else FloatLib.Numerics.Dyadic.mul (fields x) (fields y)) =
      if (Bool.xor (Bool.xor x.signBit y.signBit) flip) then
        -(((significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits) *
            significand 2 y.magnitudeBits (tailLength format.payloadBits y.magnitudeBits) *
          2 ^ (exponent format.payloadBits 2 x.magnitudeBits
                (tailLength format.payloadBits x.magnitudeBits) +
              exponent format.payloadBits 2 y.magnitudeBits
                (tailLength format.payloadBits y.magnitudeBits) + 8 * (format.payloadBits + 1) -
            (2 * bias format.payloadBits 2 + 16)) : Nat)) : Int)
      else
        (((significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits) *
            significand 2 y.magnitudeBits (tailLength format.payloadBits y.magnitudeBits) *
          2 ^ (exponent format.payloadBits 2 x.magnitudeBits
                (tailLength format.payloadBits x.magnitudeBits) +
              exponent format.payloadBits 2 y.magnitudeBits
                (tailLength format.payloadBits y.magnitudeBits) + 8 * (format.payloadBits + 1) -
            (2 * bias format.payloadBits 2 + 16)) : Nat)) : Int) := by
  have hshift : Int.toNat (((exponent format.payloadBits 2 x.magnitudeBits
        (tailLength format.payloadBits x.magnitudeBits) : Nat) : Int) -
        ((bias format.payloadBits 2 : Nat) : Int) +
        (((exponent format.payloadBits 2 y.magnitudeBits
          (tailLength format.payloadBits y.magnitudeBits) : Nat) : Int) -
          ((bias format.payloadBits 2 : Nat) : Int)) - Quire.scaleExponent format) =
      exponent format.payloadBits 2 x.magnitudeBits
            (tailLength format.payloadBits x.magnitudeBits) +
          exponent format.payloadBits 2 y.magnitudeBits
            (tailLength format.payloadBits y.magnitudeBits) + 8 * (format.payloadBits + 1) -
        (2 * bias format.payloadBits 2 + 16) := by
    rw [scaleExponent_eq]
    omega
  cases flip <;> cases hsx : x.signBit <;> cases hsy : y.signBit <;>
    simp [Quire.Model.coefficientOfDyadic, FloatLib.Numerics.Dyadic.signedSignificand,
      FloatLib.Numerics.Dyadic.mul, FloatLib.Numerics.Dyadic.mulFields, fields, hsx, hsy, hshift]

/--
Posit Standard (2022), §5.11: `quireAddProduct` on the words of a quire and two posits is the
word of the quire plus their exact product (`flip = false`, `qMulAdd`) or minus it
(`flip = true`, `qMulSub`), for every width and all operands.
-/
theorem quireAddProduct_eq (acc : Quire.Model format) (x y : Model format) (flip : Bool) :
    quireAddProduct format.payloadBits acc.toNatBits x.toNatBits y.toNatBits
        (if flip then 1 else 0) =
      (match x.toDyadic?, y.toDyadic? with
        | some dx, some dy =>
            Quire.Model.addDyadic acc
              (if flip then (FloatLib.Numerics.Dyadic.mul dx dy).neg
                else FloatLib.Numerics.Dyadic.mul dx dy)
        | _, _ => Quire.Model.nar format).toNatBits := by
  obtain ⟨hscale, _⟩ := scaleExponent_le format
  unfold quireAddProduct
  simp only [beq_quireNar, beq_nar, beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite
    Iff.rfl), Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : x = Model.nar format
  · subst hx
    simp [quireNar_eq, quire_nar_toNatBits]
  by_cases hy : y = Model.nar format
  · subst hy
    obtain ⟨dx, hdx⟩ := exists_toDyadic? x hx
    simp [hdx, quireNar_eq, quire_nar_toNatBits]
  obtain ⟨dx, hdx⟩ := exists_toDyadic? x hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic? y hy
  have hmx := Quire.Model.minPositive_exponent_le_exponent_of_toDyadic?_eq_some x dx hdx
  have hmy := Quire.Model.minPositive_exponent_le_exponent_of_toDyadic?_eq_some y dy hdy
  have hexp : (if flip then (FloatLib.Numerics.Dyadic.mul dx dy).neg
      else FloatLib.Numerics.Dyadic.mul dx dy).exponent = dx.exponent + dy.exponent := by
    cases flip <;> rfl
  by_cases hacc : acc.isNaR = true
  · simp [hdx, hdy, hacc, Quire.Model.addDyadic, quireNar_eq, quire_nar_toNatBits]
  have hacc' : acc.isNaR = false := Bool.eq_false_of_not_eq_true hacc
  rw [ite_eq_right (by tauto), hdx, hdy]
  change _ = (Quire.Model.addDyadic acc _).toNatBits
  by_cases h0 : x = Model.zero format ∨ y = Model.zero format
  · rw [ite_eq_left h0, addDyadic_zero acc _ hacc' (by omega)]
    have hsig : (FloatLib.Numerics.Dyadic.mul dx dy).significand = 0 := by
      rcases h0 with h0 | h0
      · subst h0
        rw [toDyadic?_zero] at hdx
        obtain rfl := Option.some.inj hdx
        change 0 * _ = 0
        exact Nat.zero_mul _
      · subst h0
        rw [toDyadic?_zero] at hdy
        obtain rfl := Option.some.inj hdy
        change _ * 0 = 0
        exact Nat.mul_zero _
    cases flip
    · exact hsig
    · exact hsig
  have hx0 : x ≠ Model.zero format := fun h => h0 (Or.inl h)
  have hy0 : y ≠ Model.zero format := fun h => h0 (Or.inr h)
  rw [toDyadic?_eq x hx hx0] at hdx
  rw [toDyadic?_eq y hy hy0] at hdy
  obtain rfl := Option.some.inj hdx
  obtain rfl := Option.some.inj hdy
  rw [ite_eq_right h0, addDyadic_eq acc _ (Bool.xor (Bool.xor x.signBit y.signBit) flip) _ hacc'
    (by omega) (coefficient_mul_fields x y flip)]
  simp only [magnitude_eq, sign_eq, xor_sign]
  kernel_notation

/--
Posit Standard (2022), §5.11: `quireAddQuire` on two quire words is the word of their checked
sum (`flip = false`, `qAddQ`) or difference (`flip = true`, `qSubQ`), for every width.
-/
theorem quireAddQuire_eq (q r : Quire.Model format) (flip : Bool) :
    quireAddQuire format.payloadBits q.toNatBits r.toNatBits (if flip then 1 else 0) =
      (if flip then Quire.Model.qSubQ q r else Quire.Model.qAddQ q r).toNatBits := by
  have hrlt := quire_toNatBits_lt r
  have hcoef := coefficient_eq r
  unfold quireAddQuire
  simp only [beq_quireNar]
  kernel_notation
  simp only [quireNar_eq, Nat.pow_one, Nat.mul_comm (2 ^ (Quire.width format - 1)) 2,
    Bool.or_eq_true]
  by_cases hnar : q.isNaR = true ∨ r.isNaR = true
  · have hor : (q.isNaR || r.isNaR) = true := Bool.or_eq_true _ _ ▸ hnar
    rw [ite_eq_left hnar]
    cases flip
    · change _ = (if (q.isNaR || r.isNaR) = true then Quire.Model.nar format else _).toNatBits
      rw [ite_eq_left hor, quire_nar_toNatBits]
    · change _ = (if (q.isNaR || r.isNaR) = true then Quire.Model.nar format else _).toNatBits
      rw [ite_eq_left hor, quire_nar_toNatBits]
  have hq : q.isNaR = false := by
    cases h : q.isNaR
    · rfl
    · exact absurd (Or.inl h) hnar
  have hr : r.isNaR = false := by
    cases h : r.isNaR
    · rfl
    · exact absurd (Or.inr h) hnar
  have hor : ¬((q.isNaR || r.isNaR) = true) := by simp [hq, hr]
  rw [ite_eq_right hnar]
  by_cases hneg : 2 ^ (Quire.width format - 1) ≤ r.toNatBits
  · rw [ite_eq_left hneg]
    rw [ite_eq_right (by omega)] at hcoef
    cases flip
    · have h := quireAccumulate_eq q hq true (2 * 2 ^ (Quire.width format - 1) - r.toNatBits)
      simp only [ite_true] at h
      change quireAccumulate _ _ (1 - 0) _ =
        (if (q.isNaR || r.isNaR) = true then Quire.Model.nar format else _).toNatBits
      rw [ite_eq_right hor, h, hcoef]
      congr 2
      omega
    · have h := quireAccumulate_eq q hq false (2 * 2 ^ (Quire.width format - 1) - r.toNatBits)
      simp only [Bool.false_eq_true, ite_false] at h
      change quireAccumulate _ _ (1 - 1) _ =
        (if (q.isNaR || r.isNaR) = true then Quire.Model.nar format else _).toNatBits
      rw [ite_eq_right hor, h, hcoef]
      congr 2
      omega
  · rw [ite_eq_right hneg]
    rw [ite_eq_left (by omega)] at hcoef
    cases flip
    · have h := quireAccumulate_eq q hq false r.toNatBits
      simp only [Bool.false_eq_true, ite_false] at h
      change quireAccumulate _ _ 0 _ =
        (if (q.isNaR || r.isNaR) = true then Quire.Model.nar format else _).toNatBits
      rw [ite_eq_right hor, h, hcoef]
    · have h := quireAccumulate_eq q hq true r.toNatBits
      simp only [ite_true] at h
      change quireAccumulate _ _ 1 _ =
        (if (q.isNaR || r.isNaR) = true then Quire.Model.nar format else _).toNatBits
      rw [ite_eq_right hor, h, hcoef]
      rfl

/-- Posit Standard (2022), §5.11: `quireNeg` on a quire word is the word of the negated quire,
NaR for NaR, for every width. -/
theorem quireNeg_eq (q : Quire.Model format) :
    quireNeg format.payloadBits q.toNatBits = (Quire.Model.qNegate q).toNatBits := by
  have hlt := quire_toNatBits_lt q
  have hcoef := coefficient_eq q
  have hpos := Nat.two_pow_pos (Quire.width format - 1)
  unfold quireNeg Quire.Model.qNegate
  kernel_notation
  rw [quireWidth_eq, two_pow_width]
  by_cases hnar : q.isNaR = true
  · have hword := (quire_eq_nar_iff q).1 ((Quire.Model.isNaR_eq_true_iff q).1 hnar)
    have hsubH : 2 * 2 ^ (Quire.width format - 1) - 2 ^ (Quire.width format - 1) =
        2 ^ (Quire.width format - 1) := by omega
    rw [ite_eq_left hnar, quire_nar_toNatBits, hword, hsubH, Nat.mod_eq_of_lt (by omega)]
  · have hne : q.toNatBits ≠ 2 ^ (Quire.width format - 1) := fun h =>
      hnar ((Quire.Model.isNaR_eq_true_iff q).2 ((quire_eq_nar_iff q).2 h))
    rw [ite_eq_right hnar]
    by_cases hsmall : q.toNatBits < 2 ^ (Quire.width format - 1)
    · rw [ite_eq_left hsmall] at hcoef
      rw [toNatBits_ofCoefficient (-q.coefficient)
        (2 * 2 ^ (Quire.width format - 1) - q.toNatBits) (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right hsmall] at hcoef
      rw [toNatBits_ofCoefficient (-q.coefficient)
        (4 * 2 ^ (Quire.width format - 1) - q.toNatBits) (by omega), ite_eq_left (by omega),
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- Posit Standard (2022), §5.11: `quireAbs` on a quire word is the word of the absolute value,
NaR for NaR, for every width. -/
theorem quireAbs_eq (q : Quire.Model format) :
    quireAbs format.payloadBits q.toNatBits = (Quire.Model.qAbs q).toNatBits := by
  have hcoef := coefficient_eq q
  have hlt := quire_toNatBits_lt q
  unfold quireAbs Quire.Model.qAbs
  simp only [(FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl), quireNar_eq, Nat.ble_eq]
  by_cases hnar : q.isNaR = true
  · have hword := (quire_eq_nar_iff q).1 ((Quire.Model.isNaR_eq_true_iff q).1 hnar)
    have hneg := quireNeg_eq q
    rw [Quire.Model.qNegate, ite_eq_left hnar] at hneg
    rw [ite_eq_left hnar, ite_eq_left (by omega), hneg]
  · rw [ite_eq_right hnar]
    by_cases hsmall : q.toNatBits < 2 ^ (Quire.width format - 1)
    · rw [ite_eq_left hsmall] at hcoef
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right hsmall] at hcoef
      rw [ite_eq_left (by omega), ite_eq_left (by omega), quireNeg_eq]

/-- Posit Standard (2022), §5.11: the conversion of a posit into its quire is the accumulation
of the posit into the zero quire. -/
theorem pToQ_eq_qAddP (x : Model format) :
    Quire.Model.pToQ x = Quire.Model.qAddP (Quire.Model.zero format) x := by
  obtain ⟨hscale, hminPos⟩ := scaleExponent_le format
  unfold Quire.Model.pToQ Quire.Model.qAddP
  cases hd : x.toDyadic? with
  | none => rfl
  | some d =>
      have hm := Quire.Model.minPositive_exponent_le_exponent_of_toDyadic?_eq_some x d hd
      simp only [Quire.Model.addDyadic, Quire.Model.isNaR_zero, Bool.false_eq_true, ite_false,
        Quire.Model.coefficient_zero, Int.zero_add]
      rw [ite_eq_right (by omega)]

/-- The word of the zero quire is zero. -/
theorem quire_zero_toNatBits (format : Format) : (Quire.Model.zero format).toNatBits = 0 := by
  change (BitVec.ofInt (Quire.width format) 0).toNat = 0
  simp

/--
Posit Standard (2022), §5.11: `quireRound` on a quire word is the encoding of the posit nearest
to the quire by §4.1, NaR for NaR, for every width.
-/
theorem quireRound_eq (q : Quire.Model format) :
    quireRound format.payloadBits q.toNatBits = (Quire.Model.qToP q).toNatBits := by
  have hlt := quire_toNatBits_lt q
  have hcoef := coefficient_eq q
  have hp := format.payloadBits_pos
  unfold quireRound Quire.Model.qToP Quire.Model.toDyadic?
  simp only [beq_quireNar, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl)]
  have hble : (Nat.ble (quireNar format.payloadBits) q.toNatBits = true) =
      (2 ^ (Quire.width format - 1) ≤ q.toNatBits) := by
    rw [quireNar_eq, Nat.ble_eq]
  have hsub : Nat.shiftLeft (quireNar format.payloadBits) 1 =
      2 * 2 ^ (Quire.width format - 1) := by
    rw [quireNar_eq]
    kernel_notation
    omega
  simp only [hble, hsub, Nat.beq_eq]
  by_cases hnar : q.isNaR = true
  · simp [hnar, nar_eq]
  have hne : q.toNatBits ≠ 2 ^ (Quire.width format - 1) := fun h =>
    hnar ((Quire.Model.isNaR_eq_true_iff q).2 ((quire_eq_nar_iff q).2 h))
  simp only [hnar, Bool.false_eq_true, ite_false]
  rw [← DirectDyadicPacking.round_eq_dyadic]
  by_cases hzero : q.toNatBits = 0
  · rw [ite_eq_left hzero]
    rw [ite_eq_left (by omega)] at hcoef
    have hc : q.coefficient = 0 := by omega
    rw [hc]
    exact (round_zero format _ _).symm
  rw [ite_eq_right hzero]
  have hE : ((16 : Nat) : Int) = (FloatLib.Numerics.Dyadic.ofScaledInt q.coefficient
      (Quire.scaleExponent format)).exponent +
        4 * ((Nat.mul 2 (Nat.succ format.payloadBits) : Nat) : Int) := by
    change _ = Quire.scaleExponent format + _
    rw [scaleExponent_eq]
    kernel_notation
    push_cast
    omega
  by_cases hsmall : q.toNatBits < 2 ^ (Quire.width format - 1)
  · rw [ite_eq_left hsmall] at hcoef
    rw [ite_eq_right (by omega), round_eq format _ 16 _ (by
      change q.coefficient.natAbs ≠ 0
      omega) hE]
    have hneg : (FloatLib.Numerics.Dyadic.ofScaledInt q.coefficient
        (Quire.scaleExponent format)).negative = false := by
      change decide (q.coefficient < 0) = false
      exact decide_eq_false (by omega)
    have hsig : (FloatLib.Numerics.Dyadic.ofScaledInt q.coefficient
        (Quire.scaleExponent format)).significand = q.toNatBits := by
      change q.coefficient.natAbs = _
      omega
    rw [hneg, hsig]
    exact (withSign_eq _ false _).symm
  · rw [ite_eq_right hsmall] at hcoef
    rw [ite_eq_left (by omega), round_eq format _ 16 _ (by
      change q.coefficient.natAbs ≠ 0
      omega) hE]
    have hneg : (FloatLib.Numerics.Dyadic.ofScaledInt q.coefficient
        (Quire.scaleExponent format)).negative = true := by
      change decide (q.coefficient < 0) = true
      exact decide_eq_true (by omega)
    have hsig : (FloatLib.Numerics.Dyadic.ofScaledInt q.coefficient
        (Quire.scaleExponent format)).significand =
          2 * 2 ^ (Quire.width format - 1) - q.toNatBits := by
      change q.coefficient.natAbs = _
      omega
    rw [hneg, hsig]
    rfl

/-! ## Kernel rules -/

/-- The word of the quire that stores `a` is `a` reduced to the quire width, in the form that
the kernel computes. -/
@[kernel_optimize] theorem quire_toNatBits_ofNatBits_kernel (a : Nat) :
    (Quire.Model.ofNatBits format a).toNatBits = Nat.mod a (Nat.pow 2 (Quire.width format)) :=
  BitVec.toNat_ofNat ..

/-- Posit Standard (2022), §5.11: `qAddP` is the flat accumulation on the two words. -/
@[kernel_optimize (cost := 200)] theorem qAddP_eq_kernel (acc : Quire.Model format)
    (x : Model format) :
    Quire.Model.qAddP acc x = Quire.Model.ofNatBits format
      (Flat.quireAddPosit format.payloadBits acc.toNatBits x.toNatBits 0) := by
  have h := quireAddPosit_eq acc x false
  simp only [Bool.false_eq_true, ite_false] at h
  rw [Flat.quireAddPosit_eq, h, Quire.Model.ofNatBits_toNatBits]
  rfl

/-- Posit Standard (2022), §5.11: `qSubP` is the flat accumulation with the sign flipped. -/
@[kernel_optimize (cost := 200)] theorem qSubP_eq_kernel (acc : Quire.Model format)
    (x : Model format) :
    Quire.Model.qSubP acc x = Quire.Model.ofNatBits format
      (Flat.quireAddPosit format.payloadBits acc.toNatBits x.toNatBits 1) := by
  have h := quireAddPosit_eq acc x true
  simp only [ite_true] at h
  rw [Flat.quireAddPosit_eq, h, Quire.Model.ofNatBits_toNatBits]
  rfl

/-- Posit Standard (2022), §5.11: `pToQ` is the flat accumulation into the zero quire. -/
@[kernel_optimize (cost := 200)] theorem pToQ_eq_kernel (x : Model format) :
    Quire.Model.pToQ x = Quire.Model.ofNatBits format
      (Flat.quireAddPosit format.payloadBits 0 x.toNatBits 0) := by
  rw [pToQ_eq_qAddP, qAddP_eq_kernel, quire_zero_toNatBits]

/-- Posit Standard (2022), §5.11: `qMulAdd` is the flat product accumulation on the three
words. -/
@[kernel_optimize (cost := 260)] theorem qMulAdd_eq_kernel (acc : Quire.Model format)
    (x y : Model format) :
    Quire.Model.qMulAdd acc x y = Quire.Model.ofNatBits format
      (Flat.quireAddProduct format.payloadBits acc.toNatBits x.toNatBits y.toNatBits 0) := by
  have h := quireAddProduct_eq acc x y false
  simp only [Bool.false_eq_true, ite_false] at h
  rw [Flat.quireAddProduct_eq, h, Quire.Model.ofNatBits_toNatBits]
  rfl

/-- Posit Standard (2022), §5.11: `qMulSub` is the flat product accumulation with the sign
flipped. -/
@[kernel_optimize (cost := 260)] theorem qMulSub_eq_kernel (acc : Quire.Model format)
    (x y : Model format) :
    Quire.Model.qMulSub acc x y = Quire.Model.ofNatBits format
      (Flat.quireAddProduct format.payloadBits acc.toNatBits x.toNatBits y.toNatBits 1) := by
  have h := quireAddProduct_eq acc x y true
  simp only [ite_true] at h
  rw [Flat.quireAddProduct_eq, h, Quire.Model.ofNatBits_toNatBits]
  rfl

/-- Posit Standard (2022), §5.11: `qAddQ` is the flat quire addition on the two words. -/
@[kernel_optimize (cost := 60)] theorem qAddQ_eq_kernel (q r : Quire.Model format) :
    Quire.Model.qAddQ q r = Quire.Model.ofNatBits format
      (Flat.quireAddQuire format.payloadBits q.toNatBits r.toNatBits 0) := by
  have h := quireAddQuire_eq q r false
  simp only [Bool.false_eq_true, ite_false] at h
  rw [Flat.quireAddQuire_eq, h, Quire.Model.ofNatBits_toNatBits]

/-- Posit Standard (2022), §5.11: `qSubQ` is the flat quire addition with the sign flipped. -/
@[kernel_optimize (cost := 60)] theorem qSubQ_eq_kernel (q r : Quire.Model format) :
    Quire.Model.qSubQ q r = Quire.Model.ofNatBits format
      (Flat.quireAddQuire format.payloadBits q.toNatBits r.toNatBits 1) := by
  have h := quireAddQuire_eq q r true
  simp only [ite_true] at h
  rw [Flat.quireAddQuire_eq, h, Quire.Model.ofNatBits_toNatBits]

/-- Posit Standard (2022), §5.11: `qNegate` is the two's complement of the word. -/
@[kernel_optimize (cost := 20)] theorem qNegate_eq_kernel (q : Quire.Model format) :
    Quire.Model.qNegate q =
      Quire.Model.ofNatBits format (quireNeg format.payloadBits q.toNatBits) := by
  rw [quireNeg_eq, Quire.Model.ofNatBits_toNatBits]

/-- Posit Standard (2022), §5.11: `qAbs` is the word, or its two's complement from the sign bit
on. -/
@[kernel_optimize (cost := 30)] theorem qAbs_eq_kernel (q : Quire.Model format) :
    Quire.Model.qAbs q =
      Quire.Model.ofNatBits format (quireAbs format.payloadBits q.toNatBits) := by
  rw [quireAbs_eq, Quire.Model.ofNatBits_toNatBits]

/-- Posit Standard (2022), §5.11: `qToP` is the flat rounding of the quire word. -/
@[kernel_optimize (cost := 160)] theorem qToP_eq_kernel (q : Quire.Model format) :
    Quire.Model.qToP q = Model.ofNatBits (Flat.quireRound format.payloadBits q.toNatBits) := by
  rw [Flat.quireRound_eq, quireRound_eq, ofNatBits_toNatBits]

end FloatLib.Floats.Formats.Posit.KernelPath
