/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Lean
public import FloatLib.Numerics.Exact.Dyadic.Basic
public import FloatLib.Numerics.Quantization.Deterministic
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Optimized

/-!
# Exact dyadic decoding primitives

Finite binary interchange values decode exactly to a sign, natural significand, and integral
power-of-two exponent. This module defines that bridge and the exact comparison used by
arithmetic, conversions, and rounding.

The decoding layer is intentionally independent of any arithmetic operation. Addition,
multiplication, FMA, conversion, and directed rounding can all share the same exact domain and
prove their own final packing step.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics

/-- Exact negation with the zero convention selected by the destination format. -/
@[inline] def negDyadic (fmt : FloatFormat) (value : Numerics.Dyadic) : Numerics.Dyadic :=
  if value.significand == 0 && !fmt.supportsSignedZero then
    Numerics.Dyadic.zero
  else
    value.neg

/-- Exact dyadic value represented by a finite value in Lean's logical float model. -/
def unpackedToDyadic? : Float.Model.UnpackedFloat → Option Numerics.Dyadic
  | .notANumber | .infinity _ => none
  | .zero sign =>
      some { negative := modelSignBit sign, significand := 0, exponent := 0 }
  | .finite sign mantissa exponent _ =>
      some
        { negative := modelSignBit sign
          significand := mantissa
          exponent }

/-- `2^k` as a `Nat`. -/
@[inline] def pow2 (k : Nat) : Nat :=
  Nat.shiftLeft 1 k

/-- The executable shift definition of a power of two agrees with natural exponentiation. -/
theorem pow2_eq_two_pow (k : Nat) : pow2 k = 2 ^ k := by
  simp [pow2, Nat.shiftLeft_eq]

/--
Exact comparison of two dyadics by aligning their exponents and comparing signed mantissas.

The alignment shift is the full exponent difference, so this form is only cheap when the
exponents are close. `cmpDyadic` decides every other case first and uses this form only when the
leading bit positions coincide.
-/
def cmpDyadicAligned (a b : Numerics.Dyadic) : Ordering :=
  if a.significand == 0 && b.significand == 0 then
    .eq
  else
    let e : Int := if a.exponent ≤ b.exponent then a.exponent else b.exponent
    let shA : Nat := Int.toNat (a.exponent - e)
    let shB : Nat := Int.toNat (b.exponent - e)
    let aNat : Nat := Nat.shiftLeft a.significand shA
    let bNat : Nat := Nat.shiftLeft b.significand shB
    let aInt : Int := if a.negative then -(Int.ofNat aNat) else Int.ofNat aNat
    let bInt : Int := if b.negative then -(Int.ofNat bNat) else Int.ofNat bNat
    compare aInt bInt

/--
Exact comparison of two dyadics.

Zero operands and opposite signs are decided directly. For nonzero operands of one sign, the
leading bit positions `log2 significand + exponent` decide the magnitude order unless they
coincide, and only then are the significands aligned. The alignment shift is therefore bounded by
the significand widths, not by the distance between the exponents.

This lives with the decoding primitives because finite-value comparison does not depend on any
rounding operation.
-/
def cmpDyadic (a b : Numerics.Dyadic) : Ordering :=
  if a.significand == 0 && b.significand == 0 then
    .eq
  else if a.significand == 0 then
    if b.negative then .gt else .lt
  else if b.significand == 0 then
    if a.negative then .lt else .gt
  else if a.negative != b.negative then
    if a.negative then .lt else .gt
  else
    let leadingA : Int := (a.significand.log2 : Int) + a.exponent
    let leadingB : Int := (b.significand.log2 : Int) + b.exponent
    if leadingA < leadingB then
      if a.negative then .gt else .lt
    else if leadingB < leadingA then
      if a.negative then .lt else .gt
    else
      cmpDyadicAligned a b

/-- A shifted significand lies strictly below the power of two after its leading bit. -/
private theorem shiftLeft_lt_two_pow_log2 (m k : Nat) :
    Nat.shiftLeft m k < 2 ^ (m.log2 + 1 + k) := by
  change m <<< k < _
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos k)

/-- A shifted nonzero significand is at least the power of two at its leading bit. -/
private theorem two_pow_log2_le_shiftLeft {m : Nat} (hm : m ≠ 0) (k : Nat) :
    2 ^ (m.log2 + k) ≤ Nat.shiftLeft m k := by
  change _ ≤ m <<< k
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_le_mul_right _ (Nat.log2_self_le hm)

/-- Aligned magnitudes are ordered by leading bit position when those positions differ. -/
private theorem shiftLeft_lt_of_leading_lt {a b : Nat} (hb : b ≠ 0) {i j : Nat}
    (hlead : a.log2 + i < b.log2 + j) :
    Nat.shiftLeft a i < Nat.shiftLeft b j := by
  have h1 := shiftLeft_lt_two_pow_log2 a i
  have h2 := two_pow_log2_le_shiftLeft hb j
  have h3 : 2 ^ (a.log2 + 1 + i) ≤ 2 ^ (b.log2 + j) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Shifting a zero significand leaves zero. -/
private theorem zero_shiftLeft' (k : Nat) : Nat.shiftLeft 0 k = 0 := by
  change 0 <<< k = 0
  simp

/-- Shifting a nonzero significand leaves it nonzero. -/
private theorem shiftLeft_pos {m : Nat} (hm : m ≠ 0) (k : Nat) : 0 < Nat.shiftLeft m k := by
  change 0 < m <<< k
  rw [Nat.shiftLeft_eq]
  exact Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.two_pow_pos k)

/-- The leading-position comparison agrees with exponent alignment for every operand pair. -/
theorem cmpDyadic_eq_cmpDyadicAligned (a b : Numerics.Dyadic) :
    cmpDyadic a b = cmpDyadicAligned a b := by
  obtain ⟨an, sa, ea⟩ := a
  obtain ⟨bn, sb, eb⟩ := b
  simp only [cmpDyadic, cmpDyadicAligned]
  generalize he : (if ea ≤ eb then ea else eb) = e
  have hea : e ≤ ea := by
    subst he; split <;> omega
  have heb : e ≤ eb := by
    subst he; split <;> omega
  have hlt : ∀ (x y : Nat) (ex ey : Int), y ≠ 0 → e ≤ ex → e ≤ ey →
      (x.log2 : Int) + ex < (y.log2 : Int) + ey →
      Nat.shiftLeft x (ex - e).toNat < Nat.shiftLeft y (ey - e).toNat := by
    intro x y ex ey hy hx' hy' hxy
    exact shiftLeft_lt_of_leading_lt hy (by omega)
  have hA0 : sa = 0 → Nat.shiftLeft sa (ea - e).toNat = 0 := fun h => h ▸ zero_shiftLeft' _
  have hB0 : sb = 0 → Nat.shiftLeft sb (eb - e).toNat = 0 := fun h => h ▸ zero_shiftLeft' _
  have hA := fun h => shiftLeft_pos (m := sa) h (ea - e).toNat
  have hB := fun h => shiftLeft_pos (m := sb) h (eb - e).toNat
  have hAB := hlt sa sb ea eb
  have hBA := hlt sb sa eb ea
  generalize Nat.shiftLeft sa (ea - e).toNat = A at *
  generalize Nat.shiftLeft sb (eb - e).toNat = B at *
  by_cases ha : sa = 0 <;> by_cases hb : sb = 0
  · simp [ha, hb]
  · have := hA0 ha
    have := hB hb
    cases an <;> cases bn <;> simp [ha, hb, compare, compareOfLessAndEq] <;>
      split_ifs <;> first | rfl | omega
  · have := hB0 hb
    have := hA ha
    cases an <;> cases bn <;> simp [ha, hb, compare, compareOfLessAndEq] <;>
      split_ifs <;> first | rfl | omega
  · have := hA ha
    have := hB hb
    have hAB := hAB hb hea heb
    have hBA := hBA ha heb hea
    cases an <;> cases bn <;>
      simp [ha, hb, compare, compareOfLessAndEq] <;>
      split_ifs <;> first | rfl | omega

/--
Decode an IEEE bit pattern into an exact dyadic.

- NaN / Inf → `none`
- ±0 → `mant = 0`, `exp = 0` (sign preserved)
- subnormal → `mant = frac`, `exp = ieeeMinSubnormalExponent fmt`
- normal → `mant = 2^fracWidth + frac`, `exp = e_biased - (bias + fracWidth)`

Every threshold is derived from `fmt`; no fixed-width constants are used.
-/
@[inline] def ieeeToDyadic? {fmt : FloatFormat} (x : Model fmt) : Option Numerics.Dyadic :=
  if IEEE.isNaN x || IEEE.isInf x then
    none
  else
    let s := signBit x
    let e := expField x
    let f := fracField x
    if e == 0 then
      if f == 0 then
        some { negative := s, significand := 0, exponent := 0 }
      else
        some
          { negative := s
            significand := f
            exponent := FloatFormat.ieeeMinSubnormalExponent fmt }
    else
      let significand := pow2 fmt.fracWidth + f
      let exp : Int :=
        Int.ofNat e - Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt)
      some { negative := s, significand, exponent := exp }

/--
Compiled IEEE finite decoder.

The storage word is converted to `Nat` once, then all three fields are extracted from that shared
value. The exponent field alone determines whether an IEEE encoding is exceptional, so the
decoder also avoids the repeated masks and shifts performed by `IEEE.isNaN` and `IEEE.isInf`.
-/
@[inline] def ieeeToDyadicImpl? {fmt : FloatFormat} (x : Model fmt) : Option Numerics.Dyadic :=
  let bits := x.toNatBits
  let e := (bits >>> fmt.fracWidth) &&& FloatFormat.expAllOnesNat fmt
  if e == FloatFormat.expAllOnesNat fmt then
    none
  else
    let s := bits.testBit (fmt.expWidth + fmt.fracWidth)
    let f := bits &&& FloatFormat.fracMaskNat fmt
    if e == 0 then
      if f == 0 then
        some { negative := s, significand := 0, exponent := 0 }
      else
        some
          { negative := s
            significand := f
            exponent := FloatFormat.ieeeMinSubnormalExponent fmt }
    else
      let significand := pow2 fmt.fracWidth + f
      let exp : Int :=
        Int.ofNat e - Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt)
      some { negative := s, significand, exponent := exp }

/-- The compiler uses the single-pass field decoder while proofs retain `ieeeToDyadic?`. -/
@[csimp] theorem toDyadic_eq_toDyadicImpl :
    @ieeeToDyadic? = @ieeeToDyadicImpl? := by
  funext fmt x
  change ieeeToDyadic? x =
    (let e := expFieldImpl x
     if e == FloatFormat.expAllOnesNat fmt then
       none
     else
       let s := signBitImpl x
       let f := fracFieldImpl x
       if e == 0 then
         if f == 0 then
           some { negative := s, significand := 0, exponent := 0 }
         else
           some
             { negative := s
               significand := f
               exponent := FloatFormat.ieeeMinSubnormalExponent fmt }
       else
         let significand := pow2 fmt.fracWidth + f
         let exp : Int :=
           Int.ofNat e - Int.ofNat (FloatFormat.ieeeNormalMantissaExpOffset fmt)
         some { negative := s, significand, exponent := exp })
  rw [← expField_eq_expFieldImpl_apply x, ← signBit_eq_signBitImpl_apply x,
    ← fracField_eq_fracFieldImpl_apply x]
  by_cases he : expField x = FloatFormat.expAllOnesNat fmt
  · simp [ieeeToDyadic?, IEEE.isNaN, IEEE.isInf, he]
  · simp [ieeeToDyadic?, IEEE.isNaN, IEEE.isInf, he]


end Model

end FloatLib.Floats.Formats.BinaryInterchange
