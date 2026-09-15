/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic
public import FloatLib.Numerics.Exact.Zero
public import Mathlib.Algebra.Order.Field.Basic
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Exact rationals with an IEEE sign

A rational number has no negative zero, but every IEEE binary format does. Converting a value
through `Rat` therefore forgets whether a zero was `-0` or `+0`. A cast or mixed-format
operation cannot recover that sign from the rational value alone.

`SignedRat` is a rational together with the sign bit an IEEE format would store for it. For a
nonzero value the sign bit is determined by the value, and the structure carries that fact as a
proof field, so two `SignedRat`s are equal exactly when their values and sign bits agree. Only a
zero has a free sign bit.

The arithmetic operations implement the IEEE sign rules for exact results. A product or quotient
has the exclusive-or of the operand signs. An exact zero sum is negative only when both operands
are negative, which is the round-to-nearest rule. Callers use `addWithCancellationSign` to choose
the sign of an exact cancellation for directed rounding.

Executable conversion uses this type as the exact domain of every binary destination. Rational
sources such as posits and fixed point enter through `ofRat`, and binary sources decode through
`ofDyadic`, which keeps the dyadic sign.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
An exact rational together with the IEEE sign bit of its zero.

`negative` is the sign bit. For a nonzero `value` it is forced to `decide (value < 0)`; for zero it
distinguishes `-0` from `+0`.
-/
structure SignedRat where
  /-- The exact rational value; zero for both signed zeros. -/
  value : Rat
  /-- The IEEE sign bit. -/
  negative : Bool
  /-- A nonzero value determines its sign bit. -/
  negative_eq_of_ne_zero : value ≠ 0 → negative = decide (value < 0)
  deriving DecidableEq

namespace SignedRat

/-- Two signed rationals are equal when their values and sign bits are equal. -/
@[ext] theorem ext {x y : SignedRat} (hvalue : x.value = y.value)
    (hnegative : x.negative = y.negative) : x = y := by
  cases x
  cases y
  cases hvalue
  cases hnegative
  rfl

/--
Numerical equality, ignoring the sign attached to zero.

Ordinary `==` remains structural, just like `=`. Use `sameValue` only when positive and negative
zero should represent the same rational number.
-/
@[inline] def sameValue (x y : SignedRat) : Bool :=
  x.value == y.value

/-- `sameValue` compares exactly the underlying rational values. -/
@[simp, grind =] theorem sameValue_eq_true_iff (x y : SignedRat) :
    sameValue x y = true ↔ x.value = y.value := by
  simp [sameValue]

/-- A negative zero prints as `-0`; every other value prints as its rational value. -/
protected def toString (x : SignedRat) : String :=
  if x.value = 0 ∧ x.negative then "-0" else toString x.value

instance : ToString SignedRat where
  toString := SignedRat.toString

instance : Repr SignedRat where
  reprPrec x _ := Std.Format.text (SignedRat.toString x)

/-! ## Constructors -/

/-- The signed rational of a rational; zero receives the positive sign. -/
@[inline] def ofRat (q : Rat) : SignedRat :=
  ⟨q, decide (q < 0), fun _ => rfl⟩

/-- `ofRat` keeps the rational value. -/
@[simp, grind =] theorem value_ofRat (q : Rat) : (ofRat q).value = q :=
  rfl

/-- `ofRat` marks exactly the negative rationals; zero is positive. -/
@[simp, grind =] theorem negative_ofRat (q : Rat) : (ofRat q).negative = decide (q < 0) :=
  rfl

/-- A nonzero signed rational is recovered from its value alone. -/
theorem ofRat_value_of_ne_zero {x : SignedRat} (hvalue : x.value ≠ 0) :
    ofRat x.value = x :=
  ext rfl (x.negative_eq_of_ne_zero hvalue).symm

/-- Negative zero, the value a signed rational adds to `Rat`. -/
def negZero : SignedRat :=
  ⟨0, true, fun h => absurd rfl h⟩

/-- Negative zero has value zero. -/
@[simp, grind =] theorem value_negZero : negZero.value = 0 :=
  rfl

/-- Negative zero carries the negative sign bit. -/
@[simp, grind =] theorem negative_negZero : negZero.negative = true :=
  rfl

instance : Zero SignedRat where
  zero := ofRat 0

/-- The zero of `SignedRat` has value zero. -/
@[simp, grind =] theorem value_zero : (0 : SignedRat).value = 0 :=
  rfl

/-- Both signed-zero representations are mathematical zero for checked exact arithmetic. -/
instance : ExactZero SignedRat where
  isZero value := value.value = 0
  zero_is_zero := value_zero
  decidableIsZero _ := inferInstance

/-- The generic executable zero test recognizes exactly the zero-valued signed rationals. -/
theorem exactZero_test_eq_true_iff (x : SignedRat) :
    ExactZero.test x = true ↔ x.value = 0 :=
  ExactZero.test_eq_true_iff x

/-- Failing the generic zero test means that the rational value is nonzero. -/
theorem exactZero_test_eq_false_iff (x : SignedRat) :
    ExactZero.test x = false ↔ x.value ≠ 0 :=
  ExactZero.test_eq_false_iff x

/-- The zero of `SignedRat` is positive zero. -/
@[simp, grind =] theorem negative_zero : (0 : SignedRat).negative = false := by
  change decide ((0 : Rat) < 0) = false
  simp

instance (n : Nat) : OfNat SignedRat n where
  ofNat := ofRat n

instance : NatCast SignedRat where
  natCast n := ofRat n

instance : IntCast SignedRat where
  intCast n := ofRat n

instance : RatCast SignedRat where
  ratCast := ofRat

/--
The signed rational of an exact dyadic, keeping the dyadic sign.

`Dyadic.toRat` forgets the sign of a zero dyadic; this constructor is the sign-preserving
replacement used when a binary format is decoded.
-/
def ofDyadic (d : Dyadic) : SignedRat :=
  ⟨d.toRat, d.negative, by
    intro hvalue
    have hsignificand : d.significand ≠ 0 := by
      rwa [Ne, Dyadic.toRat_eq_zero_iff] at hvalue
    cases hnegative : d.negative
    · have hpos := Dyadic.toRat_pos_of_significand_ne_zero d hsignificand hnegative
      simp [not_lt.mpr hpos.le]
    · have hpos :=
        Dyadic.toRat_pos_of_significand_ne_zero d.neg
          (by simpa using hsignificand) (by simp [hnegative])
      rw [Dyadic.neg_toRat] at hpos
      simp [neg_pos.mp hpos]⟩

/-- `ofDyadic` keeps the exact rational value of the dyadic. -/
@[simp, grind =] theorem value_ofDyadic (d : Dyadic) : (ofDyadic d).value = d.toRat :=
  rfl

/-- `ofDyadic` keeps the dyadic sign bit, so a negative dyadic zero stays negative. -/
@[simp, grind =] theorem negative_ofDyadic (d : Dyadic) : (ofDyadic d).negative = d.negative :=
  rfl

/-! ## Arithmetic -/

/-- Negation flips the sign bit, including the sign of zero. -/
def neg (x : SignedRat) : SignedRat :=
  ⟨-x.value, !x.negative, by
    intro hvalue
    have hne : x.value ≠ 0 := fun h => hvalue (by simp [h])
    rw [x.negative_eq_of_ne_zero hne]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · simp [hlt, not_lt.mpr (neg_pos.mpr hlt).le]
    · simp [not_lt.mpr hgt.le, neg_neg_iff_pos.mpr hgt]⟩

instance : Neg SignedRat where
  neg := neg

/-- Negation negates the value. -/
@[simp, grind =] theorem value_neg (x : SignedRat) : (-x).value = -x.value :=
  rfl

/-- Negation flips the sign bit, also for zero. -/
@[simp, grind =] theorem negative_neg (x : SignedRat) : (-x).negative = !x.negative :=
  rfl

/-- Negating a dyadic and then converting agrees with converting and then negating. -/
theorem ofDyadic_neg (d : Dyadic) : ofDyadic d.neg = -ofDyadic d :=
  ext (Dyadic.neg_toRat d) rfl

/--
Exact addition with the round-to-nearest sign rule for an exact zero sum.

A nonzero sum takes the sign of its value. A zero sum is negative only when both operands are
negative, so `-0 + -0 = -0` while `x + -x = +0` and `-0 + +0 = +0`.
-/
def add (x y : SignedRat) : SignedRat :=
  ⟨x.value + y.value,
    if x.value + y.value = 0 then x.negative && y.negative else decide (x.value + y.value < 0),
    fun hvalue => by simp [hvalue]⟩

instance : Add SignedRat where
  add := add

/-- Addition is exact on values. -/
@[simp, grind =] theorem value_add (x y : SignedRat) : (x + y).value = x.value + y.value :=
  rfl

/-- A nonzero exact sum has the sign of its value. -/
theorem negative_add_of_ne_zero {x y : SignedRat} (hsum : x.value + y.value ≠ 0) :
    (x + y).negative = decide (x.value + y.value < 0) := by
  change (if x.value + y.value = 0 then _ else _) = _
  simp [hsum]

/-- An exact zero sum is negative exactly when both operands are negative. -/
theorem negative_add_of_eq_zero {x y : SignedRat} (hsum : x.value + y.value = 0) :
    (x + y).negative = (x.negative && y.negative) := by
  change (if x.value + y.value = 0 then _ else _) = _
  simp [hsum]

/--
Exact addition with a caller-selected sign for cancellation between opposite signs.

Set `negativeCancellation` for rounding toward negative infinity. Same-sign zeros keep their
sign in either mode: `+0 + +0 = +0` and `-0 + -0 = -0`. A nonzero sum always takes the sign of
its rational value.
-/
def addWithCancellationSign (negativeCancellation : Bool) (x y : SignedRat) : SignedRat :=
  ⟨x.value + y.value,
    if x.value + y.value = 0 then
      if negativeCancellation then x.negative || y.negative else x.negative && y.negative
    else
      decide (x.value + y.value < 0),
    fun hvalue => by simp [hvalue]⟩

/-- Choosing a cancellation sign leaves the exact rational sum unchanged. -/
@[simp, grind =] theorem value_addWithCancellationSign
    (negativeCancellation : Bool) (x y : SignedRat) :
    (addWithCancellationSign negativeCancellation x y).value = x.value + y.value :=
  rfl

/-- Positive cancellation uses the ordinary round-to-nearest signed-rational addition. -/
@[simp, grind =] theorem addWithCancellationSign_false (x y : SignedRat) :
    addWithCancellationSign false x y = x + y :=
  rfl

/-- A nonzero sum has its numerical sign, independent of the cancellation policy. -/
theorem negative_addWithCancellationSign_of_ne_zero
    (negativeCancellation : Bool) {x y : SignedRat} (hsum : x.value + y.value ≠ 0) :
    (addWithCancellationSign negativeCancellation x y).negative =
      decide (x.value + y.value < 0) := by
  simp [addWithCancellationSign, hsum]

/-- An exact zero sum follows the selected direction while preserving same-sign zeros. -/
theorem negative_addWithCancellationSign_of_eq_zero
    (negativeCancellation : Bool) {x y : SignedRat} (hsum : x.value + y.value = 0) :
    (addWithCancellationSign negativeCancellation x y).negative =
      (if negativeCancellation then x.negative || y.negative else x.negative && y.negative) := by
  simp [addWithCancellationSign, hsum]

/-- Subtraction is addition of the negation, as in IEEE 754. -/
def sub (x y : SignedRat) : SignedRat :=
  add x (neg y)

instance : Sub SignedRat where
  sub := sub

/-- Subtraction is exact on values. -/
@[simp, grind =] theorem value_sub (x y : SignedRat) : (x - y).value = x.value - y.value := by
  change x.value + -y.value = x.value - y.value
  exact (sub_eq_add_neg x.value y.value).symm

/-- The sign of a nonzero product or quotient is the exclusive-or of the operand signs. -/
private theorem xor_negative_eq_decide {x y : SignedRat} {product : Rat}
    (hx : x.value ≠ 0) (hy : y.value ≠ 0)
    (hproduct : product < 0 ↔ x.value < 0 ∧ 0 < y.value ∨ 0 < x.value ∧ y.value < 0) :
    (x.negative ^^ y.negative) = decide (product < 0) := by
  rw [x.negative_eq_of_ne_zero hx, y.negative_eq_of_ne_zero hy]
  rcases lt_or_gt_of_ne hx with hx' | hx' <;>
    rcases lt_or_gt_of_ne hy with hy' | hy' <;>
    simp [hproduct, hx', hy', not_lt.mpr hx'.le, not_lt.mpr hy'.le]

/-- Exact multiplication; the sign bit is the exclusive-or of the operand sign bits. -/
def mul (x y : SignedRat) : SignedRat :=
  ⟨x.value * y.value, x.negative ^^ y.negative, by
    intro hvalue
    have hx : x.value ≠ 0 := left_ne_zero_of_mul hvalue
    have hy : y.value ≠ 0 := right_ne_zero_of_mul hvalue
    exact xor_negative_eq_decide hx hy (by rw [mul_neg_iff]; tauto)⟩

instance : Mul SignedRat where
  mul := mul

/-- Multiplication is exact on values. -/
@[simp, grind =] theorem value_mul (x y : SignedRat) : (x * y).value = x.value * y.value :=
  rfl

/-- A product takes the exclusive-or of the operand signs, the IEEE rule for exact products. -/
@[simp, grind =] theorem negative_mul (x y : SignedRat) :
    (x * y).negative = (x.negative ^^ y.negative) :=
  rfl

/--
Exact division; the sign bit is the exclusive-or of the operand sign bits.

Division by a zero value returns a zero value, following `Rat`; callers reject zero divisors
before quantizing.
-/
def div (x y : SignedRat) : SignedRat :=
  ⟨x.value / y.value, x.negative ^^ y.negative, by
    intro hvalue
    have hx : x.value ≠ 0 := fun h => hvalue (by simp [h])
    have hy : y.value ≠ 0 := fun h => hvalue (by simp [h])
    exact xor_negative_eq_decide hx hy (by rw [div_neg_iff]; tauto)⟩

instance : Div SignedRat where
  div := div

/-- Division is exact on values, with `Rat` division by zero giving zero. -/
@[simp, grind =] theorem value_div (x y : SignedRat) : (x / y).value = x.value / y.value :=
  rfl

/-- A quotient takes the exclusive-or of the operand signs, the IEEE rule for exact quotients. -/
@[simp, grind =] theorem negative_div (x y : SignedRat) :
    (x / y).negative = (x.negative ^^ y.negative) :=
  rfl

end SignedRat
end FloatLib.Numerics
