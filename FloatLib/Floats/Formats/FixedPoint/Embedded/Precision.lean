/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Count
import Mathlib.Algebra.Order.Ring.Int

/-!
# N1169's implementation-selected arithmetic precision

N1169, ISO/IEC TR 18037:2006(E), §4.1.6.2.1, C 6.3.1.3a and C 7.18a.4.
An admissible policy chooses ordinary rounding, a neighboring result when
`FX_FULL_PRECISION` is `OFF`, or the special inward result for an exact
product of `1` or `-1`. The latter exception is allowed independently of
the pragma and is marked for future deprecation in the draft.

Policies may depend on the destination and both operand values. Their
proof fields constrain the choices; they do not postulate arithmetic facts.
The ordinary path reuses `Arithmetic.apply` and its conversion semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics FloatLib.Numerics.Quantization

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.4: full precision or permission for one
    extra result step. -/
inductive Precision where
  /-- Full precision: no result takes the extra step. -/
  | ON
  /-- A product or a quotient may lie one grid step beyond the ordinary result. -/
  | OFF
  deriving DecidableEq, Repr

/-- Reconstruct a `Precision` constructor from its constructor index. -/
add_decl_doc Precision.ofNat_ctorIdx

/-- The four result choices permitted by WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1. -/
inductive ArithmeticChoice where
  /-- The ordinary conversion of the exact result. -/
  | ordinary
  /-- The grid neighbor of the ordinary result: the one above it when `upper` is true, the one below
  it otherwise. -/
  | neighbor (upper : Bool)
  /-- The representable value closest to an exact product of `1` or `-1` on its inner side. -/
  | unitProduct
  deriving DecidableEq, Repr

/-- N1169's restrictions on extra-unit adjustments and exceptional unit products.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.3 and 4.1.6.2.1.
-/
def ArithmeticChoice.Allowed (precision : Precision) (operation : Arithmetic)
    (x y : ℚ) : ArithmeticChoice → Prop
  | .ordinary => True
  | .neighbor _ => precision = .OFF ∧ (operation = .mul ∨ operation = .div)
  | .unitProduct => operation = .mul ∧ (x * y = 1 ∨ x * y = -1)

/-- An implementation's result selection, with every choice admitted by the source clause. -/
structure ArithmeticPolicy where
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.4: whether extra-unit multiplication and
    division error is forbidden. -/
  FX_FULL_PRECISION : Precision
  /-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1: select a result rule from the format,
    operation and exact operands. -/
  choose : Format → Arithmetic → ℚ → ℚ → ArithmeticChoice
  /-- Every choice the policy makes is one the source clause admits in this pragma state. -/
  allowed (destination : Format) (operation : Arithmetic) (x y : ℚ) :
    (choose destination operation x y).Allowed FX_FULL_PRECISION operation x y

-- Preserve the pragma identifier specified in N1169 C 7.18a.4.
attribute [nolint defsWithUnderscore] ArithmeticPolicy.FX_FULL_PRECISION

/-- Exact-result conversion is permitted with either pragma state. -/
def ArithmeticPolicy.exact (precision : Precision) : ArithmeticPolicy where
  FX_FULL_PRECISION := precision
  choose _ _ _ _ := .ordinary
  allowed _ _ _ _ := trivial

/-- A concrete relaxed implementation always selects the indicated neighboring result. -/
def ArithmeticPolicy.neighbor (upper : Bool) : ArithmeticPolicy where
  FX_FULL_PRECISION := .OFF
  choose _ operation _ _ :=
    if operation = .mul ∨ operation = .div then
      .neighbor upper
    else .ordinary
  allowed _ operation _ _ := by
    cases operation <;> simp [ArithmeticChoice.Allowed]

/-- Enable the draft's special unit-product treatment on any admissible implementation. -/
def ArithmeticPolicy.withUnitProducts (policy : ArithmeticPolicy) : ArithmeticPolicy where
  FX_FULL_PRECISION := policy.FX_FULL_PRECISION
  choose destination operation x y :=
    if operation = .mul ∧ (x * y = 1 ∨ x * y = -1) then .unitProduct
    else policy.choose destination operation x y
  allowed destination operation x y := by
    split
    · assumption
    · exact policy.allowed destination operation x y

/-- Move a stored coefficient by an integer number of grid steps, clipping at the endpoints. -/
@[inline] def Format.move {format : Format} (value : format.Code) (steps : Int) :
    format.Code :=
  format.clamp (bitsfx value + steps)

/-- Clipping a moved code cannot increase its distance from the original stored coefficient. -/
theorem Format.move_distance {format : Format} (value : format.Code) (steps : Int) :
    |bitsfx (Format.move value steps) - bitsfx value| ≤ |steps| := by
  have hself := format.quantizer.clampCode_eq_self value.2.1 value.2.2
  change format.quantizer.clampCode (bitsfx value) = bitsfx value at hself
  change |format.quantizer.clampCode (bitsfx value + steps) - bitsfx value| ≤ _
  have h := Saturating.abs_clamp_sub_clamp_le
    format.quantizer.qmin format.quantizer.qmax (bitsfx value + steps) (bitsfx value)
  change |format.quantizer.clampCode (bitsfx value + steps) -
    format.quantizer.clampCode (bitsfx value)| ≤ |bitsfx value + steps - bitsfx value| at h
  rw [hself] at h
  simpa only [add_sub_cancel_left] using h

/-- Coefficient selected by the inward exception at an exact product of `1` or `-1`. -/
@[inline] def Format.unitProduct (format : Format) (positive : Bool) : format.Code :=
  format.clamp (if positive then (2 : Int) ^ format.fractionalBits - 1
    else 1 - (2 : Int) ^ format.fractionalBits)

/-- The exceptional unit-product result is the closest representable value on its strict side. -/
theorem Format.unitProduct_closest (format : Format) (positive : Bool) :
    if positive then
      bitsfx (format.unitProduct positive) < (2 : Int) ^ format.fractionalBits ∧
        ∀ value : format.Code, bitsfx value < (2 : Int) ^ format.fractionalBits →
          bitsfx value ≤ bitsfx (format.unitProduct positive)
    else
      -(2 : Int) ^ format.fractionalBits < bitsfx (format.unitProduct positive) ∧
        ∀ value : format.Code, -(2 : Int) ^ format.fractionalBits < bitsfx value →
          bitsfx (format.unitProduct positive) ≤ bitsfx value := by
  have hzero := IntegerFormat.zero_inRange format.integerFormat
  change format.quantizer.qmin ≤ 0 ∧ 0 ≤ format.quantizer.qmax at hzero
  have hp : 1 ≤ (2 : Int) ^ format.fractionalBits := one_le_pow₀ (by decide)
  have hpow : (2 : Int) ^ format.fractionalBits ≤ (2 : Int) ^ format.precision :=
    pow_le_pow_right₀ (by decide) (Nat.le_add_left _ _)
  have hupper : (2 : Int) ^ format.fractionalBits - 1 ≤ format.quantizer.qmax := by
    change _ ≤ format.integerFormat.maxValue
    rw [format.maxValue_eq]
    omega
  cases positive
  · simp only [Bool.false_eq_true, ↓reduceIte, Format.unitProduct, bitsfx, Format.clamp,
      AffineQuantizer.clampCode, Saturating.clamp]
    rw [min_eq_right (show 1 - (2 : Int) ^ format.fractionalBits ≤
      format.quantizer.qmax from (by omega))]
    constructor
    · exact lt_max_of_lt_right (by omega)
    · intro value h
      exact max_le value.2.1 (by omega)
  · simp only [↓reduceIte, Format.unitProduct, bitsfx, Format.clamp,
      AffineQuantizer.clampCode, Saturating.clamp]
    rw [min_eq_right hupper, max_eq_right (show format.quantizer.qmin ≤
      (2 : Int) ^ format.fractionalBits - 1 from (by omega))]
    exact ⟨by omega, fun value h ↦ by omega⟩

/-- Apply one admitted result choice after the exact rational operation. -/
def ArithmeticChoice.apply (choice : ArithmeticChoice) (destination : Format)
    (rounding : Rounding) (overflow : Overflow) (exact : ℚ) : Option destination.Code :=
  match choice with
  | .ordinary => convert destination rounding overflow exact
  | .neighbor upper => (convert destination rounding overflow exact).map
      (fun value ↦ Format.move value (if upper then 1 else -1))
  | .unitProduct => some (destination.unitProduct (exact = 1))

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1: arithmetic with all admitted
    implementation-selected result choices. -/
@[inline] def Arithmetic.applyWith (operation : Arithmetic) (policy : ArithmeticPolicy)
    (destination : Format) (rounding : Rounding) (overflow : Overflow) (x y : ℚ) :
    Option destination.Code :=
  (operation.exact x y).bind fun exact ↦
    (policy.choose destination operation x y).apply destination rounding overflow exact

/-- The ordinary policy specializes to the existing exact-operation conversion. -/
@[simp] theorem Arithmetic.applyWith_exact (operation : Arithmetic) (precision : Precision)
    (destination : Format) (rounding : Rounding) (overflow : Overflow) (x y : ℚ) :
    operation.applyWith (ArithmeticPolicy.exact precision) destination rounding overflow x y =
      operation.apply destination rounding overflow x y := rfl

/-- Independent result relation: ordinary conversion, a permitted neighbor, or a strict unit
    side. -/
def Arithmetic.Allowed (operation : Arithmetic) (precision : Precision)
    (destination : Format) (rounding : Rounding) (overflow : Overflow)
    (x y : ℚ) (result : destination.Code) : Prop :=
  ∃ exact, operation.exact x y = some exact ∧
    (convert destination rounding overflow exact = some result ∨
      (precision = .OFF ∧ (operation = .mul ∨ operation = .div) ∧
        ∃ ordinary : destination.Code, convert destination rounding overflow exact = some ordinary ∧
          |bitsfx result - bitsfx ordinary| ≤ 1) ∨
      (operation = .mul ∧ (exact = 1 ∨ exact = -1) ∧
        result = destination.unitProduct (exact = 1)))

/-- Every policy execution satisfies the clause's result relation, at every destination
    precision. -/
theorem Arithmetic.applyWith_allowed (operation : Arithmetic) (policy : ArithmeticPolicy)
    (destination : Format) (rounding : Rounding) (overflow : Overflow)
    (x y : ℚ) (result : destination.Code)
    (hresult : operation.applyWith policy destination rounding overflow x y = some result) :
    operation.Allowed policy.FX_FULL_PRECISION destination rounding overflow x y result := by
  obtain ⟨exact, hexact, hchoice⟩ := Option.bind_eq_some_iff.mp hresult
  refine ⟨exact, hexact, ?_⟩
  have hadmit := policy.allowed destination operation x y
  cases hc : policy.choose destination operation x y with
  | ordinary =>
    exact Or.inl (by simpa [hc, ArithmeticChoice.apply] using hchoice)
  | neighbor upper =>
    simp only [hc, ArithmeticChoice.Allowed] at hadmit
    obtain ⟨ordinary, ho, hr⟩ := Option.map_eq_some_iff.mp
      (show (convert destination rounding overflow exact).map
        (fun value ↦ Format.move value (if upper then 1 else -1)) = some result from
          (by simpa [hc, ArithmeticChoice.apply] using hchoice))
    subst result
    exact Or.inr (Or.inl ⟨hadmit.1, hadmit.2, ordinary, ho,
      by
        have h := Format.move_distance ordinary (if upper then 1 else -1)
        cases upper <;> simpa [abs_of_nonneg (show (0 : Int) ≤ 1 by decide)] using h⟩)
  | unitProduct =>
    simp only [hc, ArithmeticChoice.Allowed] at hadmit
    have heq : exact = x * y := by
      simpa [hadmit.1, Arithmetic.exact] using hexact.symm
    refine Or.inr (Or.inr ⟨hadmit.1, by simpa only [heq] using hadmit.2, ?_⟩)
    simpa [hc, ArithmeticChoice.apply] using hchoice.symm

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3 and C 6.3.1.8: compound assignment to an integer
    lvalue.
The fixed operand determines the intermediate result type; the final conversion
truncates toward zero and checks the independently supplied integer range. -/
def Arithmetic.assignInteger (operation : Arithmetic) (policy : ArithmeticPolicy)
    (integerFormat : IntegerFormat) {format : Format} (rounding : Rounding)
    (overflow : Overflow) (integer : Int) (value : format.Code) : Option Int :=
  (operation.applyWith policy format rounding overflow integer (Format.decode value)).bind
    (fun result ↦ toInteger integerFormat (Format.decode result))

/-- Integer compound assignment succeeds exactly when its arithmetic and conversion do. -/
theorem Arithmetic.assignInteger_eq_some_iff (operation : Arithmetic)
    (policy : ArithmeticPolicy) (integerFormat : IntegerFormat) {format : Format}
    (rounding : Rounding) (overflow : Overflow) (integer : Int) (value : format.Code)
    (result : Int) :
    operation.assignInteger policy integerFormat rounding overflow integer value = some result ↔
      ∃ intermediate : format.Code,
        operation.applyWith policy format rounding overflow integer (Format.decode value) =
          some intermediate ∧
        toInteger integerFormat (Format.decode intermediate) = some result :=
  Option.bind_eq_some_iff

end FloatLib.Floats.Formats.FixedPoint.Embedded
