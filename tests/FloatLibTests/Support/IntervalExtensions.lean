/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Interval

/-!
# User-defined interval enclosures

These fixtures are defined outside the production library. Their consumer tests import the
registrations, exercising the same workflow as a downstream mathematical library.
-/

@[expose] public section

namespace FloatLibTests.Support.IntervalExtensions

open FloatLib.Numerics.Interval

/-- An irrational constant with a precision-dependent enclosure. -/
noncomputable def rootTwo : ℝ := Real.sqrt 2

/-- Use the existing square-root certificate for the user constant. -/
def rootTwoEnclosure : Extension :=
  Extension.constant (fun config => sqrtBounds? (point 2) config.precision)

/-- The registered bounds contain the intended irrational constant. -/
@[interval_extension]
theorem rootTwo_sound : rootTwoEnclosure.Sound rootTwo := by
  apply Extension.constant_sound
  intro config output h
  exact containsReal_sqrtBounds? h (by simp [containsReal_some_iff, point])

/-- A second named constant exercises direct registration of ordinary endpoint bounds. -/
noncomputable def myConstant : ℝ := Real.sqrt 2

/-- The constant API needs only a pair of rational endpoints and their inequalities. -/
@[interval_extension]
def myConstantBounds : ConstantBounds myConstant where
  bounds _ := ⟨1.4, 1.5⟩
  valid _ := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    norm_num [myConstant]
    constructor <;> nlinarith

/-- A rational value whose registered bounds improve with the requested precision. -/
noncomputable def shrinkingOne : ℝ := 1

/-- The precision argument controls the enclosure, even though the value is already rational. -/
@[interval_extension]
def shrinkingOneBounds : ConstantBounds shrinkingOne where
  bounds precision := ⟨1 - 1 / (2 ^ precision : ℚ), 1 + 1 / (2 ^ precision : ℚ)⟩
  valid precision := by
    have herror : (0 : ℝ) ≤ ((1 / (2 ^ precision : ℚ) : ℚ) : ℝ) := by positivity
    simpa only [shrinkingOne, Rat.cast_sub, Rat.cast_add, Rat.cast_one] using
      And.intro (sub_le_self (1 : ℝ) herror) (le_add_of_nonneg_right herror)

/-- Repeated arguments expose the dependency loss of ordinary interval subtraction. -/
noncomputable def cancel (x : ℝ) : ℝ := x - x

/-- Subtraction bounds deliberately improve only when the input box is subdivided. -/
def cancelEnclosure : Extension :=
  Extension.unary (fun _ I => sub? Internal.rationalOutwardRounding I I)

/-- The enclosure is valid at every real argument in the input interval. -/
@[interval_extension]
theorem cancel_sound : cancelEnclosure.Sound cancel := by
  apply Extension.unary_sound
  intro config I J x h hx
  exact containsReal_sub? Internal.rationalOutwardRounding h hx hx

/-- A four-argument function exercises calls beyond the built-in operation arities. -/
def fourth (_x _y _z w : ℝ) : ℝ := w

/-- Enclose exactly the fourth argument; reject every other argument count. -/
def fourthEnclosure : Extension where
  arity := 4
  enclose? _ inputs := match inputs with
    | [_, _, _, I] => some I
    | _ => none

/-- The generic contract supports every real tuple at arity four. -/
@[interval_extension]
theorem fourth_sound : fourthEnclosure.Sound fourth := by
  intro config inputs output values h _ hx
  cases hx with
  | nil => simp [fourthEnclosure] at h
  | cons h₁ htail =>
    cases htail with
    | nil => simp [fourthEnclosure] at h
    | cons h₂ htail =>
      cases htail with
      | nil => simp [fourthEnclosure] at h
      | cons h₃ htail =>
        cases htail with
        | nil => simp [fourthEnclosure] at h
        | cons h₄ htail =>
          cases htail with
          | nil =>
            simp only [fourthEnclosure, Option.some.injEq] at h
            subst output
            exact h₄
          | cons => simp [fourthEnclosure] at h

end FloatLibTests.Support.IntervalExtensions
