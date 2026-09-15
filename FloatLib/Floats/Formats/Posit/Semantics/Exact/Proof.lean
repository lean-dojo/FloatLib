/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correctness properties of exact posit semantics

The complete and partial rational decoders preserve zero and finite fields, identify NaR exactly,
and agree with the shared dyadic decoder used by integer arithmetic kernels.

This is the semantic junction between user-facing rational meanings and implementation-facing
dyadics. Proving the agreement once lets order, rounding, and arithmetic developments choose the
more convenient exact representation without creating parallel definitions of what a posit word
means.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

open FloatLib.Numerics

namespace Model.ExactValue

/-- Forgetting exact zero produces finite rational zero. -/
@[simp] theorem forget_zero {format : Format} :
    forget (.zero : Model.ExactValue format) = .finite 0 :=
  rfl

/-- Forgetting decoded finite fields preserves their exact rational value. -/
@[simp] theorem forget_finite {format : Format} (fields : Model.DecodedFields format) :
    forget (.finite fields) = .finite fields.toRat :=
  rfl

/-- Forgetting NaR records the common `notAReal` exceptional value. -/
@[simp] theorem forget_nar {format : Format} :
    forget (.nar : Model.ExactValue format) = .exceptional .notAReal :=
  rfl

/-- The optional rational view maps exact zero to rational zero. -/
@[simp] theorem toRat?_zero {format : Format} :
    toRat? (.zero : Model.ExactValue format) = some 0 :=
  rfl

/-- The optional rational view preserves decoded finite fields exactly. -/
@[simp] theorem toRat?_finite {format : Format} (fields : Model.DecodedFields format) :
    toRat? (.finite fields) = some fields.toRat :=
  rfl

/-- The optional rational view is unavailable for NaR. -/
@[simp] theorem toRat?_nar {format : Format} :
    toRat? (.nar : Model.ExactValue format) = none :=
  rfl

end Model.ExactValue

namespace Model

variable {format : Format}

/--
The rational and shared-dyadic decoders commute.

Integer kernels may therefore prove their rounding behavior in `Numerics.Dyadic` and reuse the
result against the public rational specification.
-/
theorem toRat?_eq_toDyadic?_map (value : Model format) :
    value.toRat? = value.toDyadic?.map FloatLib.Numerics.Dyadic.toRat := by
  unfold toRat? Model.ExactValue.toRat? Model.toDyadic?
  cases value.decodeExact <;>
    simp [Model.DecodedFields.toRat, Model.DecodedFields.toDyadic]

/-- Decoding the canonical zero word produces finite rational zero. -/
@[simp] theorem decode_zero (format : Format) :
    decode (zero format) = .finite 0 := by
  simp [decode]

/-- Decoding the unique NaR word produces the common `notAReal` exception. -/
@[simp] theorem decode_nar (format : Format) :
    decode (nar format) = .exceptional .notAReal := by
  simp [decode]

/-- The optional exact-rational semantics of the canonical zero word is zero. -/
@[simp] theorem toRat?_zero (format : Format) :
    toRat? (zero format) = some 0 := by
  simp [toRat?]

/-- The optional exact-rational semantics of the unique NaR word is unavailable. -/
@[simp] theorem toRat?_nar (format : Format) :
    toRat? (nar format) = none := by
  simp [toRat?]

/-- An exact rational is unavailable precisely for the unique NaR word. -/
theorem toRat?_eq_none_iff (value : Model format) :
    value.toRat? = none ↔ value.isNaR = true := by
  unfold toRat? Model.ExactValue.toRat? decodeExact
  by_cases hnar : value.isNaR = true
  · simp [hnar]
  · have hnarFalse : value.isNaR = false := Bool.eq_false_of_not_eq_true hnar
    by_cases hzero : value.isZero = true
    · simp [hnarFalse, hzero]
    · have hzeroFalse : value.isZero = false := Bool.eq_false_of_not_eq_true hzero
      simp [hnarFalse, hzeroFalse]

end Model
end FloatLib.Floats.Formats.Posit
