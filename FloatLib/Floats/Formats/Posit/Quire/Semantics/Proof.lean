/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Model.Proof
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correctness of exact posit-quire semantics

A quire is a wide signed fixed-point accumulator with one reserved NaR encoding. Here we connect
its stored coefficient to the exact rational, dyadic, and generic numerical-value views, and prove
that all three recognize the same exceptional word. A coefficient that was built successfully keeps
its value at the quire scale.

Exact product accumulation within the quire's capacity rests on these facts, while rounding back
to a posit is another operation with its own theorems.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire.Model

open FloatLib.Numerics

variable {format : Format}

/-- The zero quire denotes the exact rational zero. -/
@[simp] theorem toRat?_zero (format : Format) :
    (zero format).toRat? = some 0 := by
  simp [toRat?, isNaR_zero]

/-- The NaR quire has no ordinary rational interpretation. -/
@[simp] theorem toRat?_nar (format : Format) :
    (nar format).toRat? = none := by
  simp [toRat?]

/-- Exact quire decoding recognizes the canonical zero value. -/
@[simp] theorem decode_zero (format : Format) :
    (zero format).decode = .finite 0 := by
  simp [decode]

/-- Exact quire decoding recognizes the canonical NaR value. -/
@[simp] theorem decode_nar (format : Format) :
    (nar format).decode = .exceptional .notAReal := by
  simp [decode]

/-- The zero quire maps to a zero-valued dyadic at the quire's fixed binary scale. -/
@[simp] theorem toDyadic?_zero (format : Format) :
    (zero format).toDyadic? =
      some
        (FloatLib.Numerics.Dyadic.ofScaledInt
          0 (scaleExponent format)) := by
  simp [toDyadic?]

/-- The NaR quire has no ordinary dyadic interpretation. -/
@[simp] theorem toDyadic?_nar (format : Format) :
    (nar format).toDyadic? = none := by
  simp [toDyadic?]

/-- The rational quire view is the dyadic view mapped to rationals. -/
theorem toRat?_eq_toDyadic?_map (value : Model format) :
    value.toRat? =
      value.toDyadic?.map FloatLib.Numerics.Dyadic.toRat := by
  unfold toRat? toDyadic?
  by_cases hnar : value.isNaR = true
  · simp [hnar]
  · have hordinary : value.isNaR = false :=
      Bool.eq_false_of_not_eq_true hnar
    simp [hordinary]

/-- An exact rational is missing for the reserved quire NaR word and for no other word. -/
theorem toRat?_eq_none_iff (value : Model format) :
    value.toRat? = none ↔ value.isNaR = true := by
  simp [toRat?]

/-- An exact dyadic is missing for the reserved quire NaR word and for no other word. -/
theorem toDyadic?_eq_none_iff (value : Model format) :
    value.toDyadic? = none ↔ value.isNaR = true := by
  simp [toDyadic?]

/-- Generic decoding is exceptional for the reserved quire NaR word and for no other word. -/
theorem decode_eq_exceptional_iff (value : Model format) :
    value.decode = .exceptional .notAReal ↔ value.isNaR = true := by
  rw [← toRat?_eq_none_iff]
  unfold decode
  cases value.toRat? <;> simp

/-- Encoding an ordinary coefficient never produces quire NaR. -/
private theorem isNaR_ofCoefficient_of_ordinary
    {coefficient : Int}
    (hcoefficient : OrdinaryCoefficient format coefficient) :
    (ofCoefficient format coefficient).isNaR = false :=
  (ordinaryCoefficient_iff_isNaR_eq_false _).mp
    (by rwa [coefficient_ofCoefficient_of_ordinary hcoefficient])

/-- Exact semantics of a successfully encoded ordinary coefficient. -/
theorem toRat?_ofCoefficient_of_ordinary
    {coefficient : Int}
    (hcoefficient : OrdinaryCoefficient format coefficient) :
    (ofCoefficient format coefficient).toRat? =
      some
        (Rat.ofInt coefficient *
          (2 : Rat) ^ scaleExponent format) := by
  simp [toRat?, isNaR_ofCoefficient_of_ordinary hcoefficient,
    coefficient_ofCoefficient_of_ordinary hcoefficient]

/-- Generic numerical value of a successfully encoded ordinary coefficient. -/
theorem decode_ofCoefficient_of_ordinary
    {coefficient : Int}
    (hcoefficient : OrdinaryCoefficient format coefficient) :
    (ofCoefficient format coefficient).decode =
      .finite (Rat.ofInt coefficient * (2 : Rat) ^ scaleExponent format) := by
  simp [decode, toRat?_ofCoefficient_of_ordinary hcoefficient]

/-- Shared-dyadic semantics of a successfully encoded ordinary coefficient. -/
theorem toDyadic?_ofCoefficient_of_ordinary
    {coefficient : Int}
    (hcoefficient : OrdinaryCoefficient format coefficient) :
    (ofCoefficient format coefficient).toDyadic? =
      some
        (FloatLib.Numerics.Dyadic.ofScaledInt
          coefficient (scaleExponent format)) := by
  simp [toDyadic?, isNaR_ofCoefficient_of_ordinary hcoefficient,
    coefficient_ofCoefficient_of_ordinary hcoefficient]

end FloatLib.Floats.Formats.Posit.Quire.Model
