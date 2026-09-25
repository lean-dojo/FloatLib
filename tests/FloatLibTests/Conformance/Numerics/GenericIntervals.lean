/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Proof
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof

/-!
# Arbitrary interval carriers and scalar fields

The endpoint representation can inhabit a different universe from the interpreted scalar.
`ULift` provides a minimal non-floating representation; the examples remain polymorphic in the
ordered field rather than selecting rationals or one of the built-in floating-point families.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.GenericIntervals

open FloatLib.Numerics

universe u v

private def exactRounding (β : Type u) [LinearOrder β] :
    OutwardRounding (ULift.{v} β) β :=
  OutwardRounding.ofCandidates (fun x ↦ some x.down) (fun x ↦ Interval.point ⟨x⟩)

example {β : Type u} [LinearOrder β] (x : β) :
    (exactRounding.{u, v} β).enclose? x = some (Interval.point ⟨x⟩) := by
  simp [exactRounding, OutwardRounding.ofCandidates, OutwardRounding.checkedCandidates?,
    Interval.point]

example {β : Type u} [LinearOrder β] (lo hi : β) (h : lo ≤ hi) :
    Interval.ofBounds? (fun x : ULift.{v} β ↦ some x.down) ⟨lo⟩ ⟨hi⟩ =
      some (⟨⟨lo⟩, ⟨hi⟩⟩ : Interval (ULift.{v} β)) := by
  simp [Interval.ofBounds?, h]

example {β : Type u} [Field β] [LinearOrder β] [IsStrictOrderedRing β] (x y : β) :
    Interval.add? (exactRounding.{u, v} β) (Interval.point ⟨x⟩) (Interval.point ⟨y⟩) =
      some (Interval.point ⟨x + y⟩) := by
  simp [Interval.add?, Interval.liftBinary?, Interval.decode?, Interval.encloseInterval?,
    exactRounding, OutwardRounding.ofCandidates, OutwardRounding.checkedCandidates?,
    Interval.point]

example {α : Type u} {β : Type v} [Field β] [LinearOrder β] [IsStrictOrderedRing β]
    (R : OutwardRounding α β) {I J K : Interval α} {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y)
    (h : Interval.mul? R I J = some K) : K.Contains R.decode (x * y) :=
  Interval.contains_mul? R h hx hy

example {α : Type u} {β : Type v} [Field β] [LinearOrder β] [IsStrictOrderedRing β]
    (R : OutwardRounding α β) {I J K : Interval α} {x y : β}
    (hx : I.Contains R.decode x) (hy : J.Contains R.decode y)
    (h : Interval.div? R I J = some K) : K.Contains R.decode (x / y) :=
  Interval.contains_div? R h hx hy

/-! Expression evaluation uses the same syntax with exact, grid, and custom endpoints. -/

private def halfSquare : Interval.Expr :=
  .binary .div (.unary (.pow 2) (.var 0)) (.const 2)

example :
    halfSquare.eval? (Interval.Backend.rational {})
      (fun _ ↦ some ⟨-1, 1⟩) = some ⟨0, 1 / 2⟩ := by decide +kernel

example :
    halfSquare.eval? (Interval.Backend.binaryGrid { precision := 2 })
      (fun _ ↦ some ⟨-4, 4⟩) = some ⟨0, 2⟩ := by decide +kernel

example :
    halfSquare.eval? (Interval.Backend.ofRounding (exactRounding.{0, 1} ℚ))
      (fun _ ↦ some ⟨⟨-1⟩, ⟨1⟩⟩) = some ⟨⟨0⟩, ⟨1 / 2⟩⟩ := by decide +kernel

example :
    (Interval.Expr.binary .div (.const 1) (.var 0)).eval?
      (Interval.Backend.binaryGrid { precision := 8 })
      (fun _ ↦ some ⟨-256, 256⟩) = none := by decide +kernel

-- Touching zero at either endpoint also rejects reciprocal evaluation.
example :
    (Interval.Backend.binaryGrid { precision := 0 }).unary? .inv ⟨0, 2⟩ = none ∧
      (Interval.Backend.binaryGrid { precision := 0 }).unary? .inv ⟨-2, 0⟩ = none := by
  decide +kernel

-- On the quarter grid, rounding -1/3 must use floor and ceiling for negative values.
example :
    (Interval.Backend.binaryGrid { precision := 2 }).unary? .inv ⟨-12, -12⟩ =
      some ⟨-2, -1⟩ := by decide +kernel

-- Exact square-root endpoints include zero even with both accuracy controls set to zero.
example :
    (Interval.Backend.rational { precision := 0, degree := 0 }).unary? .sqrt ⟨0, 4⟩ =
      some ⟨0, 2⟩ := by decide +kernel

-- Arcsine accepts both domain endpoints without a square-root division.
example :
    ((Interval.Backend.rational { precision := 0, degree := 0 }).unary?
      .asin ⟨-1, 1⟩).isSome = true := by decide +kernel

-- An interior point can fail at coarse precision and succeed after refining the square root.
example :
    (Interval.Backend.rational { precision := 0, degree := 0 }).unary?
        .asin ⟨1 / 2, 1 / 2⟩ = none ∧
      ((Interval.Backend.rational { precision := 2, degree := 0 }).unary?
        .asin ⟨1 / 2, 1 / 2⟩).isSome = true := by
  decide +kernel

end FloatLibTests.Conformance.Numerics.GenericIntervals
