/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Proof

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

end FloatLibTests.Conformance.Numerics.GenericIntervals
