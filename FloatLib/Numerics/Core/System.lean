/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Value

/-!
# Encoded numerical systems

`NumericalSystem` is the family-independent interface of FloatLib.  It says only what code type
is stored, what mathematical scalar domain finite codes denote, and how every code is interpreted.
It does not assume a radix, exponent field, NaN convention, or rounding rule.

This small interface is broad enough for binary and decimal floats, fixed point, posits,
logarithmic number systems, block-scaled values, and exact integers.  Concrete arithmetic and its
proofs remain in the corresponding implementation modules.
-/

@[expose] public section

namespace FloatLib.Numerics

universe u v w

set_option linter.checkUnivs false in
/-- A representation together with its complete mathematical interpretation. -/
structure NumericalSystem where
  /-- Stored or executable values of the system. -/
  Code : Type u
  /-- Exact mathematical domain used to interpret ordinary codes. -/
  Scalar : Type v
  /-- Meaning of every code, including infinities and exceptional words. -/
  denote : Code → NumericalValue Scalar

namespace NumericalSystem

variable {β : Type w}

/--
Build a numerical system whose every code has an ordinary finite interpretation.

This is the common representation shape for exact integers, fixed-point values, logarithmic
codes, and other formats without infinities or exceptional words.
-/
@[reducible] def ofFinite {Code : Type u} {Scalar : Type v}
    (decode : Code → Scalar) : NumericalSystem where
  Code := Code
  Scalar := Scalar
  denote code := .finite (decode code)

/--
A scalar type viewed as an exact numerical system with no exceptional codes.

Reducibility lets Lean reuse structures such as orders and rings on `α` through the projected
`Code` and `Scalar` types without introducing forwarding instances.
-/
@[reducible] def exact (α : Type u) : NumericalSystem :=
  ofFinite (id : α → α)

/-- `code` represents the ordinary scalar `x`. -/
def Represents (S : NumericalSystem) (code : S.Code) (x : S.Scalar) : Prop :=
  S.denote code = .finite x

/-- In an `ofFinite` system, representation is equality after decoding. -/
-- grind: no rule; reducing `ofFinite` erases `decode`, so matching cannot recover every parameter.
@[simp] theorem ofFinite_represents_iff {Code : Type u} {Scalar : Type v}
    (decode : Code → Scalar) (code : Code) (value : Scalar) :
    (ofFinite decode).Represents code value ↔ decode code = value := by
  simp [Represents, ofFinite]

/-- Exact-system representation is ordinary equality. -/
@[grind =] theorem exact_represents_iff {α : Type u} (code value : α) :
    (exact α).Represents code value ↔ code = value := by
  simp [exact]

/-- An exact scalar is representable when some code denotes it. -/
def Representable (S : NumericalSystem) (x : S.Scalar) : Prop :=
  ∃ code, S.Represents code x

/-- Two codes are semantically equivalent, even if their bit patterns differ. -/
def Equivalent (S : NumericalSystem) (x y : S.Code) : Prop :=
  S.denote x = S.denote y

/-- A code has an ordinary finite meaning. -/
def IsFinite (S : NumericalSystem) (code : S.Code) : Prop :=
  ∃ x, S.Represents code x

/-- Change only the mathematical codomain of a numerical system. -/
def mapScalar (S : NumericalSystem) (f : S.Scalar → β) : NumericalSystem where
  Code := S.Code
  Scalar := β
  denote code := (S.denote code).map f

/-- A represented scalar remains represented after mapping the system's scalar codomain. -/
@[simp, grind .] theorem represents_mapScalar (S : NumericalSystem) (f : S.Scalar → β)
    (code : S.Code) (x : S.Scalar) (h : S.Represents code x) :
    (S.mapScalar f).Represents code (f x) := by
  change NumericalValue.map f (S.denote code) = .finite (f x)
  rw [show S.denote code = .finite x from h]
  rfl

end NumericalSystem
end FloatLib.Numerics
