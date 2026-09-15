/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic
public import FloatLib.Numerics.Exact.SignedRat

/-!
# Embeddings between exact domains

`ExactMap Source Target` converts exact values between the domains used by numerical families.
Binary interchange values, including Lean's native `Float32` and `Float`, use `SignedRat`, which
keeps the sign of zero; posit, fixed-point, logarithmic, and quire values use `Rat`; OCP E8M0 uses
`Dyadic`; codebooks can use another exact type. The integer, rational, dyadic, and signed-rational
embeddings are defined below. Conversion lifts these finite maps over `NumericalValue`
observations.

The map from `SignedRat` to `Rat` preserves the rational value and forgets the sign of zero. A
conversion through `Rat` therefore cannot carry a source zero sign to its destination.

Instances must preserve value without rounding, overflow, or a context-dependent choice.
The class cannot express that law for arbitrary source and target types, so every non-identity
instance needs a separate theorem relating their mathematical interpretations. An arbitrary
coercion is insufficient to define an instance.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u v

/--
Canonical embedding between executable exact domains.

This class is an interoperability capability, not an implicit numerical-promotion rule. User
values remain statically typed, and destination rounding still occurs only in an explicit
conversion or destination-driven operation. Installing an instance is a semantic commitment;
preservation must be justified in the source or target domain's own mathematical model.
-/
class ExactMap (Source : Type u) (Target : Type v) where
  /--
  Preserve the source's numerical value without rounding.

  Representation metadata can be forgotten: `signedRatToRat` discards the sign of zero.
  Preservation of numerical value is justified by separate domain-specific theorems.
  -/
  map : Source → Target

namespace ExactMap

variable {Source : Type u} {Target : Type v}

/-- Apply the canonical exact-domain embedding selected for these two types. -/
@[inline] def run [self : ExactMap Source Target] (value : Source) : Target :=
  self.map value

/-- Every exact domain embeds into itself without changing a value. -/
instance (priority := low) identity : ExactMap Source Source where
  map := id

/-- The identity exact-domain embedding is computationally the identity. -/
@[simp, grind =] theorem run_identity (value : Source) :
    run (Source := Source) (Target := Source) value = value :=
  rfl

/-- Signed integers embed exactly into rational arithmetic. -/
instance intToRat : ExactMap Int Rat where
  map := Rat.ofInt

/-- The signed-integer embedding is Mathlib's exact rational constructor. -/
@[simp, grind =] theorem run_intToRat (value : Int) :
    run (Source := Int) (Target := Rat) value = Rat.ofInt value :=
  rfl

/-- Natural numbers embed exactly into rational arithmetic. -/
instance natToRat : ExactMap Nat Rat where
  map value := Rat.ofInt (Int.ofNat value)

/-- The natural-number embedding has denominator one. -/
@[simp, grind =] theorem run_natToRat (value : Nat) :
    run (Source := Nat) (Target := Rat) value = Rat.ofInt (Int.ofNat value) :=
  rfl

/-- Exact dyadic values embed into rationals through their mathematical value. -/
instance dyadicToRat : ExactMap FloatLib.Numerics.Dyadic Rat where
  map := FloatLib.Numerics.Dyadic.toRat

/-- The dyadic embedding is the executable exact rational denotation. -/
@[simp, grind =] theorem run_dyadicToRat (value : FloatLib.Numerics.Dyadic) :
    run (Source := FloatLib.Numerics.Dyadic) (Target := Rat) value = value.toRat :=
  rfl

/-- Rationals embed into the signed-rational domain; zero receives the positive sign. -/
instance ratToSignedRat : ExactMap Rat FloatLib.Numerics.SignedRat where
  map := FloatLib.Numerics.SignedRat.ofRat

/-- The rational embedding keeps the value and derives the sign from it. -/
@[simp, grind =] theorem run_ratToSignedRat (value : Rat) :
    run (Source := Rat) (Target := FloatLib.Numerics.SignedRat) value =
      FloatLib.Numerics.SignedRat.ofRat value :=
  rfl

/-- Signed integers embed into the signed-rational domain. -/
instance intToSignedRat : ExactMap Int FloatLib.Numerics.SignedRat where
  map value := FloatLib.Numerics.SignedRat.ofRat (Rat.ofInt value)

/-- The signed-integer embedding is the rational embedding of the integer. -/
@[simp, grind =] theorem run_intToSignedRat (value : Int) :
    run (Source := Int) (Target := FloatLib.Numerics.SignedRat) value =
      FloatLib.Numerics.SignedRat.ofRat (Rat.ofInt value) :=
  rfl

/-- Natural numbers embed into the signed-rational domain. -/
instance natToSignedRat : ExactMap Nat FloatLib.Numerics.SignedRat where
  map value := FloatLib.Numerics.SignedRat.ofRat (Rat.ofInt (Int.ofNat value))

/-- The natural-number embedding is the rational embedding of the number. -/
@[simp, grind =] theorem run_natToSignedRat (value : Nat) :
    run (Source := Nat) (Target := FloatLib.Numerics.SignedRat) value =
      FloatLib.Numerics.SignedRat.ofRat (Rat.ofInt (Int.ofNat value)) :=
  rfl

/-- Exact dyadics embed into the signed-rational domain, keeping the sign of zero. -/
instance dyadicToSignedRat : ExactMap FloatLib.Numerics.Dyadic FloatLib.Numerics.SignedRat where
  map := FloatLib.Numerics.SignedRat.ofDyadic

/-- The dyadic embedding is the sign-preserving signed-rational denotation. -/
@[simp, grind =] theorem run_dyadicToSignedRat (value : FloatLib.Numerics.Dyadic) :
    run (Source := FloatLib.Numerics.Dyadic) (Target := FloatLib.Numerics.SignedRat) value =
      FloatLib.Numerics.SignedRat.ofDyadic value :=
  rfl

/--
Signed rationals embed into `Rat` by forgetting the sign of zero.

The rational value is preserved, but the target exact domain cannot distinguish the two zero
signs. A destination that needs the source zero sign must use a sign-preserving exact domain.
-/
instance signedRatToRat : ExactMap FloatLib.Numerics.SignedRat Rat where
  map := FloatLib.Numerics.SignedRat.value

/-- The signed-rational embedding into `Rat` is the value projection. -/
@[simp, grind =] theorem run_signedRatToRat (value : FloatLib.Numerics.SignedRat) :
    run (Source := FloatLib.Numerics.SignedRat) (Target := Rat) value = value.value :=
  rfl

end ExactMap
end ExecFloat
end FloatLib.Floats
