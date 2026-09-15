/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Values of encoded numerical systems

An encoded numerical system may contain ordinary values, signed infinities, and exceptional bit
patterns.  These possibilities are not specific to IEEE floating point: posits have `NaR`, some
low-precision formats reserve individual words, and fixed-point systems may have no exceptional
values at all.

`NumericalValue` records this common semantic shape without prescribing a storage layout.  The
finite value type remains a parameter, so a system may denote real numbers, rational numbers,
integers, complex numbers, or another exact mathematical domain.
-/

@[expose] public section

namespace FloatLib.Numerics

universe u v w

/-- Why an encoded word has no ordinary numerical value. -/
inductive ExceptionalValue where
  /-- A NaN encoding, optionally carrying its representation-defined payload bits. -/
  | nan (payload : Option Nat := none)
  /-- The single not-a-real value used by posit systems. -/
  | notAReal
  /-- A representation-specific reserved word, optionally retaining its encoded payload. -/
  | reserved (payload : Option Nat := none)
  /-- An operation whose result is intentionally outside the scalar semantics. -/
  | undefined
  deriving DecidableEq, Repr

/--
The mathematical meaning of one encoded value.

The sign on `infinity` is `true` for negative infinity.  Signed finite zero, when a format
distinguishes it, should be retained by the finite semantic type.  For example, FloatLib's
exact `Dyadic` representation stores the sign of a zero mantissa.
-/
inductive NumericalValue (α : Type u) where
  | finite (value : α)
  | infinity (negative : Bool)
  | exceptional (value : ExceptionalValue)
  deriving DecidableEq, Repr

namespace NumericalValue

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Apply a function to an ordinary value while preserving infinities and exceptional values. -/
def map (f : α → β) : NumericalValue α → NumericalValue β
  | .finite x => .finite (f x)
  | .infinity sign => .infinity sign
  | .exceptional e => .exceptional e

/-- Mapping a finite value applies the supplied function to its mathematical payload. -/
@[simp, grind =] theorem map_finite (f : α → β) (value : α) :
    (NumericalValue.finite value).map f = .finite (f value) :=
  rfl

/-- Mapping preserves an infinity, including its sign. -/
@[simp, grind =] theorem map_infinity (f : α → β) (negative : Bool) :
    (NumericalValue.infinity negative).map f = .infinity negative :=
  rfl

/-- Mapping preserves an exceptional value because it has no ordinary payload to transform. -/
@[simp, grind =] theorem map_exceptional (f : α → β) (value : ExceptionalValue) :
    (NumericalValue.exceptional value).map f = .exceptional value :=
  rfl

/-- Extract the ordinary value, returning `none` for infinity or an exceptional encoding. -/
def finite? : NumericalValue α → Option α
  | .finite x => some x
  | .infinity _ | .exceptional _ => none

/-- Whether this semantic value is ordinary and finite. -/
def isFinite : NumericalValue α → Bool
  | .finite _ => true
  | .infinity _ | .exceptional _ => false

/-- Extracting the payload of a finite observation succeeds. -/
@[simp, grind =] theorem finite?_finite (value : α) :
    (NumericalValue.finite value).finite? = some value :=
  rfl

/-- Infinity has no finite payload. -/
@[simp, grind =] theorem finite?_infinity (negative : Bool) :
    (NumericalValue.infinity negative : NumericalValue α).finite? = none :=
  rfl

/-- An exceptional observation has no finite payload. -/
@[simp, grind =] theorem finite?_exceptional (value : ExceptionalValue) :
    (NumericalValue.exceptional value : NumericalValue α).finite? = none :=
  rfl

/-- A finite constructor is recognized as finite. -/
@[simp, grind =] theorem isFinite_finite (value : α) :
    (NumericalValue.finite value).isFinite = true :=
  rfl

/-- Infinity is not finite. -/
@[simp, grind =] theorem isFinite_infinity (negative : Bool) :
    (NumericalValue.infinity negative : NumericalValue α).isFinite = false :=
  rfl

/-- An exceptional observation is not finite. -/
@[simp, grind =] theorem isFinite_exceptional (value : ExceptionalValue) :
    (NumericalValue.exceptional value : NumericalValue α).isFinite = false :=
  rfl

/-- Mapping the identity function leaves every numerical value unchanged. -/
@[simp, grind =] theorem map_id (x : NumericalValue α) : x.map id = x := by
  cases x <;> rfl

/-- Successive maps fuse into a single map of the composed function. -/
@[simp, grind =] theorem map_comp (f : α → β) (g : β → γ) (x : NumericalValue α) :
    (x.map f).map g = x.map (g ∘ f) := by
  cases x <;> rfl

/-- Extracting a finite payload commutes with mapping its scalar value. -/
@[simp, grind =] theorem finite?_map (f : α → β) (x : NumericalValue α) :
    (x.map f).finite? = x.finite?.map f := by
  cases x <;> rfl

end NumericalValue
end FloatLib.Numerics
