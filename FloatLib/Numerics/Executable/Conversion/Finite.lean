/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Conversion.Core

/-!
# Extending finite quantization to all numerical observations

A finite quantizer, its status report, and its mathematical relation are independent of how a
destination handles source infinities and exceptional values. `runFinite` combines them with
explicit handlers, and `implements_runFinite` transports the finite rounding theorem to the
complete conversion contract. `Specials.reject` preserves the source failure, while `Specials.map`
stores a specified value and records that a special value was mapped.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Conversion

open FloatLib.Numerics

universe u v

variable {Exact : Type u} {Destination : Type v}

/-- The complete outcomes chosen for source infinities and exceptional values. -/
structure Specials (Destination : Type v) where
  /-- Outcome for an infinity, retaining its sign as an input to the policy. -/
  infinity : Bool → ConversionOutcome Destination
  /-- Outcome for an exceptional source, retaining its tag as an input to the policy. -/
  exceptional : ExceptionalValue → ConversionOutcome Destination

namespace Specials

/-- Reject a non-finite source with its original sign or exceptional tag. -/
def reject : Specials Destination where
  infinity negative := .failure (.infinity .source negative)
  exceptional value := .failure (.exceptional .source value)

/-- Map every non-finite source to a chosen destination and record the mapping. -/
def map (value : Destination) : Specials Destination where
  infinity _ := .success value { mappedSpecial := true }
  exceptional _ := .success value { mappedSpecial := true }

end Specials

/-- Quantize finite inputs with a status report and dispatch non-finite inputs to their policy. -/
def runFinite (round : Exact → Destination) (report : Exact → Destination → ConversionStatus)
    (specials : Specials Destination) : NumericalValue Exact → ConversionOutcome Destination
  | .finite x => .success (round x) (report x (round x))
  | .infinity negative => specials.infinity negative
  | .exceptional value => specials.exceptional value

/-- A finite result satisfies its rounding relation and reported status; a non-finite result is
the complete outcome chosen by its handler. -/
def FiniteSpec (relation : Exact → Destination → Prop)
    (report : Exact → Destination → ConversionStatus) (specials : Specials Destination)
    (input : NumericalValue Exact) (outcome : ConversionOutcome Destination) : Prop :=
  match input with
  | .finite x => ∃ rounded, outcome = .success rounded (report x rounded) ∧ relation x rounded
  | .infinity negative => outcome = specials.infinity negative
  | .exceptional value => outcome = specials.exceptional value

/-- A finite rounding theorem extends to all inputs under any reporting and special-value policy. -/
theorem implements_runFinite (round : Exact → Destination)
    (relation : Exact → Destination → Prop) (hround : ∀ x, relation x (round x))
    (report : Exact → Destination → ConversionStatus) (specials : Specials Destination)
    (input : NumericalValue Exact) :
    FiniteSpec relation report specials input (runFinite round report specials input) := by
  cases input with
  | finite x => exact ⟨round x, rfl, hround x⟩
  | infinity negative => rfl
  | exceptional value => rfl

end FloatLib.Floats.ExecFloat.Conversion
