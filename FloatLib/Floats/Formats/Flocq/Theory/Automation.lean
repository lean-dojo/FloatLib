/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Arithmetic
public import FloatLib.Numerics.Automation.Numerics -- shake: keep

/-!
# FloatRep rules for numerical automation

The rules expose exact negation and multiplication through the shared operation contracts.
Concrete evaluation reduces only the executable integer carrier; real decoding remains proof-only.
-/

public meta section

namespace FloatLib.Floats.Formats.Flocq.FloatRep

open FloatLib.Numerics

attribute [aesop safe apply (rule_sets := [Numerics])]
  negExact_refines
  mulExact_refines

attribute [numerics_simps]
  toReal_negExact
  toReal_mulExact
  numericalSystem_represents_iff

attribute [numerics_reduction]
  negExact
  mulExact

end FloatLib.Floats.Formats.Flocq.FloatRep
