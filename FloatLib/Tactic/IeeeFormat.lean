/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Decide
public meta import Lean.Elab.Tactic.ElabTerm
public import Mathlib.Init -- Standard source linters.

/-!
# IEEE format side conditions

`ieee_format` first uses a matching local hypothesis, then tries a closed decision.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange

/--
Prove `format.isIEEE = true` from a hypothesis in context that states it, or by `decide` for a
concrete IEEE-encoded format such as `FloatFormat.binary32`.

The hypothesis is tried first and matched up to reducible unfolding only. So other Boolean facts
in context, such as the finiteness of a result, are never evaluated, and a format that only later
arguments fix never reaches `decide` when its proof is in context.

The configured binary theorems take their format proof `hformat` last, with this tactic as its
default. A call on a concrete IEEE format passes no format proof, and a variable format passes
`(hformat := h)` when no hypothesis is in context.
-/
syntax (name := ieeeFormat) "ieee_format" : tactic

macro_rules
  | `(tactic| ieee_format) =>
    `(tactic| first
      | with_reducible assumption
      | decide
      | fail "this theorem needs an IEEE-encoded format. `decide` proves `format.isIEEE = true` \
          for a concrete IEEE format such as binary32. For a variable format, pass the proof as \
          `(hformat := h)`.")

end FloatLib.Floats.Formats.BinaryInterchange
