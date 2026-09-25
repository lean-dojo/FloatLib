/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic -- shake: keep

/-!
# Format-independent `ExecFloat` automation

`execfloat_spec` rewrites the six universal public operations to their capability-selected
specifications, both as explicit calls such as `ExecFloat.add x y` and as notation such as
`x + y`. It knows nothing about IEEE fields, radix arithmetic, exceptional encodings, or a
particular backend family. Format packages may register additional semantic rules with
`numerics`, but those plugins remain below this layer.

The equations are ordinary kernel-checked theorems from the capability dictionaries. The
automation introduces no axiom and does not unfold an executable backend.
-/

public meta section

namespace FloatLib.Floats.ExecFloat

/--
Rewrite universal `ExecFloat` arithmetic in the goal and local hypotheses to the exact
specifications. Use `grind` directly when a public-to-specification equality is itself the goal.
-/
syntax (name := execFloatSpec) "execfloat_spec" : tactic

macro_rules
| `(tactic| execfloat_spec) =>
    `(tactic|
      simp_all (failIfUnchanged := false) only [
        FloatLib.Floats.ExecFloat.Proof.add_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.sub_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.mul_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.div_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.add_notation_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.sub_notation_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.mul_notation_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.div_notation_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.sqrt_eq_spec,
        FloatLib.Floats.ExecFloat.Proof.fma_eq_spec
      ])

end FloatLib.Floats.ExecFloat
