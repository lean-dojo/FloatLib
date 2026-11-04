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
specifications, whether you wrote a call such as `ExecFloat.add x y` or notation such as `x + y`. It
knows nothing about IEEE fields, radix arithmetic, exceptional encodings, or a particular backend
family. Format packages may register further semantic rules with `numerics`, but those plugins stay
below this layer.

The equations are ordinary kernel-checked theorems from the capability dictionaries. No axiom is
introduced, and no executable backend is unfolded.
-/

public meta section

namespace FloatLib.Floats.ExecFloat

/--
Rewrite universal `ExecFloat` arithmetic in the goal and local hypotheses to the exact
specifications. When a public-to-specification equality is itself the goal, use `grind` on its own.
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
