/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Dispatch
public import FloatLib.Floats.ExecFloat.Instances
public import FloatLib.Floats.ExecFloat.Spec.Arithmetic

/-!
# Arithmetic refinement equations

The six `*_eq_spec` theorems rewrite `ExecFloat.add`, `ExecFloat.sub`, `ExecFloat.mul`,
`ExecFloat.div`, `ExecFloat.sqrt`, and `ExecFloat.fma` to the format's reference operations. They
follow from the selected capability's refinement proof. The four `*_notation_eq_spec` theorems
state the same equations for `left + right`, `left - right`, `left * right`, and `left / right`.
Rewriting, `simp`, and `grind` match terms up to reducible unfolding, and notation elaborates to
`HAdd.hAdd` and its siblings rather than to `ExecFloat.add`, so both forms are registered. The
equations hold for built-in and user-defined formats under any supported planning policy.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Proof

open FloatLib.Numerics

universe u

variable {F : Type u} [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]
    [EncodedFormat F]

/--
Executable addition agrees with reference addition. For `left + right`, use `add_notation_eq_spec`.
-/
@[grind =] theorem add_eq_spec [FloatLib.Floats.ExecFloat.Add F]
    (left right : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.add left right =
      FloatLib.Floats.ExecFloat.Spec.add left right :=
  FloatLib.Floats.ExecFloat.Add.run_eq_spec left right

/--
Executable subtraction agrees with reference subtraction. For `left - right`, use
`sub_notation_eq_spec`.
-/
@[grind =] theorem sub_eq_spec [FloatLib.Floats.ExecFloat.Sub F]
    (left right : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.sub left right =
      FloatLib.Floats.ExecFloat.Spec.sub left right :=
  FloatLib.Floats.ExecFloat.Sub.run_eq_spec left right

/--
Executable multiplication agrees with reference multiplication. For `left * right`, use
`mul_notation_eq_spec`.
-/
@[grind =] theorem mul_eq_spec [FloatLib.Floats.ExecFloat.Mul F]
    (left right : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.mul left right =
      FloatLib.Floats.ExecFloat.Spec.mul left right :=
  FloatLib.Floats.ExecFloat.Mul.run_eq_spec left right

/--
Executable division agrees with reference division. For `left / right`, use `div_notation_eq_spec`.
-/
@[grind =] theorem div_eq_spec [FloatLib.Floats.ExecFloat.Div F]
    (left right : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.div left right =
      FloatLib.Floats.ExecFloat.Spec.div left right :=
  FloatLib.Floats.ExecFloat.Div.run_eq_spec left right

/-- The notation `left + right` agrees with reference addition. -/
@[grind =] theorem add_notation_eq_spec [FloatLib.Floats.ExecFloat.Add F]
    (left right : FloatLib.Floats.ExecFloat F) :
    left + right = FloatLib.Floats.ExecFloat.Spec.add left right :=
  FloatLib.Floats.ExecFloat.Add.run_eq_spec left right

/-- The notation `left - right` agrees with reference subtraction. -/
@[grind =] theorem sub_notation_eq_spec [FloatLib.Floats.ExecFloat.Sub F]
    (left right : FloatLib.Floats.ExecFloat F) :
    left - right = FloatLib.Floats.ExecFloat.Spec.sub left right :=
  FloatLib.Floats.ExecFloat.Sub.run_eq_spec left right

/-- The notation `left * right` agrees with reference multiplication. -/
@[grind =] theorem mul_notation_eq_spec [FloatLib.Floats.ExecFloat.Mul F]
    (left right : FloatLib.Floats.ExecFloat F) :
    left * right = FloatLib.Floats.ExecFloat.Spec.mul left right :=
  FloatLib.Floats.ExecFloat.Mul.run_eq_spec left right

/-- The notation `left / right` agrees with reference division. -/
@[grind =] theorem div_notation_eq_spec [FloatLib.Floats.ExecFloat.Div F]
    (left right : FloatLib.Floats.ExecFloat F) :
    left / right = FloatLib.Floats.ExecFloat.Spec.div left right :=
  FloatLib.Floats.ExecFloat.Div.run_eq_spec left right

/-- Executable square root agrees with the format's reference square root. -/
@[grind =] theorem sqrt_eq_spec [FloatLib.Floats.ExecFloat.Sqrt F]
    (value : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.sqrt value =
      FloatLib.Floats.ExecFloat.Spec.sqrt value :=
  FloatLib.Floats.ExecFloat.Sqrt.run_eq_spec value

/-- Executable fused multiply-add agrees with the reference operation supplied by its capability. -/
@[grind =] theorem fma_eq_spec [FloatLib.Floats.ExecFloat.Fma F]
    (left right addend : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.fma left right addend =
      FloatLib.Floats.ExecFloat.Spec.fma left right addend :=
  FloatLib.Floats.ExecFloat.Fma.run_eq_spec left right addend

end FloatLib.Floats.ExecFloat.Proof
