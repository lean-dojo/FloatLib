/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Runtime
public import FloatLib.Floats.Formats.P3109.Functions.Runtime

/-!
# P3109 block elementary functions

The unapproved P3109 interim report v4.1 report, §§5.3–5.4 and §5.7, normalizes the
exact function value at the result scale before rounding. Finite nonzero
scales use rational affine expressions; other cases reuse rational block
normalization with an exact sign witness when needed.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109

open FloatLib.Numerics FloatLib.Floats.ExecFloat

namespace FunctionBlock

/-- A rational representative of an expression's exact sign, for infinite result scales. -/
def signWitness (expression : FunctionExpr) : Rat :=
  match (expression.prepare 8).compare 0 with
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- P3109 interim report v4.1 §5.4.2: normalize a closed exact expression before any destination
    rounding. -/
def normalize (scale : NumericalValue Rat) :
    NumericalValue FunctionExpr → NumericalValue FunctionExpr
  | .finite expression =>
      match scale with
      | .finite value =>
          .finite (if value = 0 then .rational 0 else .affine (1 / value) 0 expression)
      | .infinity negative =>
          (Block.normalize (.infinity negative) (.finite (signWitness expression))).map
            FunctionExpr.rational
      | .exceptional _ => .exceptional .nan
  | .infinity negative =>
      (Block.normalize scale (.infinity negative)).map FunctionExpr.rational
  | .exceptional category =>
      (Block.normalize scale (.exceptional category)).map FunctionExpr.rational

end FunctionBlock

namespace Block

variable {length : ℕ+}
variable {Scale ScaleExact Source SourceExact ResultScale ResultScaleExact : Type}
variable [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
variable [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]

/-- P3109 interim report v4.1, §5.4.2: normalize and project exact function lanes, retaining the
    given result scale. -/
def projectFunctions (format : Format) (policy : BlockPolicy length) (scale : ResultScale)
    (expressions : Vector (NumericalValue FunctionExpr) length) :
    Block ResultScale (ExecFloat.P3109 format) length :=
  let exactScale := Arithmetic.Mixed.decode scale
  ⟨scale, Vector.ofFn fun lane : Fin (length : Nat) =>
    ExecFloat.P3109.projectFunction
      (FunctionBlock.normalize exactScale expressions[lane.val])
      (policy.at lane).rounding (policy.at lane).saturation⟩

/-- P3109 interim report v4.1, §5.7: evaluate a unary function on each exact decoded lane before
    normalization. -/
def unaryFunction (format : Format) (policy : BlockPolicy length)
    (operation : Functions.Unary) (block : Block Scale Source length) (resultScale : ResultScale) :
    Block ResultScale (ExecFloat.P3109 format) length :=
  projectFunctions format policy resultScale ((decode block).map (Functions.unary operation))

variable {RightScale RightScaleExact Right RightExact : Type}
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]

/-- P3109 interim report v4.1, §5.7: two-argument inverse tangent of exact lanes, normalized
    before projection. -/
def angleFunction (format : Format) (policy : BlockPolicy length) (piScaled : Bool)
    (y : Block Scale Source length) (x : Block RightScale Right length)
    (resultScale : ResultScale) : Block ResultScale (ExecFloat.P3109 format) length :=
  let yValues := decode y
  let xValues := decode x
  projectFunctions format policy resultScale (Vector.ofFn fun lane : Fin (length : Nat) =>
    Functions.arcTan2 piScaled yValues[lane.val] xValues[lane.val])

end Block
end FloatLib.Floats.Formats.P3109
