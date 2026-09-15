/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Comparison
public import FloatLib.Floats.ExecFloat.Dispatch

/-!
# Ordinary notation for `ExecFloat`

Ordinary operators call the selected `ExecFloat` operations. Each instance requires the
corresponding arithmetic or comparison capability. Formats whose values have a lawful total
order provide their own `LinearOrder`.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

universe u

variable {F : Type u} [EncodedFormat F] [ExecFloat.Backend.PolicyFor F]

/-- `+` is ordinary notation for the public format-selected addition capability. -/
instance execFloatAdd [ExecFloat.Add F] : Add (ExecFloat F) where
  add := ExecFloat.add

/-- `-` is ordinary notation for the public format-selected subtraction capability. -/
instance execFloatSub [ExecFloat.Sub F] : Sub (ExecFloat F) where
  sub := ExecFloat.sub

/-- `*` is ordinary notation for the public format-selected multiplication capability. -/
instance execFloatMul [ExecFloat.Mul F] : Mul (ExecFloat F) where
  mul := ExecFloat.mul

/-- `/` is ordinary notation for the public format-selected division capability. -/
instance execFloatDiv [ExecFloat.Div F] : Div (ExecFloat F) where
  div := ExecFloat.div

/-- `==` uses the format-defined comparison rather than structural code equality. -/
instance (priority := 2000) execFloatBEq [ExecFloat.Comparison F] :
    BEq (ExecFloat F) where
  beq := ExecFloat.compareEqual

end FloatLib.Floats
