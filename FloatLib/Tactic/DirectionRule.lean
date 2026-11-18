/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value -- shake: keep

/-!
# The `direction_rule` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath (NatView)

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
`direction_rule name for format := lift, natView [args]` declares `lift_name_eq`: the codec lift of
the model operation `name` in a rounding direction, which is what the mode-taking operation of
configured values runs for a direction without a kernel of its own, equals the kernel operation
`KernelPath.Value.name` in that direction. `natView` is the theorem that turns the codec lift
into the lift of the kernel view.
-/
macro "direction_rule " name:ident " for " format:term:max " := " lift:ident ", " natView:ident
    " [" args:ident* "]" : command => do
  let ruleName := Lean.mkIdent
    (Lean.Name.mkSimple (lift.getId.toString ++ "_" ++ name.getId.toString ++ "_eq"))
  let codecLift := Lean.mkIdent (`FloatLib.Floats.ExecFloat.ModelCodec ++ lift.getId)
  let model := Lean.mkIdent (`Model ++ name.getId)
  let value := Lean.mkIdent (`KernelPath.Value ++ name.getId)
  let valueLift := Lean.mkIdent (`KernelPath.Value ++ name.getId.appendAfter "_eq_lift")
  `(/--
    The operation of configured values in a rounding direction, as the mode-taking operation
    runs it through the model, equals the kernel operation in that direction.
    -/
    @[kernel_optimize] theorem $ruleName {plan : StoragePlan $format}
        (mode : Model.IEEERoundingMode)
        ($args* : FloatLib.Floats.ExecFloat (Family $format (Code plan) plan)) :
        $codecLift (Model := Model $format) (plan := plan)
            (fun $args* => $model $args* (mode := mode)) $args* =
          $value mode $args* := by
      rw [$natView:ident, $valueLift:ident])

end FloatLib.Floats.Formats.BinaryInterchange.Configured
