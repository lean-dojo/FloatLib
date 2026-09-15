/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Configured.Proof
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Info

/-!
# Inspection reports for configured OCP MX values

This optional meta module registers `#float_info` for the common-carrier E8M0 scale and MX block
families. The executable wrappers remain independent of command elaboration and proof-report
rendering.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Configured.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some family ← Inspection.execFamily? typeExpr
          | throwUnsupportedSyntax
        let result ←
          if family.isConstOf
              ``FloatLib.Floats.ExecFloat.OCP.MX.E8M0.Family then
            pure E8M0.FloatInfo.Command.profile
          else if family.isAppOfArity
              ``FloatLib.Floats.ExecFloat.OCP.MX.Block.Family 1 then
            let format := family.getAppArgs[0]!
            let identity ← E8M0.FloatInfo.Command.blockElementIdentity format
            pure (E8M0.FloatInfo.Command.blockProfile identity)
          else
            throwUnsupportedSyntax
        logInfoAt tk <| ← Inspection.renderProfile result typeExpr .none

end FloatLib.Floats.Formats.OCP.MX.Configured.FloatInfo.Command
