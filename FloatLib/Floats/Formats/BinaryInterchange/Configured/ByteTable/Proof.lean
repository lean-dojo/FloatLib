/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs

/-!
# Correctness of configured binary byte tables

These theorems connect direct table execution to the representation-independent configured
operations. They apply to every binary-interchange descriptor whose complete encoding fits in
eight bits.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

variable {format : FloatFormat}

/-- A direct binary-table call is exactly the configured lifted model operation. -/
theorem runBinary_eq_lift
    {modelSpec : Model format → Model format → Model format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedBinary (encoding format width_le_eight) modelSpec)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le_eight)) (.byte width_le_eight))) :
    runBinary width_le_eight kernel left right =
      ModelCodec.liftBinary
        (F := Family format
          (Code (StoragePlan.byte width_le_eight))
          (StoragePlan.byte width_le_eight))
        (Model := Model format) (plan := StoragePlan.byte width_le_eight)
        modelSpec left right := by
  unfold runBinary
  apply ModelCodec.applyBinary_eq_lift
  exact kernel.decodeCode_run

/-- A direct unary-table call is exactly the configured lifted model operation. -/
theorem runUnary_eq_lift
    {modelSpec : Model format → Model format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedUnary (encoding format width_le_eight) modelSpec)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le_eight)) (.byte width_le_eight))) :
    runUnary width_le_eight kernel value =
      ModelCodec.liftUnary
        (F := Family format
          (Code (StoragePlan.byte width_le_eight))
          (StoragePlan.byte width_le_eight))
        (Model := Model format) (plan := StoragePlan.byte width_le_eight)
        modelSpec value := by
  unfold runUnary
  apply ModelCodec.applyUnary_eq_lift
  exact kernel.decodeCode_run

/-- A direct ternary-table call is exactly the configured lifted model operation. -/
theorem runTernary_eq_lift
    {modelSpec : Model format → Model format → Model format → Model format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedTernary (encoding format width_le_eight) modelSpec)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le_eight)) (.byte width_le_eight))) :
    runTernary width_le_eight kernel left right addend =
      ModelCodec.liftTernary
        (F := Family format
          (Code (StoragePlan.byte width_le_eight))
          (StoragePlan.byte width_le_eight))
        (Model := Model format) (plan := StoragePlan.byte width_le_eight)
        modelSpec left right addend := by
  unfold runTernary
  apply ModelCodec.applyTernary_eq_lift
  exact kernel.decodeCode_run

end FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable
