/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.ByteTable.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof
public import Mathlib.Analysis.Real.Sqrt

/-!
# Correctness of byte-sized posit tables

The generic byte encoding agrees with configured posit decoding, and every direct table call
implements the corresponding carrier-independent configured operation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.ByteTable

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

variable {format : Format}

/-- Generic byte decoding is definitionally the configured posit byte decoder. -/
@[simp, grind =] theorem decodeCode_eq_toModel
    (width_le : format.bits ≤ 8) (code : ByteCode format) :
    (encoding format width_le).decodeCode code =
      Code.toModel (plan := .byte width_le) code :=
  rfl

/-- A direct binary-table call is exactly the configured lifted model operation. -/
theorem runBinary_eq_lift
    {modelSpec : Model format → Model format → Model format}
    (width_le : format.bits ≤ 8)
    (kernel : TinyTable.CertifiedBinary (encoding format width_le) modelSpec)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le)) (.byte width_le))) :
    runBinary width_le kernel left right =
      ModelCodec.liftBinary
        (F := Family format
          (Code (StoragePlan.byte width_le))
          (StoragePlan.byte width_le))
        (Model := Model format) (plan := StoragePlan.byte width_le)
        modelSpec left right := by
  unfold runBinary
  apply ModelCodec.applyBinary_eq_lift
  exact kernel.decodeCode_run

/-- A direct unary-table call is exactly the configured lifted model operation. -/
theorem runUnary_eq_lift
    {modelSpec : Model format → Model format}
    (width_le : format.bits ≤ 8)
    (kernel : TinyTable.CertifiedUnary (encoding format width_le) modelSpec)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le)) (.byte width_le))) :
    runUnary width_le kernel value =
      ModelCodec.liftUnary
        (F := Family format
          (Code (StoragePlan.byte width_le))
          (StoragePlan.byte width_le))
        (Model := Model format) (plan := StoragePlan.byte width_le)
        modelSpec value := by
  unfold runUnary
  apply ModelCodec.applyUnary_eq_lift
  exact kernel.decodeCode_run

/-- A direct ternary-table call is exactly the configured lifted model operation. -/
theorem runTernary_eq_lift
    {modelSpec : Model format → Model format → Model format → Model format}
    (width_le : format.bits ≤ 8)
    (kernel : TinyTable.CertifiedTernary (encoding format width_le) modelSpec)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.byte width_le)) (.byte width_le))) :
    runTernary width_le kernel left right addend =
      ModelCodec.liftTernary
        (F := Family format
          (Code (StoragePlan.byte width_le))
          (StoragePlan.byte width_le))
        (Model := Model format) (plan := StoragePlan.byte width_le)
        modelSpec left right addend := by
  unfold runTernary
  apply ModelCodec.applyTernary_eq_lift
  exact kernel.decodeCode_run

end FloatLib.Floats.Formats.Posit.Configured.ByteTable
