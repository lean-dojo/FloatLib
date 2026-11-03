/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange
meta import Lean.Elab.Command

/-!
# Binary models as conversion sources

A binary `Model` value decodes through the binary signed-rational decoder, so converting it keeps
a negative zero and a NaN's sign and payload, exactly as casting the configured value that stores
it does. This module imports only the binary family, so the decoder it finds cannot come from the
P3109 adapters.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.ModelSource

open FloatLib.Floats
open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

open Lean in
run_cmd do
  for moduleName in (← getEnv).header.moduleNames do
    if (`FloatLib.Floats.Formats.P3109).isPrefixOf moduleName then
      throwError "the binary family import loads the P3109 module {moduleName}"

/-- The binary import supplies the signed-rational model decoder. -/
example :
    (inferInstance : ExecFloat.ExactDecoder (Model FloatFormat.binary32) SignedRat) =
      ExecFloat.Binary.Conversion.modelDecoder FloatFormat.binary32 :=
  rfl

private def negativeZero : Model FloatFormat.binary32 := Model.ofNatBits 0x80000000

private def quietPayload : Model FloatFormat.binary32 := Model.ofNatBits 0x7fc00005

private def signalingPayload : Model FloatFormat.binary32 := Model.ofNatBits 0xff800005

/--
Converting a model keeps a negative zero and a NaN's sign and payload, and a signaling source
raises invalid.
-/
example :
    [ (ExecFloat.convert (target := Binary64) negativeZero).map ExecFloat.Binary.toNatBits
    , (ExecFloat.convert (target := Binary64) quietPayload).map ExecFloat.Binary.toNatBits
    , (ExecFloat.convert (target := Binary64) signalingPayload).map ExecFloat.Binary.toNatBits
    ] =
      [ .success 0x8000000000000000 {}
      , .success 0x7ff8000000000005 {}
      , .success 0xfff8000000000005 { invalid := true }
      ] := by
  decide +kernel

/-- A model converts like the configured value that stores it, for every source word. -/
example (value : Model FloatFormat.binary32) :
    ExecFloat.convert (target := Binary16) value =
      (ExecFloat.Binary.ofModel value : Binary32).cast (target := Binary16) :=
  ExecFloat.Binary.Conversion.convert_model_eq_cast_ofModel value _ _

/--
Mixed arithmetic with model operands keeps the sign of an exact zero and reports a NaN operand
with its payload.
-/
example :
    [ (ExecFloat.Mixed.add (target := Binary32) negativeZero negativeZero).map
        ExecFloat.Binary.toNatBits
    , (ExecFloat.Mixed.mul (target := Binary64) quietPayload (1 : Binary32)).map
        ExecFloat.Binary.toNatBits
    ] =
      [ .success 0x80000000 {}
      , .failure (.exceptional .left (.nan (some 5) false false))
      ] := by
  decide +kernel

end FloatLibTests.Conformance.Formats.ModelSource
