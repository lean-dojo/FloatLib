/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Instances
public import FloatLib.Tactic.CompilerOptimize
public import FloatLib.Tactic.KernelOptimize

/-!
# Posit and IEEE interchange through the common conversion interface

The cross-family adapter lives above both configured format implementations.

Posit Standard (2022), §6.5. These equations specialize generic `cast` to its
two existing exact-domain maps, preserving the destination's proved
quantization relation. The certificates provide reference execution paths;
they assert neither acceleration nor a new rounding theorem.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Posit

open FloatLib.Numerics

variable {posit : Formats.Posit.Format}
  {positPlan : Formats.Posit.Configured.StoragePlan posit} {positCode : Type}
  [ModelCodec positPlan (Formats.Posit.Model posit) positCode]
  {binary : Formats.BinaryInterchange.FloatFormat}
  {binaryPlan : Formats.BinaryInterchange.Configured.StoragePlan binary} {binaryCode : Type}
  [ModelCodec binaryPlan (Formats.BinaryInterchange.Model binary) binaryCode]

local notation "P" =>
  ExecFloat (Formats.Posit.Configured.Family posit positCode positPlan)
local notation "B" =>
  ExecFloat (Formats.BinaryInterchange.Configured.Family binary binaryCode binaryPlan)

/-- Section 6.5 incoming cast forgets the IEEE zero sign and applies default posit conversion. -/
@[kernel_optimize] theorem cast_fromIEEE (value : B) :
    value.cast (target := P) =
      Conversion.run Conversion.Context.default
        ((ExecFloat.Binary.decode value).map SignedRat.value) :=
  rfl

/-- Section 6.5 outgoing cast uses the selected binary direction and the default other policies. -/
@[kernel_optimize] theorem cast_toIEEE (value : P) (mode : RoundingMode) :
    value.cast (target := B) (mode := mode) =
      ExecFloat.Binary.Conversion.run
        (ExecFloat.Binary.Conversion.Policy.default.withRounding mode)
        ((decode value).map SignedRat.ofRat) :=
  rfl

/-- Section 6.5 compiled reference for incoming IEEE values, with independent descriptor codecs. -/
@[compiler_optimize baseline]
def fromIEEEReference : Backend.Certified (fun value : B => value.cast (target := P)) :=
  .reference { name := "IEEE to posit conversion", kind := .generic, steadyCost := 1 }
    (fun value : B => value.cast (target := P))

/-- Section 6.5 compiled reference for outgoing values in each selected binary rounding mode. -/
@[compiler_optimize baseline]
def toIEEEReference :
    Backend.Certified (fun (value : P) (mode : RoundingMode) =>
      value.cast (target := B) (mode := mode)) :=
  .reference { name := "posit to IEEE conversion", kind := .generic, steadyCost := 1 }
    (fun (value : P) (mode : RoundingMode) => value.cast (target := B) (mode := mode))

end FloatLib.Floats.ExecFloat.Posit
