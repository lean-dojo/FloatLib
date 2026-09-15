/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Routes

/-!
# Cost estimates for configured binary execution

These estimates combine arithmetic work with the cost of adapting the selected storage
carrier to the proof model. They influence static backend selection only; no semantic
theorem depends on their calibration.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-! ## Representation-aware cost decoration -/

/--
Estimated cost of adapting one packed public value to and from the proof model.

The count scales with operation arity because every operand is decoded and one result is packed.
The values are calibration priors, not semantic facts. A direct carrier kernel sets this cost to
zero; benchmark calibration may update the constants without changing any refinement theorem.

Byte and machine-word carriers are charged one unit per adapted value, on the same approximate
100 ns scale as the tiny-format arithmetic estimates. Machine-word carriers decode with
`BitVec.ofNatLT` from the stored range proof and pack with one narrowing conversion.

The limb carrier converts each value through `LimbArray.toNat` and `LimbArray.ofNat`, one
arbitrary-precision operation per limb, so its adapter cost grows with the limb count. Accepted
wide-limb paths avoid this conversion; declined calls use the model adapter for the exact fallback.
-/
def modelMarshallingCost {format : FloatFormat}
    (plan : StoragePlan format) (operation : Operation) : Nat :=
  let values := operation.arity + 1
  values *
    match plan with
    | .byte _ => 1
    | .word16 _ => 1
    | .word32 _ => 1
    | .word64 _ => 1
    | .wide => 0
    | .limbs _ => 8 + (format.bitWidth + 31) / 32

/-- Attach the selected storage carrier and model-adapter cost to an arithmetic estimate. -/
def modelAdapterEstimate {format : FloatFormat}
    (plan : StoragePlan format) (operation : Operation) (estimate : Candidate) : Candidate :=
  { estimate with
    storage := plan.storageClass
    marshallingCost := modelMarshallingCost plan operation }

/-- Attach byte storage to a direct table estimate; no model conversion occurs on a warm lookup. -/
def directByteEstimate (format : FloatFormat) (operation : Operation) : Candidate :=
  { Descriptor.Plan.tableEstimate format operation with
    storage := .byte
    marshallingCost := 0 }

/-- Generic kernel estimate for the selected carrier. -/
def genericEstimate {format : FloatFormat}
    (plan : StoragePlan format) (operation : Operation) : Candidate :=
  modelAdapterEstimate plan operation (Descriptor.Plan.genericEstimate format operation)

/-- Estimate for the structural route entered by the executable dispatcher. -/
def structuralEstimate {format : FloatFormat}
    (plan : StoragePlan format) (operation : Operation)
    (route : Descriptor.Plan.StructuralRoute) : Candidate :=
  modelAdapterEstimate plan operation (route.estimate format operation)

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
