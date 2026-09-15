/-
Copyright (c) 2026 Robert Weller
Released under MIT license as described in the file LICENSE.
Authors: Robert Weller
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Backend.Proof
public import FloatLib.Floats.ExecFloat.Core.Capability

/-!
# Default static-byte capability construction

This is the final wiring layer for byte-sized binary families. It packages each family-selected
kernel with the refinement theorem from `Backend.Proof`, then installs the result as an ordinary
`ExecFloat` capability.

Construction is shared so the six operations do not each need a family-specific adapter.
Every `Family` instance uses this construction and supplies its own certified kernel, which may
use a table or compute the operation directly.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

universe u

instance (priority := 100) addCapability
    (F : Type u) [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    @FloatLib.Floats.ExecFloat.Add F (familyEncodedFormat F) planning :=
  FloatLib.Floats.ExecFloat.Capability.ofCertified .add
    (FloatLib.Floats.ExecFloat.Backend.Certified.binary
      (Backend.familyEstimate "addition") Spec.add Backend.add Backend.add_eq_spec)

instance (priority := 100) subCapability
    (F : Type u) [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    @FloatLib.Floats.ExecFloat.Sub F (familyEncodedFormat F) planning :=
  FloatLib.Floats.ExecFloat.Capability.ofCertified .sub
    (FloatLib.Floats.ExecFloat.Backend.Certified.binary
      (Backend.familyEstimate "subtraction") Spec.sub Backend.sub Backend.sub_eq_spec)

instance (priority := 100) mulCapability
    (F : Type u) [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    @FloatLib.Floats.ExecFloat.Mul F (familyEncodedFormat F) planning :=
  FloatLib.Floats.ExecFloat.Capability.ofCertified .mul
    (FloatLib.Floats.ExecFloat.Backend.Certified.binary
      (Backend.familyEstimate "multiplication") Spec.mul Backend.mul Backend.mul_eq_spec)

instance (priority := 100) divCapability
    (F : Type u) [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    @FloatLib.Floats.ExecFloat.Div F (familyEncodedFormat F) planning :=
  FloatLib.Floats.ExecFloat.Capability.ofCertified .div
    (FloatLib.Floats.ExecFloat.Backend.Certified.binary
      (Backend.familyEstimate "division") Spec.div Backend.div Backend.div_eq_spec)

instance (priority := 100) sqrtCapability
    (F : Type u) [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    @FloatLib.Floats.ExecFloat.Sqrt F (familyEncodedFormat F) planning :=
  FloatLib.Floats.ExecFloat.Capability.ofCertified .sqrt
    (FloatLib.Floats.ExecFloat.Backend.Certified.unary
      (Backend.familyEstimate "square root") Spec.sqrt Backend.sqrt Backend.sqrt_eq_spec)

instance (priority := 100) fmaCapability
    (F : Type u) [Family F]
    [planning : FloatLib.Floats.ExecFloat.Backend.PolicyFor F] :
    @FloatLib.Floats.ExecFloat.Fma F (familyEncodedFormat F) planning :=
  FloatLib.Floats.ExecFloat.Capability.ofCertified .fma
    (FloatLib.Floats.ExecFloat.Backend.Certified.ternary
      (Backend.familyEstimate "fused multiply-add") Spec.fma Backend.fma Backend.fma_eq_spec)

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
