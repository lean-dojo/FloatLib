/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Conformance.BinaryInterchange.BoundaryCases
public import FloatLibTests.Conformance.BinaryInterchange.ExactAutomation
public import FloatLibTests.Conformance.BinaryInterchange.ExecComplexAutomation
public import FloatLibTests.Conformance.BinaryInterchange.ExecFloatAutomation
public import FloatLibTests.Conformance.BinaryInterchange.NativeModel
public import FloatLibTests.Conformance.Execution.AutomaticDispatch
public import FloatLibTests.Conformance.Execution.Capabilities
public import FloatLibTests.Conformance.Execution.Certificates
public import FloatLibTests.Conformance.Formats.Configured
public import FloatLibTests.Conformance.Formats.ConfiguredIntervals
public import FloatLibTests.Conformance.Formats.Conversion
public import FloatLibTests.Conformance.Formats.LowBit
public import FloatLibTests.Conformance.Formats.NonBinaryIntervals
public import FloatLibTests.Conformance.Numerics.Boolean
public import FloatLibTests.Conformance.Numerics.Declaration
public import FloatLibTests.Conformance.Numerics.FixedInt
public import FloatLibTests.Conformance.Numerics.FixedPoint
public import FloatLibTests.Conformance.Numerics.GenericIntervals
public import FloatLibTests.Conformance.Numerics.Quantization.Affine
public import FloatLibTests.Conformance.Numerics.Quantization.Interfaces
public import FloatLibTests.Conformance.Numerics.Quantization.RealAffine
public import FloatLibTests.Conformance.Numerics.Reduction
public import FloatLibTests.Conformance.Numerics.Automation
public import FloatLibTests.Conformance.P3109.Projection
public import FloatLibTests.Conformance.Posit
public import FloatLibTests.Conformance.Trust.Axioms
public import FloatLibTests.Conformance.Trust.RootImports

/-!
# Conformance gates

These modules audit the public refinement boundary and exercise format-independent automation for
floating-point, fixed-point, integer, Boolean, and quantized representations. General results and
small closed cases use kernel reduction; reviewed `native_decide` sites cover larger finite
execution boundaries. Host-FPU and external numerical-oracle checks remain outside this module.
-/

@[expose] public section
