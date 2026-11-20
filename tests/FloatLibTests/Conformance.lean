/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLibTests.Conformance.BinaryInterchange.BoundaryCases
public import FloatLibTests.Conformance.BinaryInterchange.ComplexElementary
public import FloatLibTests.Conformance.BinaryInterchange.ComplexErrorBounds
public import FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded
public import FloatLibTests.Conformance.BinaryInterchange.Expm1x
public import FloatLibTests.Conformance.BinaryInterchange.KernelCoverage
public import FloatLibTests.Conformance.BinaryInterchange.KernelDirected
public import FloatLibTests.Conformance.BinaryInterchange.MixedError
public import FloatLibTests.Conformance.BinaryInterchange.NativeModel
public import FloatLibTests.Conformance.Execution.AutomaticDispatch
public import FloatLibTests.Conformance.Execution.Capabilities
public import FloatLibTests.Conformance.Execution.Certificates
public import FloatLibTests.Conformance.Formats.BinaryConveniences
public import FloatLibTests.Conformance.Formats.DecimalRecommended
public import FloatLibTests.Conformance.Formats.DecimalFunctions
public import FloatLibTests.Conformance.Formats.DecimalRecommendedFunctions
public import FloatLibTests.Conformance.Formats.IEEENames
public import FloatLibTests.Conformance.BinaryInterchange.Recommended
public import FloatLibTests.Conformance.BinaryInterchange.RecommendedFunctions
public import FloatLibTests.Conformance.BinaryInterchange.DirectedFunctions
public import FloatLibTests.Conformance.BinaryInterchange.RecommendedKernelPath
public import FloatLibTests.Conformance.BinaryInterchange.ReductionSchedule
public import FloatLibTests.Conformance.BinaryInterchange.FormatOf
public import FloatLibTests.Conformance.Formats.Extensions
public import FloatLibTests.Conformance.Formats.KernelPaths
public import FloatLibTests.Conformance.Formats.BlockBackend
public import FloatLibTests.Conformance.Formats.BlockExamples
public import FloatLibTests.Conformance.Formats.BlockTheory
public import FloatLibTests.Conformance.Formats.BlockWorking
public import FloatLibTests.Conformance.Formats.Configured
public import FloatLibTests.Conformance.Formats.Conversion
public import FloatLibTests.Conformance.Formats.EmbeddedFixedPoint
public import FloatLibTests.Conformance.Formats.EmbeddedText
public import FloatLibTests.Conformance.Formats.EmbeddedConstant
public import FloatLibTests.Conformance.Formats.EmbeddedCoefficient
public import FloatLibTests.Conformance.Formats.EmbeddedFormatted
public import FloatLibTests.Tactic.FloatInfo
public import FloatLibTests.Conformance.Formats.LowBit
public import FloatLibTests.Conformance.Formats.MXStandard
public import FloatLibTests.Conformance.Formats.ModelSource
public import FloatLibTests.Conformance.Numerics.Boolean
public import FloatLibTests.Conformance.Numerics.Coeff
public import FloatLibTests.Conformance.Numerics.FixedInt
public import FloatLibTests.Conformance.Numerics.FixedPoint
public import FloatLibTests.Conformance.Numerics.KernelComplex
public import FloatLibTests.Conformance.Numerics.KernelExact
public import FloatLibTests.Conformance.Numerics.KernelSearch
public import FloatLibTests.Conformance.Numerics.MagnitudeRounding
public import FloatLibTests.Conformance.Numerics.Packed
public import FloatLibTests.Conformance.Numerics.Quantization.Affine
public import FloatLibTests.Conformance.Numerics.Quantization.Interfaces
public import FloatLibTests.Conformance.Numerics.Quantization.RealAffine
public import FloatLibTests.Conformance.Numerics.Reduction
public import FloatLibTests.Conformance.Numerics.Wiener
public import FloatLibTests.Tactic.Numerics
public import FloatLibTests.Conformance.OCP.OFP8
public import FloatLibTests.Conformance.OCP.OFP8Classification
public import FloatLibTests.Conformance.OCP.MX
public import FloatLibTests.Conformance.OCP.MXFiniteReduction
public import FloatLibTests.Conformance.P3109.Arithmetic
public import FloatLibTests.Conformance.P3109.Block
public import FloatLibTests.Conformance.P3109.Projection
public import FloatLibTests.Conformance.P3109.Standard
public import FloatLibTests.Conformance.P3109.Functions
public import FloatLibTests.Conformance.P3109.RecommendedFunctions
public import FloatLibTests.Conformance.P3109.BlockFunctions
public import FloatLibTests.Conformance.Posit
public import FloatLibTests.Conformance.Posit.General
public import FloatLibTests.Conformance.Posit.Standard
public import FloatLibTests.Conformance.Trust.Axioms
public import FloatLibTests.Conformance.Trust.RootImports
public import FloatLibTests.Tactic.CompilerOptimize
public import FloatLibTests.Tactic.ExecFloatSpec
public import FloatLibTests.Tactic.FloatFormat
public import FloatLibTests.Tactic.FloatInfo.BinaryInterchange
public import FloatLibTests.Tactic.FloatInfo.Block
public import FloatLibTests.Tactic.FloatInfo.Imports
public import FloatLibTests.Tactic.Interval
public import FloatLibTests.Tactic.Interval.Coeff
public import FloatLibTests.Tactic.Interval.Configured
public import FloatLibTests.Tactic.Interval.Constants
public import FloatLibTests.Tactic.Interval.Constraints
public import FloatLibTests.Tactic.Interval.Extensions
public import FloatLibTests.Tactic.Interval.NonBinary
public import FloatLibTests.Tactic.KernelOptimize
public import FloatLibTests.Tactic.KernelTwin
public import FloatLibTests.Tactic.Numerics.Complex
public import FloatLibTests.Tactic.Numerics.Exact
public import FloatLibTests.Tactic.PackedValues
public import FloatLibTests.Tactic.Roundoff
public import FloatLibTests.Tactic.Roundoff.Backward
public import FloatLibTests.Tactic.Roundoff.Block
public import FloatLibTests.Tactic.Roundoff.Callbacks
public import FloatLibTests.Tactic.Roundoff.Cases
public import FloatLibTests.Tactic.Roundoff.Check
public import FloatLibTests.Tactic.Roundoff.Closed
public import FloatLibTests.Tactic.Roundoff.Expm1x
public import FloatLibTests.Tactic.Roundoff.GivenFacts
public import FloatLibTests.Tactic.Roundoff.Guards
public import FloatLibTests.Tactic.Roundoff.Kernels
public import FloatLibTests.Tactic.Roundoff.MixedPrecision
public import FloatLibTests.Tactic.Roundoff.Native
public import FloatLibTests.Tactic.Roundoff.Options
public import FloatLibTests.Tactic.Roundoff.Reads
public import FloatLibTests.Tactic.Roundoff.Regressions
public import FloatLibTests.Tactic.Roundoff.Shape
public import FloatLibTests.Tactic.Roundoff.StepRelations
public import FloatLibTests.Tactic.Roundoff.Tightness
public import FloatLibTests.Tactic.Roundoff.Tuples

public import FloatLibTests.Tactic.FloatDecide
public import FloatLibTests.Tactic.KernelEval
public import FloatLibTests.Tactic.KernelRefl
public import FloatLibTests.Tactic.KernelShape
public import FloatLibTests.Tactic.LaneDecide
public import FloatLibTests.Tactic.LaneTable
public import FloatLibTests.Tactic.PackedRow

/-!
# Conformance gates

These modules audit the public refinement boundary and exercise format-independent automation for
floating-point, fixed-point, integer, Boolean, and quantized representations. General results and
small closed cases use kernel reduction, and reviewed `native_decide` sites cover larger finite
execution boundaries. Host-FPU and external numerical-oracle checks are outside this module.
-/

@[expose] public section
