/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Algebraic.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Algebraic.RationalPower.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Elementary.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Functions.Basic
public import FloatLib.Floats.Formats.Posit.Configured.Hyperbolic.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Logarithm.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Pi.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Atan2.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Integer.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Integer.Unsigned.Runtime
public import FloatLib.Floats.Formats.Posit.Formatting.Configured.Runtime
public import FloatLib.Tactic.ReferencePaths

public import FloatLib.Floats.Formats.Posit.Configured.KernelPath
public meta import FloatLib.Tactic.PositStandard
public import FloatLib.Tactic.CompilerOptimize

/-!
# Standard posit arithmetic and comparison names

The Posit Standard (2022), §§5.1–5.5, requires operands of the same width.
These entry points work for every valid width and every invertible carrier
codec. Arithmetic uses the selected certified capability, with `HasSpec`
requiring that capability to implement the posit specification.
The `HasSpec` proof constrains admissible capabilities without entering the
executable body. Only these arithmetic wrappers therefore exempt that
intentional proof constraint from the `unusedArguments` linter; their
function-equality theorems use it.

The arithmetic names unfold to the common operation interface, so its existing
compiled candidates and kernel forms apply. Comparisons reuse the exact model
comparisons: NaR equals itself and is the least signed word. Their compiled
certificates execute that definition; kernel registration unfolds it.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Posit

open FloatLib.Floats.Formats.Posit


/-- Posit Standard (2022), §5.4: exact addition, rounded once; NaR propagates. -/
standard_arithmetic addition (left right) for .add using ExecFloat.add spec Configured.Spec.addition
  /-- Posit Standard (2022), §5.4: every certified addition capability implements the
  configured addition specification as a function. -/
  theorem addition_eq_spec
/-- Posit Standard (2022), §5.4: exact subtraction, rounded once; NaR propagates. -/
standard_arithmetic subtraction (left right) for .sub using ExecFloat.sub
  spec Configured.Spec.subtraction
  /-- Posit Standard (2022), §5.4: every certified subtraction capability implements the
  configured subtraction specification as a function. -/
  theorem subtraction_eq_spec
/-- Posit Standard (2022), §5.4: exact multiplication, rounded once; NaR propagates. -/
standard_arithmetic multiplication (left right) for .mul using ExecFloat.mul
  spec Configured.Spec.multiplication
  /-- Posit Standard (2022), §5.4: every certified multiplication capability implements the
  configured multiplication specification as a function. -/
  theorem multiplication_eq_spec
/-- Posit Standard (2022), §5.4: exact division, rounded once; NaR or zero divisor gives NaR. -/
standard_arithmetic division (left right) for .div using ExecFloat.div spec Configured.Spec.division
  /-- Posit Standard (2022), §5.4: every certified division capability implements the
  configured division specification as a function. -/
  theorem division_eq_spec

/-- Posit Standard (2022), §5.5: square root, rounded once; NaR or negative input gives NaR. -/
standard_arithmetic sqrt (value) for .sqrt using ExecFloat.sqrt spec Configured.Spec.sqrt
  /-- Posit Standard (2022), §5.5: every certified square-root capability implements the
  configured square-root specification as a function. -/
  theorem sqrt_eq_spec


/-- Posit Standard (2022), §5.3: word equality, including NaR with itself. -/
standard_compare compareEqual := Model.compareEqual
/-- Posit Standard (2022), §5.3: word inequality. -/
standard_compare compareNotEqual := Model.compareNotEqual
/-- Posit Standard (2022), §5.3: strict signed-word greater-than. -/
standard_compare compareGreater := Model.compareGreater
/-- Posit Standard (2022), §5.3: signed-word greater-than-or-equal. -/
standard_compare compareGreaterEqual := Model.compareGreaterEqual
/-- Posit Standard (2022), §5.3: strict signed-word less-than, with NaR least. -/
standard_compare compareLess := Model.compareLess
/-- Posit Standard (2022), §5.3: signed-word less-than-or-equal, with NaR least. -/
standard_compare compareLessEqual := Model.compareLessEqual

attribute [compiler_optimize reference] negate compareEqual compareNotEqual
  compareGreater compareGreaterEqual compareLess compareLessEqual

attribute [kernel_optimize unfold] negate addition subtraction multiplication division sqrt
  compareEqual compareNotEqual compareGreater compareGreaterEqual compareLess compareLessEqual

end FloatLib.Floats.ExecFloat.Posit

/-!
# Execution certificates for the standard posit functions

Posit Standard (2022), §§5.2, 5.5–5.8 and 6.3–6.4. Every function already lifts its
model operation through the invertible carrier codec. These reference
certificates and defining-equation kernel fallbacks reuse those definitions.
The companion proof modules establish model refinement, exact real rounding
and the stated exceptional domains at every valid width. No runtime bound
or finite-precision approximation is asserted by a reference certificate.
-/

namespace FloatLib.Floats.ExecFloat.Posit

reference_paths next
reference_paths prior
reference_paths abs
reference_paths sign
reference_paths nearestInt
reference_paths ceil
reference_paths floor
reference_paths rSqrt
reference_paths exp
reference_paths expMinus1
reference_paths exp2
reference_paths exp2Minus1
reference_paths exp10
reference_paths exp10Minus1
reference_paths log
reference_paths logPlus1
reference_paths log2
reference_paths log2Plus1
reference_paths log10
reference_paths log10Plus1
reference_paths sin
reference_paths sinPi
reference_paths cos
reference_paths cosPi
reference_paths tan
reference_paths tanPi
reference_paths arcSin
reference_paths arcSinPi
reference_paths arcCos
reference_paths arcCosPi
reference_paths arcTan
reference_paths arcTanPi
reference_paths sinH
reference_paths cosH
reference_paths tanH
reference_paths arcSinH
reference_paths arcCosH
reference_paths arcTanH
reference_paths hypot
reference_paths pow
reference_paths arcTan2
reference_paths arcTan2Pi
reference_paths fMM
reference_paths compound
reference_paths rootN
reference_paths display
reference_paths parse
reference_paths ofFixedInt
reference_paths toFixedInt
reference_paths ofUnsigned
reference_paths toUnsigned

end FloatLib.Floats.ExecFloat.Posit
