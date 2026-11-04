/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Selection.Certified

/-!
# Execution planning for exact logarithmic multiplication

The planner has one candidate for logarithmic multiplication, the direct sign-and-exponent kernel.
That kernel is both what runs and its own reference specification, and its agreement with real
multiplication is `toReal_mul` in `Configured.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Logarithmic.Plan

open FloatLib.Numerics

variable {radix : Radix}

/-- Cost description of sign xor and unbounded-integer exponent addition. -/
def mulEstimate : Backend.Candidate where
  name := "exact logarithmic multiplication"
  kind := .custom "direct logarithmic kernel" 0
  storage := .custom
  steadyCost := 3

/-- The direct logarithmic kernel is its executable specification. -/
def mulCertified :
    Backend.Certified (Logarithmic.mul (radix := radix)) :=
  Backend.Certified.reference mulEstimate Logarithmic.mul

end FloatLib.Floats.ExecFloat.Logarithmic.Plan
