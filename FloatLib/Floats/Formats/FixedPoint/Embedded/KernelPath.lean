/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Count
public import FloatLib.Numerics.Quantization.Integer.Shift
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Tactic.CompilerOptimize

/-!
# N1169 countls through integer headroom

WG14 N1169 (2006 TR 18037 draft), C clauses 7.18a.6.4. The direct coefficient
calculation is proved equal to the greatest-shift specification for every format.
Compiled code uses the integer logarithm; the kernel uses FloatLib's existing
proved bit-length path. Zero retains the recommended number of value bits.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics FloatLib.Floats.ExecFloat

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.4, using the shared arbitrary-interval
    headroom calculation. -/
def countlsfxDirect {format : Format} (value : format.Code) : Nat :=
  if bitsfx value = 0 then format.precision
  else format.integerFormat.range.countLeftShifts (bitsfx value)

/-- The direct count is exactly the greatest-shift specification at every precision. -/
@[kernel_optimize (cost := 285)]
theorem countlsfx_eq_direct {format : Format} (value : format.Code) :
    countlsfx value = countlsfxDirect value := by
  by_cases hzero : bitsfx value = 0
  · simp [countlsfxDirect, countlsfx_zero value hzero, hzero]
  · simp only [countlsfxDirect, ite_eq_right hzero]
    have hcharacterize := format.integerFormat.range.le_countLeftShifts_iff
      (IntegerFormat.zero_inRange format.integerFormat) (bitsfx value) value.2 hzero
    apply Nat.le_antisymm
    · exact (hcharacterize _).mpr (countlsfx_in_range value)
    · exact le_countlsfx value hzero _ ((hcharacterize _).mp le_rfl)

/-- Compile the standard operation through its proved direct coefficient calculation. -/
compiled_as countlsfx := countlsfxDirect by countlsfx_eq_direct

/-- Direct compiled certificate for WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.4, with
    no width restriction. -/
@[compiler_optimize direct]
def countlsfxCompiled : Backend.Certified (@countlsfx) where
  estimate := { name := "integer headroom", kind := .generic, steadyCost := 1 }
  run := @countlsfxDirect
  run_eq_spec := by
    funext format value
    exact (countlsfx_eq_direct value).symm

end FloatLib.Floats.Formats.FixedPoint.Embedded
