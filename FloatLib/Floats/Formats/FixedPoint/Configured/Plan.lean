/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Configured.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Selection.Certified

/-!
# Execution planning for exact fixed-point arithmetic

For exact fixed point, each direct integer-coefficient operation is both the executable
implementation and its own reference specification.

Same-scale addition and subtraction need no rounding, so this plan registers their direct
implementations with `ExecFloat`. Their rational exactness is proved in `Configured.Proof`.
Conversions and scale-composing multiplication have APIs of their own.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.FixedPoint.Plan

open FloatLib.Numerics

variable {radix : Radix} {fractionalDigits : Nat}

/-- Cost description of direct unbounded-integer coefficient arithmetic. -/
def estimate (operation : Backend.Operation) : Backend.Candidate where
  name := s!"exact fixed-point {repr operation}"
  kind := .custom "direct integer-coefficient kernel" 0
  storage := .custom
  steadyCost :=
    match operation with
    | .add | .sub => 2
    | _ => 3

/-- Certified exact same-scale addition. -/
def addCertified :
    Backend.Certified (FixedPoint.add (radix := radix)
      (fractionalDigits := fractionalDigits)) :=
  Backend.Certified.reference (estimate .add) FixedPoint.add

/-- Certified exact same-scale subtraction. -/
def subCertified :
    Backend.Certified (FixedPoint.sub (radix := radix)
      (fractionalDigits := fractionalDigits)) :=
  Backend.Certified.reference (estimate .sub) FixedPoint.sub

end FloatLib.Floats.ExecFloat.FixedPoint.Plan
