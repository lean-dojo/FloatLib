/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime

/-!
# Exactly rounded posit algebraic functions

Reciprocal square root, hypotenuse, and fused triple multiplication evaluate their rational
intermediates exactly and round only the final result. In particular, an intermediate product
cannot overflow or underflow the posit format. Square roots use exact comparisons with squared
posit rounding boundaries, including the standard's appended-bit tie rule.

## Reference

* [Posit Standard (2022), §§4.1–4.2 and 5.5–5.7](https://posithub.org/docs/posit_standard-2.pdf)
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/--
Reciprocal square root, rounded once. Nonpositive inputs and NaR produce NaR.

The exact identity `1 / sqrt x = sqrt (1 / x)` reduces this operation to rational square-root
rounding without first rounding either the reciprocal or the square root.
-/
@[inline] def rSqrt (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some q => if q ≤ 0 then nar format else roundSqrtRat format q⁻¹

/-- Hypotenuse `sqrt (a² + b²)`, rounded once; either NaR input produces NaR. -/
@[inline] def hypot (left right : Model format) : Model format :=
  match left.toRat?, right.toRat? with
  | some a, some b => roundSqrtRat format (a * a + b * b)
  | _, _ => nar format

/-- Fused triple multiplication `a * b * c`, rounded once; any NaR input produces NaR. -/
@[inline] def fMM (left right third : Model format) : Model format :=
  match left.toRat?, right.toRat?, third.toRat? with
  | some a, some b, some c => roundRat format (a * b * c)
  | _, _, _ => nar format

end FloatLib.Floats.Formats.Posit.Model
