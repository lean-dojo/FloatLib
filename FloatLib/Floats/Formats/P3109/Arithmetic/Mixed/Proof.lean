/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.Runtime
public import FloatLib.Floats.Formats.P3109.Arithmetic.Proof

/-!
# Semantics of mixed and scaled P3109 arithmetic

In mixed arithmetic the source types, their storage representations, and the destination format
can all differ. These results say which exact expression reaches the final destination
projection. Under finite hypotheses it's an ordinary rational expression, and without them the
closed operation keeps the report's NaN and infinity rules.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.9.1, 4.10 and 5.8.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

open ExecFloat

variable {Source SourceExact Left LeftExact Right RightExact Third ThirdExact Result : Type}
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
variable [ExactDecoder Left LeftExact] [ExactMap LeftExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
variable [ExactDecoder Third ThirdExact] [ExactMap ThirdExact Rat]

/-- Generic conversion to P3109 decodes to one report projection of the exact source datum.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.9.1, 4.10 and 5.8.
-/
theorem decode_convert (format : Format) (value : Source) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode (Convert (Destination.p3109 format) value mode saturation))
      (format.projectRatValue { rounding := mode, saturation } (decode value)) :=
  ExecFloat.P3109.decode_projectRat _ mode saturation

/-- An arbitrary mixed unary operation refines the same destination projection. -/
theorem decode_unary (format : Format)
    (operation : NumericalValue Rat → NumericalValue Rat) (value : Source) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (unary (Destination.p3109 format) operation value mode saturation))
      (format.projectRatValue { rounding := mode, saturation } (operation (decode value))) :=
  ExecFloat.P3109.decode_projectRat _ mode saturation

/-- Both independently decoded operands reach the exact closed operation before projection. -/
theorem decode_binary (format : Format)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (left : Left) (right : Right) (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (binary (Destination.p3109 format) operation left right mode saturation))
      (format.projectRatValue { rounding := mode, saturation }
        (operation (decode left) (decode right))) :=
  ExecFloat.P3109.decode_projectRat _ mode saturation

/-- Ternary arithmetic retains all three exact source observations before projection. -/
theorem decode_ternary (format : Format)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat →
      NumericalValue Rat)
    (left : Left) (right : Right) (third : Third) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (ternary (Destination.p3109 format) operation left right third mode saturation))
      (format.projectRatValue { rounding := mode, saturation }
        (operation (decode left) (decode right) (decode third))) :=
  ExecFloat.P3109.decode_projectRat _ mode saturation

/-- Finite mixed FMA passes the exact `x * y + z` to the destination, with no rounded product. -/
theorem fma_eq_project_finite (destination : Destination Result)
    (left : Left) (right : Right) (third : Third) (mode : RoundingMode)
    (saturation : SaturationMode) (x y z : Rat)
    (hx : decode left = .finite x) (hy : decode right = .finite y)
    (hz : decode third = .finite z) :
    FMA destination left right third mode saturation =
      destination.project { rounding := mode, saturation } (.finite (x * y + z)) := by
  simp [FMA, ternary, hx, hy, hz]

/-- Finite mixed FAA passes the exact sum of all three operands to the destination. -/
theorem faa_eq_project_finite (destination : Destination Result)
    (left : Left) (middle : Right) (right : Third) (mode : RoundingMode)
    (saturation : SaturationMode) (x y z : Rat)
    (hx : decode left = .finite x) (hy : decode middle = .finite y)
    (hz : decode right = .finite z) :
    FAA destination left middle right mode saturation =
      destination.project { rounding := mode, saturation } (.finite (x + y + z)) := by
  simp [FAA, ternary, Arithmetic.FAA, Arithmetic.Add, hx, hy, hz]

variable {LeftScale LeftScaleExact RightScale RightScaleExact : Type}
variable [ExactDecoder LeftScale LeftScaleExact] [ExactMap LeftScaleExact Rat]
variable [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]

/-- Scaled operations project the closed operation on exact block-decoded operands. -/
theorem decode_scaledBinary (format : Format)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode (scaledBinary (Destination.p3109 format) operation
        leftScale left rightScale right mode saturation))
      (format.projectRatValue { rounding := mode, saturation }
        (operation (Arithmetic.Multiply (decode leftScale) (decode left))
          (Arithmetic.Multiply (decode rightScale) (decode right)))) :=
  ExecFloat.P3109.decode_projectRat _ mode saturation

/-- Finite scaled addition is the projection of `s * x + t * y`. -/
theorem scaledAdd_eq_project_finite (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode) (saturation : SaturationMode)
    (s x t y : Rat) (hs : decode leftScale = .finite s) (hx : decode left = .finite x)
    (ht : decode rightScale = .finite t) (hy : decode right = .finite y) :
    ScaledAdd destination leftScale left rightScale right mode saturation =
      destination.project { rounding := mode, saturation } (.finite (s * x + t * y)) := by
  simp [ScaledAdd, scaledBinary, Arithmetic.Add, Arithmetic.Multiply, hs, hx, ht, hy]

/-- Finite scaled subtraction is the projection of `s * x - t * y`. -/
theorem scaledSub_eq_project_finite (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode) (saturation : SaturationMode)
    (s x t y : Rat) (hs : decode leftScale = .finite s) (hx : decode left = .finite x)
    (ht : decode rightScale = .finite t) (hy : decode right = .finite y) :
    ScaledSubtract destination leftScale left rightScale right mode saturation =
      destination.project { rounding := mode, saturation } (.finite (s * x - t * y)) := by
  simp [ScaledSubtract, scaledBinary, Arithmetic.Subtract, Arithmetic.Add, Arithmetic.Negate,
    Arithmetic.Multiply,
    hs, hx, ht, hy, sub_eq_add_neg]

/-- Finite scaled multiplication retains both scale products before the final projection. -/
theorem scaledMul_eq_project_finite (destination : Destination Result)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode) (saturation : SaturationMode)
    (s x t y : Rat) (hs : decode leftScale = .finite s) (hx : decode left = .finite x)
    (ht : decode rightScale = .finite t) (hy : decode right = .finite y) :
    ScaledMultiply destination leftScale left rightScale right mode saturation =
      destination.project { rounding := mode, saturation } (.finite ((s * x) * (t * y))) := by
  simp [ScaledMultiply, scaledBinary, Arithmetic.Multiply, hs, hx, ht, hy]

/-- Dividing a closed datum by exact one returns its canonical form: finite values and infinities
are unchanged, and every exceptional value becomes the canonical NaN. -/
theorem div_one (value : NumericalValue Rat) :
    Arithmetic.Divide value (.finite 1) = canonical value := by
  cases value <;> (repeat' cases_type Bool) <;> norm_num [Arithmetic.Divide, canonical]

/-- Closed addition returns canonical data: its only exceptional result is the canonical NaN. -/
theorem canonical_add (left right : NumericalValue Rat) :
    canonical (Arithmetic.Add left right) = Arithmetic.Add left right := by
  cases left <;> cases right <;> simp only [Arithmetic.Add] <;> (try split_ifs) <;> rfl

/-- Closed subtraction returns canonical data: its only exceptional result is the canonical NaN. -/
theorem canonical_sub (left right : NumericalValue Rat) :
    canonical (Arithmetic.Subtract left right) = Arithmetic.Subtract left right :=
  canonical_add left _

/-- Closed multiplication returns canonical data: its only exceptional result is the canonical
NaN. -/
theorem canonical_mul (left right : NumericalValue Rat) :
    canonical (Arithmetic.Multiply left right) = Arithmetic.Multiply left right := by
  cases left <;> cases right <;> simp only [Arithmetic.Multiply] <;> (try split_ifs) <;> rfl

/-- A scaled operation whose closed `operation` returns canonical data, as addition, subtraction
and multiplication do, is the §5.8 operation with an explicit exact result scale of one: dividing
the scaled result by one before the projection changes nothing. -/
theorem scaledBinary_eq_project_div_one (destination : Destination Result)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (hcanonical : ∀ left right, canonical (operation left right) = operation left right)
    (leftScale : LeftScale) (left : Left) (rightScale : RightScale) (right : Right)
    (mode : RoundingMode) (saturation : SaturationMode) :
    scaledBinary destination operation leftScale left rightScale right mode saturation =
      destination.project { rounding := mode, saturation }
        (Arithmetic.Divide (operation (Arithmetic.Multiply (decode leftScale) (decode left))
          (Arithmetic.Multiply (decode rightScale) (decode right))) (.finite 1)) := by
  rw [div_one, hcanonical]
  rfl

end FloatLib.Floats.Formats.P3109.Arithmetic.Mixed
