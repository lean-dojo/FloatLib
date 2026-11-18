/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Rounding

/-!
# N1169 conversion, rounded overflow and saturation

N1169, ISO/IEC TR 18037:2006(E), §4.1.3, C 6.3.1.3a and C 7.18a.5,
with the rounding-before-overflow order specified by Annex G item 2. `convert` reports
undefined unsaturated overflow as `none`. Every adjacent rounding implementation is
supported; saturation reuses the affine quantizer's clamp.

The caller supplies the applicable `FX_FRACT_OVERFLOW` or `FX_ACCUM_OVERFLOW`
state. A `_Sat` destination takes precedence over either pragma.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics FloatLib.Numerics.Quantization

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.5: the two states of either fixed-point
    overflow pragma. -/
inductive Overflow where
  /-- Primary-type overflow has undefined behavior. -/
  | DEFAULT
  /-- Overflow replaces the source by the closest representable endpoint. -/
  | SAT
  deriving DecidableEq, Repr

/-- Reconstruct a `Overflow` constructor from its constructor index. -/
add_decl_doc Overflow.ofNat_ctorIdx

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.3: a saturating type or an enabled pragma requests
    saturation. -/
def Format.Saturates (format : Format) (overflow : Overflow) : Prop :=
  format.saturating = true ∨ overflow = .SAT

instance (format : Format) (overflow : Overflow) :
    Decidable (format.Saturates overflow) :=
  inferInstanceAs (Decidable (format.saturating = true ∨ overflow = .SAT))

/-- Source representability in WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.3a, including
    both endpoints. -/
def Format.SourceInRange (format : Format) (x : ℚ) : Prop :=
  (format.quantizer.qmin : ℚ) ≤ x / format.quantizer.scale ∧
    x / format.quantizer.scale ≤ (format.quantizer.qmax : ℚ)

instance (format : Format) (x : ℚ) : Decidable (format.SourceInRange x) :=
  inferInstanceAs (Decidable
    ((format.quantizer.qmin : ℚ) ≤ x / format.quantizer.scale ∧
      x / format.quantizer.scale ≤ (format.quantizer.qmax : ℚ)))

/-- Common saturating integer-coefficient constructor for the N1169 operation families.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.3.
-/
@[inline] def Format.clamp (format : Format) (coefficient : Int) : format.Code :=
  ⟨format.quantizer.clampCode coefficient, format.quantizer.clampCode_mem coefficient⟩

/-- N1169's overflow step applied to an already rounded integer coefficient.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.3.
-/
def Format.finish (format : Format) (overflow : Overflow) (coefficient : Int) :
    Option format.Code :=
  if format.Saturates overflow ∨ format.integerFormat.InRange coefficient then
    some (format.clamp coefficient)
  else none

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.3, C 6.3.1.3a and Annex G item 2: round, then handle
    overflow.
`none` means undefined unsaturated overflow; the source is an exact rational. -/
@[inline] def convert (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) : Option format.Code :=
  format.finish overflow (rounding.run (x / format.quantizer.scale))

/-- Exact outcome equation for every adjacent conversion and overflow policy. -/
theorem convert_eq_some_iff (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) (value : format.Code) :
    convert format rounding overflow x = some value ↔
      (format.Saturates overflow ∨
        format.integerFormat.InRange (rounding.run (x / format.quantizer.scale))) ∧
        bitsfx value = format.quantizer.clampCode
          (rounding.run (x / format.quantizer.scale)) := by
  unfold convert Format.finish
  split <;> simp_all [Format.clamp, bitsfx, Subtype.ext_iff, eq_comm]

/-- N1169 leaves precisely unsaturated overflow of the rounded coefficient undefined.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.3.
-/
theorem convert_eq_none_iff (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) :
    convert format rounding overflow x = none ↔
      ¬ format.Saturates overflow ∧
        ¬ format.integerFormat.InRange (rounding.run (x / format.quantizer.scale)) := by
  simp [convert, Format.finish]

/-- When the source fits, the selected adjacent coefficient fits without clamping. -/
theorem convert_of_in_range (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) (h : format.SourceInRange x) :
    convert format rounding overflow x =
      fxbits format (rounding.run (x / format.quantizer.scale)) := by
  have hr := rounding.in_range format.integerFormat.range h
  simp only [convert, Format.finish, hr, or_true, ↓reduceIte, fxbits]
  apply congrArg some
  apply Subtype.ext
  exact format.quantizer.clampCode_eq_self hr.1 hr.2

/-- Independent adjacent-grid specification on every source that fits. -/
theorem convert_adjacent (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) (value : format.Code)
    (h : format.SourceInRange x) (hv : convert format rounding overflow x = some value) :
    bitsfx value = (x / format.quantizer.scale).floor ∨
      bitsfx value = (x / format.quantizer.scale).ceil := by
  rw [convert_of_in_range _ _ _ _ h, fxbits_eq_some_iff] at hv
  rw [hv]
  exact rounding.adjacent _

/-- Saturated conversion below the range gives its lower endpoint for every rounder. -/
theorem convert_below (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) (hs : format.Saturates overflow)
    (hx : x / format.quantizer.scale ≤ (format.quantizer.qmin : ℚ)) :
    convert format rounding overflow x = some (format.clamp format.quantizer.qmin) := by
  have hr := rounding.run_le_int hx
  simp only [convert, Format.finish, hs, true_or, ↓reduceIte]
  apply congrArg some
  apply Subtype.ext
  simp only [Format.clamp, AffineQuantizer.clampCode, Saturating.clamp]
  rw [max_eq_left ((min_le_right _ _).trans hr),
    min_eq_right format.quantizer.code_range, max_self]

/-- Saturated conversion above the range gives its upper endpoint for every rounder. -/
theorem convert_above (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) (hs : format.Saturates overflow)
    (hx : (format.quantizer.qmax : ℚ) ≤ x / format.quantizer.scale) :
    convert format rounding overflow x = some (format.clamp format.quantizer.qmax) := by
  have hr := rounding.int_le_run hx
  simp only [convert, Format.finish, hs, true_or, ↓reduceIte]
  apply congrArg some
  apply Subtype.ext
  simp only [Format.clamp, AffineQuantizer.clampCode, Saturating.clamp]
  rw [min_eq_left hr, min_self]

/-- Conversion of a stored value preserves it, independently of rounding and overflow policy. -/
@[simp] theorem convert_decode (format : Format) (rounding : Rounding)
    (overflow : Overflow) (value : format.Code) :
    convert format rounding overflow (Format.decode value) = some value := by
  have hx : Format.decode value / format.quantizer.scale = (value.1 : ℚ) := by
    change format.quantizer.scale * ((value.1 - 0 : Int) : ℚ) /
      format.quantizer.scale = _
    rw [Int.sub_zero, mul_div_cancel_left₀ _ (ne_of_gt format.quantizer.scale_pos)]
  have hr : format.SourceInRange (Format.decode value) := by
    unfold Format.SourceInRange
    rw [hx]
    exact ⟨by exact_mod_cast value.2.1, by exact_mod_cast value.2.2⟩
  rw [convert_of_in_range _ _ _ _ hr, hx, rounding.run_intCast]
  exact fxbits_bitsfx value

end FloatLib.Floats.Formats.FixedPoint.Embedded
