/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.FormattedProof
public meta import FloatLib.Tactic.Roundoff.Extension
public import FloatLib.Numerics.MixedError.Basic

/-!
# N1169 contracts for `roundoff`

N1169, ISO/IEC TR 18037:2006(E), §4.1.3 and C 7.18a.6.3.
The exact rational error theorems embed into real `MixedError` contracts.
Each optional conversion supplies its successful-result premise. Saturation
remains an explicit part of the budget; an in-range premise removes it.
These local contracts compose through the existing `roundoff` automation.
Only the registration interface is imported here. A client using the tactic
imports `FloatLib.Tactic.Roundoff`, as for the other format families.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.3: adjacent conversion with its rounding and
    saturation budget. -/
@[roundoff_rule]
theorem convert_mixedError (format : Format) (rounding : Rounding)
    (overflow : Overflow) (x : ℚ) (result : format.Code)
    (hresult : convert format rounding overflow x = some result) :
    MixedError (Format.decode result : ℝ) (x : ℝ) 0
      ((format.quantizer.scale * (1 + format.clippingError x) : ℚ) : ℝ) := by
  apply MixedError.of_abs_sub_le
  exact_mod_cast convert_error_le_one format rounding overflow x result hresult

/-- A nearest adjacent choice halves the rounding term; saturation is unchanged. -/
@[roundoff_rule]
theorem convert_nearest_mixedError (format : Format) (rounding : NearestRounding)
    (overflow : Overflow) (x : ℚ) (result : format.Code)
    (hresult : convert format rounding.toRounding overflow x = some result) :
    MixedError (Format.decode result : ℝ) (x : ℝ) 0
      ((format.quantizer.scale * (1 / 2 + format.clippingError x) : ℚ) : ℝ) := by
  apply MixedError.of_abs_sub_le
  exact_mod_cast convert_nearest_error_le_half format rounding overflow x result hresult

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.3: saturated coarse rounding has at most
    half a coarse step of error. -/
@[roundoff_rule]
theorem roundfx_mixedError {format : Format} (rounding : NearestRounding)
    (value result : format.Code) (count : Int)
    (hresult : roundfx rounding value count = some result) :
    MixedError (Format.decode result : ℝ) (Format.decode value : ℝ) 0
      ((format.quantizer.scale *
        ((2 : ℚ) ^ (format.fractionalBits - count.toNat) / 2) : ℚ) : ℝ) := by
  apply MixedError.of_abs_sub_le
  exact_mod_cast roundfx_error_le_half rounding value result count hresult

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1: the implementation-selected arithmetic family,
    including relaxed results. -/
@[roundoff_rule]
theorem Arithmetic.applyWith_mixedError (operation : Arithmetic) (policy : ArithmeticPolicy)
    (format : Format) (rounding : Rounding) (overflow : Overflow)
    (x y exact : ℚ) (result : format.Code)
    (hexact : operation.exact x y = some exact)
    (hresult : operation.applyWith policy format rounding overflow x y = some result) :
    MixedError (Format.decode result : ℝ) (exact : ℝ) 0
      ((format.quantizer.scale * (2 + format.clippingError exact) : ℚ) : ℝ) := by
  apply MixedError.of_abs_sub_le
  exact_mod_cast operation.applyWith_error_le policy format rounding overflow
    x y exact result hexact hresult

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.8: a parsed subject inherits the
    saturated conversion error bound. -/
@[roundoff_rule]
theorem Text.convert_mixedError (format : Format) (rounding : Rounding) (text : String)
    (endptr : Nat) (value : ℚ) (h : Text.scan text = some (endptr, value)) :
    MixedError (Format.decode (Text.convert format rounding text).value : ℝ) (value : ℝ) 0
      ((format.quantizer.scale * (1 + format.clippingError value) : ℚ) : ℝ) :=
  Embedded.convert_mixedError format rounding .SAT value _
    (Text.convert_value_spec format rounding text endptr value h)

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.4.4.2a: all permitted constant translations,
    including exact fract one. -/
@[roundoff_rule]
theorem Constant.translate_mixedError (layout : Layout) (policy : Constant.Policy)
    (literal : Constant.Literal) (result : (layout.format literal.type).Code)
    (hresult : Constant.translate layout policy literal = some result) :
    MixedError (Format.decode result : ℝ) (literal.value : ℝ) 0
      (((layout.format literal.type).quantizer.scale * (3 / 2) : ℚ) : ℝ) := by
  apply MixedError.of_abs_sub_le
  exact_mod_cast Constant.translate_error_le layout policy literal result hresult

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.1: the decimal value printed by any
    adjacent rounding implementation. -/
@[roundoff_rule]
theorem Formatted.decimal_mixedError (rounding : Rounding) (value : ℚ) (places : Nat) :
    MixedError ((Formatted.decimal rounding value places).toRat : ℝ) (value : ℝ) 0
      ((1 / (10 : ℚ) ^ places : ℚ) : ℝ) := by
  apply MixedError.of_abs_sub_le
  exact_mod_cast Formatted.decimal_error_le_one rounding value places

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.2: a successful primary-type input has the
    shared conversion budget. -/
@[roundoff_rule]
theorem Formatted.scanValue_mixedError (format : Format) (rounding : Rounding)
    (value : ℚ) (result : format.Code) (hprimary : format.saturating = false)
    (hresult : Formatted.scanValue format rounding value = some result) :
    MixedError (Format.decode result : ℝ) (value : ℝ) 0
      ((format.quantizer.scale * (1 + format.clippingError value) : ℚ) : ℝ) := by
  rw [Formatted.scanValue_eq_convert format rounding value hprimary] at hresult
  exact convert_mixedError format rounding .DEFAULT value result hresult

end FloatLib.Floats.Formats.FixedPoint.Embedded
