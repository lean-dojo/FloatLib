/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.FixedPoint.Embedded.Roundoff
import FloatLib.Tactic.Roundoff

/-! WG14 N1169 (2006 TR 18037 draft), C clause 6.4.4.2a: complete suffix grammar and distinct
translation policies. -/

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.Formats.FixedPoint.Embedded

def smallLayout : Layout where
  fractionalBits := fun _ _ _ ↦ 3
  integralBits := fun _ _ ↦ 2

def summary (text : String) : Option (CType × Rat × Bool) :=
  (Constant.parse text).map fun literal ↦ (literal.type, literal.value, literal.hexadecimal)

example : summary "0X.8P+0uHR" = some (⟨.fract, .short, false, false⟩, 1 / 2, true) := by
  decide +kernel

example : summary "12.5e-1LK" = some (⟨.accum, .long, true, false⟩, 5 / 4, false) := by
  decide +kernel

example : summary "1r" = some (⟨.fract, .default, true, false⟩, 1, false) := by
  decide +kernel

example : summary "-0.5r" = none ∧ summary "+0.5r" = none ∧ summary " 0.5r" = none := by
  decide +kernel

example : summary "0x1r" = none ∧ summary "0.5" = none ∧ summary "1e+r" = none ∧
    summary "0.5ru" = none := by
  decide +kernel

def translateBits (policy : Constant.Policy) (text : String) : Option Int := do
  let literal ← Constant.parse text
  return bitsfx (← Constant.translate smallLayout policy literal)

example : translateBits .even "1r" = some 7 ∧
    translateBits (.neighbor .floor .even false) "1r" = some 7 := by
  decide +kernel

example : translateBits .even "0.90625r" = none := by decide +kernel

example : translateBits .even "0.5r" = some 4 ∧
    translateBits (.neighbor .floor .even false) "0.5r" = some 3 ∧
    translateBits (.neighbor .ceil .even true) "0.5r" = some 5 := by
  decide +kernel

example : translateBits (.neighbor .floor .even false) "0x0.9p0r" = some 4 ∧
    translateBits (.neighbor .ceil .even true) "0x0.9p0r" = some 5 := by
  decide +kernel

example (layout : Layout) (policy : Constant.Policy) (literal : Constant.Literal)
    (hkind : literal.type.kind = .fract) (hvalue : literal.value = 1) :
    Constant.translate layout policy literal = some (layout.format literal.type).maximum :=
  Constant.translate_fract_one layout policy literal hkind hvalue

example (layout : Layout) (policy : Constant.Policy) (literal : Constant.Literal) :
    Constant.translate layout policy literal = none ↔
      ¬ (literal.type.kind = .fract ∧ literal.value = 1) ∧
        ¬ (layout.format literal.type).SourceInRange literal.value :=
  Constant.translate_eq_none_iff layout policy literal

example (layout : Layout) (policy : Constant.Policy) (literal : Constant.Literal)
    (hhex : literal.hexadecimal = true)
    (hrange : (layout.format literal.type).SourceInRange literal.value) :
    bitsfx (Constant.rounded layout policy literal) = policy.hexadecimal.run
      (literal.value / (layout.format literal.type).quantizer.scale) :=
  Constant.rounded_hexadecimal layout policy literal hhex hrange

example (layout : Layout) (policy : Constant.Policy) (literal : Constant.Literal)
    (hdecimal : literal.hexadecimal = false)
    (hrange : (layout.format literal.type).SourceInRange literal.value) :
    |bitsfx (Constant.rounded layout policy literal) - policy.nearest.run
      (literal.value / (layout.format literal.type).quantizer.scale)| ≤ 1 :=
  Constant.rounded_decimal_distance layout policy literal hdecimal hrange

example : Backend.Certified (@Constant.parse) :=
  compiled_reference% (@Constant.parse) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }

example : Backend.Certified (@Constant.translate) :=
  compiled_reference% (@Constant.translate) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }

example : Backend.Certified (@Constant.rounded) :=
  compiled_reference% (@Constant.rounded) using
    { name := "fixed-point reference", kind := .generic, steadyCost := 1 }

example (format : Format) (h : format.integralBits = 0) :
    Format.decode format.maximum = 1 - format.quantizer.scale :=
  format.decode_maximum_fract h

example (layout : Layout) (policy : Constant.Policy) (literal : Constant.Literal)
    (result : (layout.format literal.type).Code)
    (hresult : Constant.translate layout policy literal = some result) :
    |Format.decode result - literal.value| ≤
      (layout.format literal.type).quantizer.scale * (3 / 2) :=
  Constant.translate_error_le layout policy literal result hresult

example (layout : Layout) (policy : Constant.Policy) (literal : Constant.Literal)
    (result : (layout.format literal.type).Code)
    (hresult : Constant.translate layout policy literal = some result) :
    FloatLib.Numerics.MixedError (-(Format.decode result : ℝ)) (-(literal.value : ℝ)) 0
      (((layout.format literal.type).quantizer.scale * (3 / 2) : ℚ) : ℝ) := by
  have h := Constant.translate_mixedError layout policy literal result hresult
  roundoff
