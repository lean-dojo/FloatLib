/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.KernelPath
public meta import FloatLib.Tactic.EmbeddedStandard
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Coefficient
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Limits
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Text
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Constant
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Formatted
public import FloatLib.Tactic.ReferencePaths

/-!
# The N1169 stdfix spellings

N1169, ISO/IEC TR 18037:2006(E), C 7.18a.2–3 and 7.18a.6 supplies the names below.
Each length is selected from an arbitrary `Layout`; no host word size is hardcoded.
One implementation and proof serve each operation family. The named entry points
are generated specializations, with compiled reference certificates and kernel
defining equations. These equations are fallbacks after cheaper proved replacements;
eager selector unfolding would hide the coefficient paths before rule selection.
The WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.2–3 integer-type and limit names retain
    their required underscores;
only these generated standard spellings are exempt from `defsWithUnderscore`.

The C integer result and argument types are supplied as mathematical integers or an
`IntegerFormat`, independently of ABI names such as `int` and `long`. Their range
conditions remain explicit. Text conversion models the C locale and records end
and range outcomes. Formatted conversion handles one resolved numeric field.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics FloatLib.Floats.ExecFloat

-- Expose coefficient arithmetic to the existing integer and bit-length rules.
-- Endpoint theorems avoid recomputing generic signed-word bounds through rationals.
attribute [kernel_optimize] Unary.negateCoefficient.eq_def Unary.updateCoefficient.eq_def
  shiftCoefficient.eq_def Format.finish.eq_def Format.clamp.eq_def Format.Saturates.eq_def
  Format.width.eq_def Format.precision.eq_def Format.quantizer.eq_def
  Format.minValue_eq Format.maxValue_eq
  Quantization.AffineQuantizer.clampCode.eq_def Quantization.Saturating.clamp.eq_def
  countlsfxDirect.eq_def IntegerRange.countLeftShifts.eq_def IntegerRange.shiftCapacity.eq_def
  IntegerFormat.range.eq_def IntegerFormat.InRange.eq_def IntegerRange.Contains.eq_def

reference_paths Formatted.fprintf
reference_paths Formatted.fscanf
reference_paths Formatted.decimal
reference_paths Formatted.formatValue
reference_paths Formatted.scan
reference_paths Formatted.scanValue


stdfix_limits SFRACT int_hr_t for .fract, .short, true
stdfix_limits FRACT int_r_t for .fract, .default, true
stdfix_limits LFRACT int_lr_t for .fract, .long, true
stdfix_limits USFRACT uint_uhr_t for .fract, .short, false
stdfix_limits UFRACT uint_ur_t for .fract, .default, false
stdfix_limits ULFRACT uint_ulr_t for .fract, .long, false
stdfix_limits SACCUM int_hk_t for .accum, .short, true
stdfix_limits ACCUM int_k_t for .accum, .default, true
stdfix_limits LACCUM int_lk_t for .accum, .long, true
stdfix_limits USACCUM uint_uhk_t for .accum, .short, false
stdfix_limits UACCUM uint_uk_t for .accum, .default, false
stdfix_limits ULACCUM uint_ulk_t for .accum, .long, false


stdfix_min SFRACT_MIN for .fract, .short
stdfix_min FRACT_MIN for .fract, .default
stdfix_min LFRACT_MIN for .fract, .long
stdfix_min SACCUM_MIN for .accum, .short
stdfix_min ACCUM_MIN for .accum, .default
stdfix_min LACCUM_MIN for .accum, .long


stdfix_ibit SACCUM_IBIT for .short, true
stdfix_ibit ACCUM_IBIT for .default, true
stdfix_ibit LACCUM_IBIT for .long, true
stdfix_ibit USACCUM_IBIT for .short, false
stdfix_ibit UACCUM_IBIT for .default, false
stdfix_ibit ULACCUM_IBIT for .long, false


stdfix_text strtofxhr for .fract, .short, true
stdfix_text strtofxr for .fract, .default, true
stdfix_text strtofxlr for .fract, .long, true
stdfix_text strtofxuhr for .fract, .short, false
stdfix_text strtofxur for .fract, .default, false
stdfix_text strtofxulr for .fract, .long, false
stdfix_text strtofxhk for .accum, .short, true
stdfix_text strtofxk for .accum, .default, true
stdfix_text strtofxlk for .accum, .long, true
stdfix_text strtofxuhk for .accum, .short, false
stdfix_text strtofxuk for .accum, .default, false
stdfix_text strtofxulk for .accum, .long, false


stdfix roundhr countlshr bitshr hrbits for .fract, .short, true
stdfix roundr countlsr bitsr rbits for .fract, .default, true
stdfix roundlr countlslr bitslr lrbits for .fract, .long, true
stdfix roundhk countlshk bitshk hkbits for .accum, .short, true
stdfix roundk countlsk bitsk kbits for .accum, .default, true
stdfix roundlk countlslk bitslk lkbits for .accum, .long, true
stdfix rounduhr countlsuhr bitsuhr uhrbits for .fract, .short, false
stdfix roundur countlsur bitsur urbits for .fract, .default, false
stdfix roundulr countlsulr bitsulr ulrbits for .fract, .long, false
stdfix rounduhk countlsuhk bitsuhk uhkbits for .accum, .short, false
stdfix rounduk countlsuk bitsuk ukbits for .accum, .default, false
stdfix roundulk countlsulk bitsulk ulkbits for .accum, .long, false


stdfix_abs abshr for .fract, .short
stdfix_abs absr for .fract, .default
stdfix_abs abslr for .fract, .long
stdfix_abs abshk for .accum, .short
stdfix_abs absk for .accum, .default
stdfix_abs abslk for .accum, .long


stdfix_mixed mulir divir rdivi idivr for .fract, .default, true
stdfix_mixed mulilr divilr lrdivi idivlr for .fract, .long, true
stdfix_mixed mulik divik kdivi idivk for .accum, .default, true
stdfix_mixed mulilk divilk lkdivi idivlk for .accum, .long, true
stdfix_mixed muliur diviur urdivi idivur for .fract, .default, false
stdfix_mixed muliulr diviulr ulrdivi idivulr for .fract, .long, false
stdfix_mixed muliuk diviuk ukdivi idivuk for .accum, .default, false
stdfix_mixed muliulk diviulk ulkdivi idivulk for .accum, .long, false


fixed_binary Binary.«+» := Arithmetic.add
fixed_binary Binary.«-» := Arithmetic.sub
fixed_binary Binary.«*» := Arithmetic.mul
fixed_binary Binary.«/» := Arithmetic.div


fixed_update Prefix.«++» Postfix.«++» := true
fixed_update Prefix.«--» Postfix.«--» := false


fixed_shift Binary.«<<» := true
fixed_shift Binary.«>>» := false
fixed_shift Assignment.«<<=» := true
fixed_shift Assignment.«>>=» := false


fixed_integer IntegerLeft.«+» IntegerRight.«+»
  Assignment.IntegerLeft.«+=» Assignment.IntegerRight.«+=» := Arithmetic.add
fixed_integer IntegerLeft.«-» IntegerRight.«-»
  Assignment.IntegerLeft.«-=» Assignment.IntegerRight.«-=» := Arithmetic.sub
fixed_integer IntegerLeft.«*» IntegerRight.«*»
  Assignment.IntegerLeft.«*=» Assignment.IntegerRight.«*=» := Arithmetic.mul
fixed_integer IntegerLeft.«/» IntegerRight.«/»
  Assignment.IntegerLeft.«/=» Assignment.IntegerRight.«/=» := Arithmetic.div

/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3: assignment converts the source value to the left
    operand's type.
The returned code is the value stored and produced by the assignment expression. -/
@[inline] def Assignment.«=» (destination : Format) (rounding : Rounding)
    (overflow : Overflow) (source : ℚ) : Option destination.Code :=
  convert destination rounding overflow source


fixed_assign Assignment.«+=» := Arithmetic.add
fixed_assign Assignment.«-=» := Arithmetic.sub
fixed_assign Assignment.«*=» := Arithmetic.mul
fixed_assign Assignment.«/=» := Arithmetic.div


fixed_compare Compare.«==» IntegerLeft.«==» IntegerRight.«==» := Eq
fixed_compare Compare.«!=» IntegerLeft.«!=» IntegerRight.«!=» := Ne
fixed_compare Compare.«<» IntegerLeft.«<» IntegerRight.«<» := LT.lt
fixed_compare Compare.«<=» IntegerLeft.«<=» IntegerRight.«<=» := LE.le
fixed_compare Compare.«>» IntegerLeft.«>» IntegerRight.«>» := GT.gt
fixed_compare Compare.«>=» IntegerLeft.«>=» IntegerRight.«>=» := GE.ge

reference_paths convert
reference_paths Unary.«+»
reference_paths Unary.«-»
reference_paths Unary.«!»
reference_paths Unary.update
reference_paths shift
reference_paths absfx
reference_paths roundfx
reference_paths countlsfx
reference_paths bitsfx
reference_paths fxbits
reference_paths toInteger
reference_paths Layout.evaluate
reference_paths Layout.preconvert
reference_paths Format.toBits
reference_paths Format.ofBits
reference_paths Assignment.«=»
reference_paths Arithmetic.applyWith
reference_paths ArithmeticChoice.apply
reference_paths Arithmetic.assignInteger
reference_paths Format.minimum
reference_paths Format.maximum
reference_paths Format.epsilon
reference_paths Format.bitsInteger
reference_paths Text.convert
reference_paths Text.scan
reference_paths Constant.parse
reference_paths Constant.rounded
reference_paths Constant.translate

end FloatLib.Floats.Formats.FixedPoint.Embedded
