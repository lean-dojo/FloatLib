/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.KernelPath
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Coefficient
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Limits
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Text
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Constant
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Formatted
public import FloatLib.Tactic.ReferencePaths
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# EmbeddedStandard generators

The commands expand into declarations checked in the importing module. The declarations carry the
identifiers of the C draft, such as `SFRACT_FBIT`, so their names keep its underscores and are
marked `nolint defsWithUnderscore`.
-/

public meta section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

open FloatLib.Numerics FloatLib.Floats.ExecFloat

set_option hygiene false in
/-- Expand `stdfix_limits` into its checked family declarations. -/
macro (name := stdfixLimits) "stdfix_limits " stem:ident integerName:ident
    " for " kind:term "," length:term "," signed:term : command => do
  let fbit := Lean.mkIdent (stem.getId.appendAfter "_FBIT")
  let maximum := Lean.mkIdent (stem.getId.appendAfter "_MAX")
  let epsilon := Lean.mkIdent (stem.getId.appendAfter "_EPSILON")
  `(/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the implementation's fractional
    value-bit count. -/
    @[inline, nolint defsWithUnderscore] def $fbit (layout : Layout) : Nat :=
      (layout.format ⟨$kind, $length, $signed, false⟩).fractionalBits
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the greatest stored value of the
      named type. -/
    @[inline, nolint defsWithUnderscore] def $maximum (layout : Layout) :
        (layout.format ⟨$kind, $length, $signed, false⟩).Code :=
      (layout.format ⟨$kind, $length, $signed, false⟩).maximum
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the least positive stored value of
      the named type. -/
    @[inline, nolint defsWithUnderscore] def $epsilon (layout : Layout) (valid : layout.Valid) :
        (layout.format ⟨$kind, $length, $signed, false⟩).Code :=
      (layout.format ⟨$kind, $length, $signed, false⟩).epsilon
        (layout.precision_pos valid _)
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.2: an associated integer format
      containing every coefficient.
    The extra width parameter represents implementation-selected excess capacity. -/
    @[inline, nolint defsWithUnderscore] def $integerName
        (layout : Layout) (extra : Nat := 0) : IntegerFormat :=
      (layout.format ⟨$kind, $length, $signed, false⟩).bitsInteger extra
    reference_paths $fbit
    reference_paths $maximum
    reference_paths $epsilon
    reference_paths $integerName)


set_option hygiene false in
/-- Expand `stdfix_min` into its checked family declarations. -/
macro (name := stdfixMin) "stdfix_min " name:ident " for " kind:term "," length:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the least stored value of the named
    signed type. -/
    @[inline, nolint defsWithUnderscore] def $name (layout : Layout) :
        (layout.format ⟨$kind, $length, true, false⟩).Code :=
      (layout.format ⟨$kind, $length, true, false⟩).minimum
    reference_paths $name)


set_option hygiene false in
/-- Expand `stdfix_ibit` into its checked family declarations. -/
macro (name := stdfixIbit) "stdfix_ibit " name:ident " for " length:term "," signed:term :
    command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: the implementation's integral
    value-bit count. -/
    @[inline, nolint defsWithUnderscore] def $name (layout : Layout) : Nat :=
      (layout.format ⟨.accum, $length, $signed, false⟩).integralBits
    reference_paths $name)


set_option hygiene false in
/-- Expand `stdfix_text` into its checked family declarations. -/
macro (name := stdfixText) "stdfix_text " name:ident " for " kind:term "," length:term ","
    signed:term :
    command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.8: longest C-locale subject, rounded
    and saturated.
    The result records the end offset and range error without C memory mutation. -/
    @[inline] def $name (layout : Layout) (rounding : Rounding) (text : String) :
        Text.Result (layout.format ⟨$kind, $length, $signed, false⟩) :=
      Text.convert (layout.format ⟨$kind, $length, $signed, false⟩) rounding text
    reference_paths $name)


set_option hygiene false in
/-- Expand `stdfix` into its checked family declarations. -/
macro (name := stdfix) "stdfix " roundName:ident countName:ident bitsName:ident fromName:ident
    " for " kind:term "," length:term "," signed:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.3: nearest coarse-grid rounding with
    saturation, at the layout's
    precision. -/
    @[inline] def $roundName (layout : Layout) (rounding : NearestRounding)
        (value : (layout.format ⟨$kind, $length, $signed, false⟩).Code) (count : Int) :
        Option (layout.format ⟨$kind, $length, $signed, false⟩).Code :=
      roundfx rounding value count
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.4: greatest nonoverflowing shift,
      with the recommended zero convention. -/
    @[inline] def $countName (layout : Layout)
        (value : (layout.format ⟨$kind, $length, $signed, false⟩).Code) : Nat :=
      countlsfx value
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.5: exact integer coefficient of the
      named fixed-point type. -/
    @[inline] def $bitsName (layout : Layout)
        (value : (layout.format ⟨$kind, $length, $signed, false⟩).Code) : Int :=
      bitsfx value
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.6: exact coefficient conversion;
      out-of-range inputs have no exact code. -/
    @[inline] def $fromName (layout : Layout) (coefficient : Int) :
        Option (layout.format ⟨$kind, $length, $signed, false⟩).Code :=
      fxbits (layout.format ⟨$kind, $length, $signed, false⟩) coefficient
    reference_paths $roundName
    reference_paths $countName
    reference_paths $bitsName
    reference_paths $fromName)


set_option hygiene false in
/-- Expand `stdfix_abs` into its checked family declarations. -/
macro (name := stdfixAbs) "stdfix_abs " name:ident " for " kind:term "," length:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.2: signed absolute value, saturated
    at the positive endpoint. -/
    @[inline] def $name (layout : Layout)
        (value : (layout.format ⟨$kind, $length, true, false⟩).Code) :
        (layout.format ⟨$kind, $length, true, false⟩).Code :=
      absfx value
    reference_paths $name)


set_option hygiene false in
/-- Expand `stdfix_mixed` into its checked family declarations. -/
macro (name := stdfixMixed) "stdfix_mixed " mulName:ident divName:ident quotientName:ident
    intName:ident
    " for " kind:term "," length:term "," signed:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.1: integer times fixed, exactly
    computed then truncated toward zero. -/
    @[inline] def $mulName (layout : Layout) (integerFormat : IntegerFormat)
        (integer : Int) (value : (layout.format ⟨$kind, $length, $signed, false⟩).Code) :
        Option Int :=
      muli integerFormat integer value
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.1: integer divided by fixed; zero
      divisor is undefined. -/
    @[inline] def $divName (layout : Layout) (integerFormat : IntegerFormat)
        (integer : Int) (value : (layout.format ⟨$kind, $length, $signed, false⟩).Code) :
        Option Int :=
      divi integerFormat integer value
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.1: integer quotient returning fixed
      point, with saturated overflow. -/
    @[inline] def $quotientName (layout : Layout) (rounding : Rounding)
        (numerator denominator : Int) :
        Option (layout.format ⟨$kind, $length, $signed, false⟩).Code :=
      fxdivi (layout.format ⟨$kind, $length, $signed, false⟩) rounding numerator denominator
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.6.1: fixed quotient returning an
      integer, truncated toward zero. -/
    @[inline] def $intName (layout : Layout) (integerFormat : IntegerFormat)
        (x y : (layout.format ⟨$kind, $length, $signed, false⟩).Code) : Option Int :=
      idiv integerFormat x y
    reference_paths $mulName
    reference_paths $divName
    reference_paths $quotientName
    reference_paths $intName)


set_option hygiene false in
/-- Expand `fixed_binary` into its checked family declarations. -/
macro (name := fixedBinary) "fixed_binary " name:ident " := " operation:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.1 and C 6.3.1.8: arithmetic with usual
    fixed-point type conversions. -/
    @[inline] def $name (layout : Layout) (environment : Environment) (left right : CType)
        (x : (layout.format left).Code) (y : (layout.format right).Code) :
        Option (layout.format (left.common right)).Code :=
      layout.evaluate environment $operation left right x y
    reference_paths $name)


set_option hygiene false in
/-- Expand `fixed_update` into its checked family declarations. -/
macro (name := fixedUpdate) "fixed_update " prefixName:ident postfixName:ident " := "
    increment:term :
    command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.1: prefix update returns the new value to be
    stored in the lvalue. -/
    @[inline] def $prefixName {format : Format} (rounding : Rounding) (overflow : Overflow)
        (value : format.Code) : Option format.Code :=
      Unary.update $increment rounding overflow value
    /-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.1.1: postfix update returns the old value and
      the new stored value.
    The pair models the expression result and lvalue update without performing C object mutation. -/
    @[inline] def $postfixName {format : Format} (rounding : Rounding) (overflow : Overflow)
        (value : format.Code) : Option (format.Code × format.Code) :=
      (Unary.update $increment rounding overflow value).map (fun result ↦ (value, result))
    reference_paths $prefixName
    reference_paths $postfixName)


set_option hygiene false in
/-- Expand `fixed_shift` into its checked family declarations. -/
macro (name := fixedShift) "fixed_shift " name:ident " := " left:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.2: exact power-of-two scaling with the C
    shift-count constraint. -/
    @[inline] def $name {format : Format} (rounding : Rounding) (overflow : Overflow)
        (value : format.Code) (count : Int) : Option format.Code :=
      shift $left rounding overflow value count
    reference_paths $name)


set_option hygiene false in
/-- Expand `fixed_integer` into its checked family declarations. -/
macro (name := fixedInteger) "fixed_integer " leftName:ident rightName:ident
    leftAssign:ident rightAssign:ident " := " operation:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.8: integer/fixed arithmetic retains
    both operand values.
    The result has the fixed operand's type; the integer is not converted beforehand. -/
    @[inline] def $leftName {format : Format} (rounding : Rounding) (overflow : Overflow)
        (integer : Int) (value : format.Code)
        (policy : ArithmeticPolicy := .exact .OFF) : Option format.Code :=
      Arithmetic.applyWith $operation policy format rounding overflow integer (Format.decode value)
    /-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.8: fixed/integer arithmetic, with
      implementation-selected result precision. -/
    @[inline] def $rightName {format : Format} (rounding : Rounding) (overflow : Overflow)
        (value : format.Code) (integer : Int)
        (policy : ArithmeticPolicy := .exact .OFF) : Option format.Code :=
      Arithmetic.applyWith $operation policy format rounding overflow (Format.decode value) integer
    /-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3: compound assignment to an integer lvalue
      through a fixed intermediate. -/
    @[inline] def $leftAssign (integerFormat : IntegerFormat) {format : Format}
        (rounding : Rounding) (overflow : Overflow) (integer : Int) (value : format.Code)
        (policy : ArithmeticPolicy := .exact .OFF) : Option Int :=
      Arithmetic.assignInteger $operation policy integerFormat rounding overflow integer value
    /-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3: compound assignment to a fixed lvalue with
      an integer right operand. -/
    @[inline] def $rightAssign {format : Format} (rounding : Rounding) (overflow : Overflow)
        (value : format.Code) (integer : Int)
        (policy : ArithmeticPolicy := .exact .OFF) : Option format.Code :=
      Arithmetic.applyWith $operation policy format rounding overflow (Format.decode value) integer
    reference_paths $leftName
    reference_paths $rightName
    reference_paths $leftAssign
    reference_paths $rightAssign)


set_option hygiene false in
/-- Expand `fixed_assign` into its checked family declarations. -/
macro (name := fixedAssign) "fixed_assign " name:ident " := " operation:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.3: compound assignment computes the common-type
    operation,
    then converts its result back to the left operand's type, as C requires. -/
    @[inline] def $name (layout : Layout) (environment : Environment) (left right : CType)
        (x : (layout.format left).Code) (y : (layout.format right).Code) :
        Option (layout.format left).Code :=
      (layout.evaluate environment $operation left right x y).bind fun result ↦
        convert (layout.format left) (environment.rounding left) (environment.overflow left)
          (Format.decode result)
    reference_paths $name)


set_option hygiene false in
/-- Expand `fixed_compare` into its checked family declarations. -/
macro (name := fixedCompare) "fixed_compare " name:ident leftName:ident rightName:ident
    " := " relation:term : command =>
  `(/-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.3: compare the exact operand values without
    common-type conversion. -/
    @[inline] def $name {left right : Format} (x : left.Code) (y : right.Code) : Bool :=
      decide ($relation (Format.decode x) (Format.decode y))
    /-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.3: integer/fixed comparison retains both
      exact values. -/
    @[inline] def $leftName {format : Format} (integer : Int) (value : format.Code) : Bool :=
      decide ($relation (integer : ℚ) (Format.decode value))
    /-- WG14 N1169 (2006 TR 18037 draft), §4.1.6.2.3: fixed/integer comparison retains both
      exact values. -/
    @[inline] def $rightName {format : Format} (value : format.Code) (integer : Int) : Bool :=
      decide ($relation (Format.decode value) (integer : ℚ))
    reference_paths $name
    reference_paths $leftName
    reference_paths $rightName)


end FloatLib.Floats.Formats.FixedPoint.Embedded
