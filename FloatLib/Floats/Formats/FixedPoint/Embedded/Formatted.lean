/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Layout
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Text
public import FloatLib.Numerics.Exact.DecimalText.Notation

/-!
# N1169 fixed-point formatted conversions

N1169, ISO/IEC TR 18037:2006(E), C 7.19.6.1–2, with inherited N1256
C99 clauses of the same numbers. These are single, resolved C-locale
conversion kernels. They model decimal precision, sign and padding flags,
field width, maximal numeric input items and explicit conversion outcomes.
Whole format strings, streams, pointer writes and assignment suppression
are outside this value model.

The scanner distinguishes an incomplete input item from `strtofx`'s shorter
complete subject. It recognizes complete subjects or subjects completed by
one zero digit. `FormattedProof` proves that these are exactly the prefixes
with a numeric completion, and that selection consumes a maximal such prefix.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded.Formatted

open FloatLib.Numerics

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.1–2: the four fixed-point conversion
    specifiers. -/
inductive Specifier where
  /-- `%r`: a signed fract value. -/
  | r
  /-- `%R`: an unsigned fract value. -/
  | R
  /-- `%k`: a signed accum value. -/
  | k
  /-- `%K`: an unsigned accum value. -/
  | K
  deriving DecidableEq, Repr

/-- Reconstruct a `Specifier` constructor from its constructor index. -/
add_decl_doc Specifier.ofNat_ctorIdx

/-- The specifier and length modifier select one of the twelve primary fixed types. -/
def Specifier.type (specifier : Specifier) (length : Length) : CType :=
  match specifier with
  | .r => ⟨.fract, length, true, false⟩
  | .R => ⟨.fract, length, false, false⟩
  | .k => ⟨.accum, length, true, false⟩
  | .K => ⟨.accum, length, false, false⟩

/-- Resolved flags, dynamic width and dynamic precision of one fixed output conversion. -/
structure PrintOptions where
  /-- C 7.19.6.1: minimum field width; a negative width also requests left alignment. -/
  width : Int := 0
  /-- C 7.19.6.1: fractional digit count; absent or negative precision selects six digits. -/
  precision : Option Int := none
  /-- C 7.19.6.1: the `-` flag pads on the right and overrides zero padding. -/
  left : Bool := false
  /-- C 7.19.6.1: the `+` flag prefixes nonnegative signed results with a plus sign. -/
  plus : Bool := false
  /-- C 7.19.6.1: the space flag prefixes nonnegative signed results unless `+` applies. -/
  space : Bool := false
  /-- C 7.19.6.1: the `#` flag retains a decimal point even at zero precision. -/
  alternate : Bool := false
  /-- C 7.19.6.1: the `0` flag inserts zero padding after the sign when right aligned. -/
  zero : Bool := false
  deriving Repr

/-- Missing or negative precision means six fractional digits, as in C 7.19.6.1. -/
def PrintOptions.places (options : PrintOptions) : Nat :=
  match options.precision with
  | none => 6
  | some precision => if precision < 0 then 6 else precision.toNat

/-- Round once on the selected decimal grid; preserve a negative source's rounded zero sign. -/
def decimal (rounding : Rounding) (value : ℚ) (places : Nat) : DecimalText.Decimal :=
  DecimalText.Decimal.ofScaledInt (rounding.run (value * (10 : ℚ) ^ places))
    (-(places : Int)) (value < 0)

/-- Sign, point and width presentation, reusing the shared exact fixed-decimal formatter. -/
def fieldCharacters (signed : Bool) (options : PrintOptions)
    (value : DecimalText.Decimal) : List Char :=
  let sign := if value.negative then ['-']
    else if signed && options.plus then ['+']
    else if signed && options.space then [' '] else []
  let digits := { value with negative := false }.fixedCharacters ++
    if options.alternate && options.places == 0 then ['.'] else []
  let padding := options.width.natAbs - (sign.length + digits.length)
  if options.left || options.width < 0 then
    sign ++ digits ++ List.replicate padding ' '
  else if options.zero then sign ++ List.replicate padding '0' ++ digits
  else List.replicate padding ' ' ++ sign ++ digits

/-- C-locale decimal output for any fixed grid, after precision and flag resolution. -/
def formatValue {format : Format} (rounding : Rounding) (options : PrintOptions)
    (value : format.Code) : String :=
  String.ofList (fieldCharacters format.signed options
    (decimal rounding (Format.decode value) options.places))

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.1: the fixed-point portion of `fprintf`,
    for any layout and rank. -/
def fprintf (layout : Layout) (specifier : Specifier) (length : Length)
    (rounding : Rounding) (options : PrintOptions)
    (value : (layout.format (specifier.type length)).Code) : String :=
  formatValue rounding options value

/-- Numeric input-item recognition: complete subjects or subjects completed by one zero. -/
def item (characters : List Char) : Option Unit :=
  if (Text.subject characters).isSome || (Text.subject (characters ++ ['0'])).isSome then
    some () else none

/-- Input after leading whitespace, restricted by the optional positive field width. -/
def input (width : Option ℕ+) (text : String) : List Char :=
  let rest := Text.subjectInput text
  match width with
  | none => rest
  | some width => rest.take width

/-- Observable outcomes of a single fixed-point input conversion. -/
inductive ScanStatus where
  /-- An item was read and its rounded value is a code of the format. -/
  | success
  /-- The input does not continue with a complete fixed-point item. -/
  | matchingFailure
  /-- The input ended before the first character of an item. -/
  | inputFailure
  /-- An item was read whose rounded value the format does not hold: C leaves the behavior
  undefined. -/
  | undefined
  deriving DecidableEq, Repr

/-- Reconstruct a `ScanStatus` constructor from its constructor index. -/
add_decl_doc ScanStatus.ofNat_ctorIdx

/-- Consumed position and optional numeric result; no C memory is mutated. -/
structure ScanResult (format : Format) where
  /-- C 7.19.6.2: consumed character count, including leading whitespace and the input item. -/
  consumed : Nat
  /-- C 7.19.6.2: success, input or matching failure, or an unrepresentable numeric result. -/
  status : ScanStatus
  /-- C 7.19.6.2: the rounded representable code on success; absent for every failure. -/
  value : Option format.Code

/-- C 7.19.6.2: the result must fit after rounding; stream conversion does not saturate. -/
def scanValue (format : Format) (rounding : Rounding) (value : ℚ) : Option format.Code :=
  fxbits format (rounding.run (value / format.quantizer.scale))

/-- N1169 input conversion, consuming an incomplete item before reporting matching failure.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.2, amendments to C clause 7.19.6.2.
-/
def scan (format : Format) (rounding : Rounding) (width : Option ℕ+) (text : String) :
    ScanResult format :=
  let rest := Text.subjectInput text
  let characters := input width text
  let length := RadixText.prefixLength item characters
  let consumed := text.toList.length - rest.length + length
  if length = 0 then
    ⟨consumed, if rest = [] then .inputFailure else .matchingFailure, none⟩
  else match Text.subject (characters.take length) with
    | none => ⟨consumed, .matchingFailure, none⟩
    | some exact =>
        match scanValue format rounding exact with
        | none => ⟨consumed, .undefined, none⟩
        | some result => ⟨consumed, .success, some result⟩

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.19.6.2: the fixed-point portion of `fscanf`,
    for any layout and rank. -/
def fscanf (layout : Layout) (specifier : Specifier) (length : Length)
    (rounding : Rounding) (width : Option ℕ+) (text : String) :
    ScanResult (layout.format (specifier.type length)) :=
  scan (layout.format (specifier.type length)) rounding width text

end FloatLib.Floats.Formats.FixedPoint.Embedded.Formatted
