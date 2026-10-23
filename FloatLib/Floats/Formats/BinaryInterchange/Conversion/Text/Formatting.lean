/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.DecimalFormatting
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Shortest
public import FloatLib.Numerics.Exact.DecimalText.Special

/-!
# Binary external character output

`format value` writes a decimal that reads back as `value`, normally the shortest one or the exact
value when that is short, and `toString`, `repr` and `#eval` show the same text. The `style` option
selects every other output: exact decimal and hexadecimal digits, a count of significant digits, and
fixed or scientific notation with a count of places. Styles that round do so once, in the `mode`
option, and `(status := true)` returns the text with the inexact indicator of that rounding.
Exponents are unbounded, so output cannot overflow or underflow.

The display writes `inf`, `-inf` and `nan`. The other styles keep the complete spellings of
infinities and NaNs, including the sign, signaling state and payload of a NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- How `format` writes a binary value. -/
inductive TextStyle where
  /-- The shortest decimal that reads back as the value, or a short exact value: the display. -/
  | shortest
  /-- Every digit of the exact decimal value, as a significand and a decimal exponent. -/
  | exact
  /-- This many significant decimal digits, as a significand and a decimal exponent. -/
  | significant (digits : ℕ+)
  /-- Ordinary decimal notation with exactly this many digits after the point. -/
  | fixed (places : Nat)
  /-- One digit before the point, this many after it, and an `e` exponent. -/
  | scientific (places : Nat)
  /-- A hexadecimal significand with a `p` binary exponent, exact or to significant digits. -/
  | hex (precision : Numerics.DecimalText.Precision := .exact)

namespace Internal.Status

/-- Text of the finite value `value`, with exact value `exact`, in `style`, and its status. -/
@[inline] def formatFinite {fmt : FloatFormat} (style : TextStyle) (mode : IEEERoundingMode)
    (value : Model fmt) (exact : Numerics.Dyadic) : TextOutcome :=
  match style with
  | .shortest =>
      let record := Shortest.decimal mode value exact
      { text := String.ofList (Shortest.characters (Shortest.digits fmt) record)
        status := { inexact := decide (record.toRat ≠ exact.toRat) } }
  | .exact => formatDyadicText mode .decimal .exact exact
  | .significant digits => formatDyadicText mode .decimal (.significant digits) exact
  | .fixed places => fixedText mode places exact
  | .scientific places => scientificText mode places exact
  | .hex precision => formatDyadicText mode .hexadecimal precision exact

/-- Text of `value` in `style` with the inexact indicator of its rounding in `mode`. -/
@[inline] def format {fmt : FloatFormat} (value : Model fmt) (style : TextStyle)
    (mode : IEEERoundingMode) : TextOutcome :=
  match exactValue value with
  | .finite exact => formatFinite style mode value exact
  | .infinity negative =>
      match style with
      | .shortest => { text := if negative then "-inf" else "inf" }
      | _ => { text := String.ofList (Numerics.SpecialText.infinityCharacters negative) }
  | .nan negative signaling payload =>
      match style with
      | .shortest => { text := "nan" }
      | _ =>
          { text := String.ofList (Numerics.SpecialText.nanCharacters negative signaling payload) }

end Internal.Status

/--
Write a value of any binary descriptor as text.

By default this is the display: the exact value when it has at most `d` significant digits (`d` is
17 for binary64), and otherwise the shortest decimal the search finds that `parse` reads back as
`value`, with the exact value as the fallback. It uses fixed notation from `0.0001` up to `10^d` and
an `e` exponent otherwise. `toString`, `repr` and `#eval` use it. `style` selects the exact decimal
or hexadecimal digits, significant digits, or fixed or scientific notation. Styles that round do so
once in `mode`, and with `mode` the display reads back in that mode. With `status := true` the
result also carries the inexact indicator of that rounding.
-/
@[inline] def format {fmt : FloatFormat} (value : Model fmt) (style : TextStyle := .shortest)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => TextOutcome
    | false => String :=
  match status with
  | true => Internal.Status.format value style mode
  | false => (Internal.Status.format value style mode).text

/-- Values print as a decimal that reads back as the same value, normally the shortest. -/
instance {fmt : FloatFormat} : ToString (Model fmt) where
  toString value := format value

/-- `#eval` and `repr` show the same decimal, parenthesized when negative inside an argument. -/
instance {fmt : FloatFormat} : Repr (Model fmt) where
  reprPrec value precedence :=
    let text := format value
    if text.startsWith "-" then Repr.addAppParen text precedence else text

/-- `#eval` shows the three fields, displaying the value as `toString` does. -/
instance {fmt : FloatFormat} : Repr (IEEEOutcome fmt) where
  reprPrec outcome _ :=
    Std.Format.bracket "{ "
      (Std.Format.joinSep
        [f!"value := {repr outcome.value}", f!"status := {repr outcome.status}",
          f!"ternary := {repr outcome.ternary}"]
        ("," ++ Std.Format.line))
      " }"

end FloatLib.Floats.Formats.BinaryInterchange.Model
