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

`format value` writes a decimal that reads back as `value`. Normally that is the shortest such
decimal, or the exact value when the exact value is short, and `toString`, `repr` and `#eval` show
the same text. Its `style` option selects every other output: exact decimal and hexadecimal
digits, a count of significant digits, and fixed or scientific notation with a count of places.
Styles that round do so once, in the `mode` option, and `(status := true)` returns the text with
the inexact indicator of that rounding. Exponents are unbounded, so output cannot overflow or
underflow.

In the display, infinities and NaNs are `inf`, `-inf` and `nan`. Other styles keep the complete
spellings of infinities and NaNs, including the sign, signaling state and payload of a NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/--
How `format` writes a binary value. For the binary32 value nearest `0.1`, rounding to nearest-even:

| Style | Text | What `mode` does |
| --- | --- | --- |
| `.shortest` | `"0.1"` | the direction the text is read back in |
| `.exact` | `"100000001490116119384765625e-27"` | nothing: every digit |
| `.significant (digits := 4)` | `"1000e-4"` | rounds the digits |
| `.fixed (places := 3)` | `"0.100"` | rounds the digits |
| `.scientific (places := 3)` | `"1.000e-1"` | rounds the digits |
| `.hex` | `"0xcccccdp-27"` | nothing: the exact integral significand and exponent |
| `.hex (.significant (digits := 3))` | `"0x19ap-12"` | rounds the hexadecimal digits |

`.fixed` and `.scientific` count places after the point, as C's `%.3f` and `%.3e` do, so
`.scientific (places := 3)` keeps four significant digits. With `(mode := .up)` the three decimal
styles that round give `"1001e-4"`, `"0.101"` and `"1.001e-1"`. With `(mode := .down)` the
hexadecimal one gives `"0x199p-12"`, and the display is `"0.100000002"`, a shortest decimal that
rounds down to this value.
-/
inductive TextStyle where
  /-- The shortest decimal that reads back as the value, or a short exact value: the display. -/
  | shortest
  /-- Every digit of the exact decimal value, as a significand and a decimal exponent. -/
  | exact
  /-- This many significant decimal digits, as a significand and a decimal exponent. -/
  | significant (digits : ℕ+)
  /-- Ordinary decimal notation with this many digits after the point. -/
  | fixed (places : Nat)
  /-- One digit before the point, this many after it, and an `e` exponent. -/
  | scientific (places : Nat)
  /-- A hexadecimal significand with a `p` binary exponent, exact or to significant digits. -/
  | hex (precision : Numerics.DecimalText.Precision := .exact)
  deriving DecidableEq, Repr

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

By default this is the display, which `toString`, `repr` and `#eval` also use. It is the exact
value when that has at most `d` significant digits (`d` is 17 for binary64), and otherwise the
shortest decimal the search finds that `parse` reads back as `value`, with the exact value as the
fallback. Fixed notation covers `0.0001` up to `10^d`, and other values get an `e` exponent.
`style` selects the exact decimal or hexadecimal digits, significant digits, or fixed or
scientific notation, as the `TextStyle` table shows.

What `mode` does depends on the style. For the display it is the direction the text is read back
in, since the search keeps a candidate only if `parse` in `mode` returns `value`. The styles that
round, `.significant`, `.fixed`, `.scientific` and `.hex (.significant n)`, round the printed
digits once in `mode`. `.exact` and the exact `.hex` print every digit and ignore it. With
`status := true` the result also carries the inexact indicator, raised when the printed digits do
not denote the finite value. Infinities and NaNs never raise it, and the display writes every NaN
as `nan`.
-/
@[inline] def format {fmt : FloatFormat} (value : Model fmt) (style : TextStyle := .shortest)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => TextOutcome
    | false => String :=
  match status with
  | true => Internal.Status.format value style mode
  | false => (Internal.Status.format value style mode).text

/--
Finite values print as a decimal that reads back as the same value, normally the shortest.
Infinities print as `inf` and `-inf`, and every NaN prints as `nan`, without its sign, signaling
state or payload. Every other `TextStyle` of `format` keeps them.
-/
instance {fmt : FloatFormat} : ToString (Model fmt) where
  toString value := format value

/-- `#eval` and `repr` show the same text as `toString`, parenthesized when negative inside an
argument, so NaNs show as `nan` here too. -/
instance {fmt : FloatFormat} : Repr (Model fmt) where
  reprPrec value precedence :=
    let text := format value
    if text.startsWith "-" then Repr.addAppParen text precedence else text

/-- `#eval` shows the three fields, displaying the value as `toString` does and listing only the
raised flags, as `{ value := 0.3333333, status := { inexact := true }, ternary := Ordering.lt }`. -/
instance {fmt : FloatFormat} : Repr (IEEEOutcome fmt) where
  reprPrec outcome _ :=
    Numerics.reprRecord
      [("value", repr outcome.value), ("status", repr outcome.status),
        ("ternary", repr outcome.ternary)]

end FloatLib.Floats.Formats.BinaryInterchange.Model
