/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Parsing
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Numerics.Exact.DecimalText.Notation
public import Mathlib.Data.Nat.Log

/-!
# Shortest decimal text of binary values

The display of a finite binary value is normally the shortest decimal that reads back as the same
value.
A value whose exact decimal has at most `d` significant digits, where `d` digits always identify
a value of the format (17 for binary64, 9 for binary32, 5 for binary16, 4 for bfloat16), prints
exactly instead, so `65504` stays `65504` in binary16 and `3.75` stays `3.75` in an 8-bit format.

The digits come from exact integer arithmetic on the interval of decimals that round to the value.
The coarsest decimal grid `10^q` meeting that interval is found by starting from its width and
climbing, and the grid point nearest to the value is chosen, ties to even. The candidate is then
converted by the parser's own decimal conversion. It is printed only if that conversion returns the
value, and otherwise the exact decimal expansion is printed, so reading the text back returns the
value by construction (`Model.parse_format_of_isFinite`).

Fixed notation is used from `0.0001` up to `10^d`, and smaller and larger values use one leading
digit and an `e` exponent.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model
namespace Shortest

open FloatLib.Numerics

/--
Magnitudes from `low * 2^scale` to `high * 2^scale` that read back as one finite nonzero value,
each end included when its flag is set.
-/
structure Range where
  /-- Least magnitude, as a multiple of `2^scale`. -/
  low : Nat
  /-- Greatest magnitude, as a multiple of `2^scale`. -/
  high : Nat
  /-- Whether `low` itself reads back as the value. -/
  lowIncluded : Bool
  /-- Whether `high` itself reads back as the value. -/
  highIncluded : Bool
  /-- Binary exponent of the unit. -/
  scale : Int

/--
The range of magnitudes that round in `mode` to the value `significand * 2^exponent`.

Neighbors lie one unit `2^exponent` away, except below the first value of a binade, where the
step is half as large (`binadeBottom`). Nearest-even includes both midpoints exactly when the
significand is even, and the directed modes take the half-open gap on the side they round from.
-/
def range (mode : IEEERoundingMode) (negative : Bool) (significand : Nat) (exponent : Int)
    (binadeBottom : Bool) : Range :=
  let center := 4 * significand
  let below := if binadeBottom then 2 else 4
  let truncating : Range := ⟨center, center + 4, true, false, exponent - 2⟩
  let ceiling : Range := ⟨center - below, center, false, true, exponent - 2⟩
  match mode with
  | .nearest =>
      let even := significand % 2 == 0
      ⟨center - below / 2, center + 2, even, even, exponent - 2⟩
  | .nearestAway => ⟨center - below / 2, center + 2, true, false, exponent - 2⟩
  | .towardZero => truncating
  | .away => ceiling
  | .up => if negative then truncating else ceiling
  | .down => if negative then ceiling else truncating

/-- `10^q / 2^scale` as a numerator and a denominator. -/
@[inline] def step (scale q : Int) : Nat × Nat :=
  let twos := q - scale
  (2 ^ twos.toNat * 5 ^ q.toNat, 2 ^ (-twos).toNat * 5 ^ (-q).toNat)

/-- The least multiple of a grid in the interval, from the floor and ceiling of its low end. -/
@[inline] def first (range : Range) (lowFloor lowCeil : Nat) : Nat :=
  if range.lowIncluded then lowCeil else lowFloor + 1

/-- The greatest multiple of a grid in the interval, from the floor and ceiling of its high end. -/
@[inline] def last (range : Range) (highFloor highCeil : Nat) : Nat :=
  if range.highIncluded then highFloor else highCeil - 1

/-- Floor and ceiling of `value * den / num`. -/
@[inline] def bounds (value num den : Nat) : Nat × Nat :=
  let scaled := value * den
  let quotient := scaled / num
  (quotient, if scaled % num = 0 then quotient else quotient + 1)

/--
From the grid `10^q = (num / den) * 2^scale`, lower `q` until the interval contains a multiple.
Returns the grid with the floors and ceilings of both interval ends in its units.
-/
def descend (range : Range) :
    Nat → Int → Nat → Nat → Option (Int × Nat × Nat × Nat × Nat × Nat × Nat)
  | 0, _, _, _ => none
  | fuel + 1, q, num, den =>
      let (lowFloor, lowCeil) := bounds range.low num den
      let (highFloor, highCeil) := bounds range.high num den
      if first range lowFloor lowCeil ≤ last range highFloor highCeil then
        some (q, num, den, lowFloor, lowCeil, highFloor, highCeil)
      else
        descend range fuel (q - 1) num (10 * den)

/--
Coarsen a grid that meets the interval tenfold while the coarser grid still meets it, counting
the steps. Floors and ceilings of the interval ends on the coarser grid are those of the finer
grid divided by ten, so this needs no further exact arithmetic on the ends. Grids that meet the
interval are closed under refinement, so the first miss leaves the coarsest one.
-/
def climb (range : Range) : Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, steps, lowFloor, lowCeil, highFloor, highCeil =>
      (steps, first range lowFloor lowCeil, last range highFloor highCeil)
  | fuel + 1, steps, lowFloor, lowCeil, highFloor, highCeil =>
      let lowFloor' := lowFloor / 10
      let lowCeil' := (lowCeil + 9) / 10
      let highFloor' := highFloor / 10
      let highCeil' := (highCeil + 9) / 10
      if first range lowFloor' lowCeil' ≤ last range highFloor' highCeil' then
        climb range fuel (steps + 1) lowFloor' lowCeil' highFloor' highCeil'
      else
        (steps, first range lowFloor lowCeil, last range highFloor highCeil)

/--
The multiple of the coarsest decimal grid in the interval that is nearest to `target * 2^scale`,
ties to the even multiple, with the given sign.

The initial grid comes from the interval width and `1233 / 4096 < log₁₀ 2`. Descent allows for
the estimate's error, then climbing finds the coarsest grid that meets the interval. Both loop
bounds come from the exact integers' bit lengths, without a fixed precision or exponent limit.
-/
def search (range : Range) (target : Nat) (negative : Bool) : Option DecimalText.Decimal :=
  let q := (((range.high - range.low).log2 : Int) + range.scale) * 1233 / 4096
  let (num, den) := step range.scale q
  match descend range (num.log2 + 2) q num den with
  | none => none
  | some (q, num, den, lowFloor, lowCeil, highFloor, highCeil) =>
      let (steps, first, last) :=
        climb range (highCeil.log2 + 2) 0 lowFloor lowCeil highFloor highCeil
      let scaled := target * den
      let quotient := scaled / num
      let remainder := scaled % num
      let power := 10 ^ steps
      let n := quotient / power
      let rest := quotient % power
      let up :=
        if steps = 0 then 2 * remainder > num ∨ (2 * remainder = num ∧ n % 2 = 1)
        else 2 * rest > power ∨ (2 * rest = power ∧ (remainder ≠ 0 ∨ n % 2 = 1))
      let nearest := if up then n + 1 else n
      some { negative, significand := max first (min last nearest), exponent := q + steps }

/--
The number of significant decimal digits that always identify a value of the format, one more
than the digits of `2^precision`: 17 for binary64, 9 for binary32, 5 for binary16, 4 for
bfloat16 and 3 for an 8-bit format with four significant bits.
-/
def digits (fmt : FloatFormat) : Nat :=
  Nat.log 10 (2 ^ (fmt.fracWidth + 1)) + 2

/--
The shortest candidate of `search` for the finite nonzero value `value` with exact value
`exact`, kept only if the parser's value conversion in `mode` returns `value`. The exact decimal
value replaces a candidate that does not.
-/
def verified {fmt : FloatFormat} (mode : IEEERoundingMode) (value : Model fmt)
    (exact : Numerics.Dyadic) : DecimalText.Decimal :=
  let readBack := range mode exact.negative exact.significand exact.exponent
    (fracField value == 0 && 1 < expField value)
  match search readBack (4 * exact.significand) exact.negative with
  | some candidate =>
      match Internal.Value.convertText fmt mode (.decimal candidate) with
      | .ok restored =>
          if restored = value then candidate else (DecimalText.ofDyadic exact).compact
      | .error _ => (DecimalText.ofDyadic exact).compact
  | none => (DecimalText.ofDyadic exact).compact

/--
The decimal record displayed for the finite value `value` with exact value `exact`: zero with its
sign, the exact value when it has at most `digits fmt` significant digits, and otherwise the
`verified` shortest decimal.

An exact value with that few digits has a binary exponent within the bounds tested first, so
values far outside them go straight to the search without expanding their exact decimal.
-/
def decimal {fmt : FloatFormat} (mode : IEEERoundingMode) (value : Model fmt)
    (exact : Numerics.Dyadic) : DecimalText.Decimal :=
  if exact.significand = 0 then
    { negative := exact.negative, significand := 0, exponent := 0 }
  else
    let precision := fmt.fracWidth + 1
    let count := digits fmt
    if -((precision + 2 * count : Nat) : Int) ≤ exact.exponent ∧
        exact.exponent ≤ ((2 * precision + 4 * count : Nat) : Int) then
      let exactRecord := (DecimalText.ofDyadic exact).compact
      if exactRecord.significand < 10 ^ count then exactRecord else verified mode value exact
    else
      verified mode value exact

/--
Characters of a displayed decimal record: fixed notation when the leading digit lies between four
places after the point and `count` places before it, otherwise one leading digit and an `e`
exponent. Both read back as the value and sign of the record.
-/
def characters (count : Nat) (record : DecimalText.Decimal) : List Char :=
  let leading := (Nat.log 10 record.significand : Int) + record.exponent
  if -4 ≤ leading ∧ leading < count then record.fixedCharacters
  else record.scientificCharacters

end Shortest
end FloatLib.Floats.Formats.BinaryInterchange.Model
