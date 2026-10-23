/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Basic
public import FloatLib.Numerics.Enclosure.Trigonometric.Runtime

/-!
# Cached constants: π/2, 2/π and log 2 at any precision

`piLevel bits` holds `π/2` and `2/π`, and `ln2Fixed bits` holds `log 2`, each as a natural number
`T` with `T ≤ c * 2 ^ bits < T + 2`. Binary splitting sums Machin's formula
`π/4 = 4 atan (1/5) - atan (1/239)` and the series of `log 2 = log (4/3) - log (2/3)` into
unreduced integer fractions, so each constant costs one integer division and no rational
normalization. The fractions are the lower and upper endpoints of `piQuarter (piDegree bits)` and
`logSeries 2 (ln2Degree bits)`, the rational enclosures of `Trigonometric.Runtime` and
`Elementary.Runtime`, and `Constants.Proof` proves the two-unit bounds at every precision.

Level `k` holds the constants at `64 * 2 ^ k` fractional bits. The first forty levels are cached.
Each is computed at most once per process, on first use, and then shared. Higher levels are
computed on each call. A read at `bits` shifts the first level with at least `bits` bits down to
`bits`, which keeps the two-unit bound. The faithful read of `log 2` takes 64 more bits and is
within one unit, and the grid read returns an enclosure on a binary grid.

The cache is read by the binary sine and cosine reduction, the exponential reduction, generated
transcendental configurations, the certified binary power and `Model.pi`. Two computations do not
read it. The rational enclosures behind the exact comparators compute their own `π/4` with
`piQuarter`, and `BinaryGrid.log`, behind the certified binary and decimal logarithms and the
logarithm comparator `ElementaryComparison.compareLog`, computes its own `log 2`.

Module initialization only allocates the cells. The cache definitions disable closed-term
extraction, and every read goes through `Internal.forceCache`, which is never inlined or extracted.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Read a cached value. The read is kept out of line and out of closed-term extraction, so it stays a
first-use computation whatever the caller's compiler settings.
-/
@[noinline, never_extract] def Internal.forceCache {α : Type} (cache : Thunk α) : α :=
  cache.get

end FloatLib.Numerics

namespace FloatLib.Numerics.Enclosure.Constants

open Taylor

/-! ## π/2 and 2/π -/

/--
The Machin series degree for `bits` fractional bits. Each term of `atan (1/5)` gains `log₂ 25`
bits, so a quarter of `bits` terms and four more leave a truncation error far below `2 ^ -bits`.
-/
def piDegree (bits : Nat) : Nat :=
  bits / 4 + 4

/-- Endpoints of a rational enclosure, as unreduced fractions over one positive denominator. -/
structure FractionBounds where
  /-- Numerator of the lower endpoint. -/
  lower : Int
  /-- Numerator of the upper endpoint. -/
  upper : Int
  /-- Common denominator of both endpoints. -/
  denominator : Nat
  /-- A positive denominator keeps both endpoints defined. -/
  denominator_pos : 0 < denominator
  deriving Repr

/--
The endpoints of `piQuarter degree`, from the integers of binary splitting.

With the first `degree + 1` arctangent terms written as `c / (5 b)` for `1/5` and `c' / (239 b')`
for `1/239`, and the radii `1 / (120 * 25 ^ degree)` and `1 / (13651680 * 57121 ^ degree)` of
`atanRadius`, the endpoints are `4 (c / (5 b) ∓ r) - (c' / (239 b') ± r')`.
-/
def piQuarterBounds (degree : Nat) : FractionBounds :=
  let five := split (atanStep (1 / 5)) 0 (degree + 1)
  let large := split (atanStep (1 / 239)) 0 (degree + 1)
  let fivePower : Nat := 25 ^ degree
  let largePower : Nat := 57121 ^ degree
  let fiveSum : Int := 24 * five.constantTerm * fivePower
  let largeSum : Int := 57120 * large.constantTerm * largePower
  let fiveDenominator : Nat := 30 * five.denominator * fivePower
  let largeDenominator : Nat := 13651680 * large.denominator * largePower
  { lower := (fiveSum - five.denominator) * largeDenominator -
      (largeSum + large.denominator) * fiveDenominator
    upper := (fiveSum + five.denominator) * largeDenominator -
      (largeSum - large.denominator) * fiveDenominator
    denominator := fiveDenominator * largeDenominator
    denominator_pos :=
      Nat.mul_pos
        (Nat.mul_pos (Nat.mul_pos (by decide) five.denominator_pos) (Nat.pow_pos (by decide)))
        (Nat.mul_pos (Nat.mul_pos (by decide) large.denominator_pos) (Nat.pow_pos (by decide))) }

/-- `2/π` and `π/2` at one precision, as lower bounds in units of `2 ^ -bits`. -/
structure PiLevel where
  /-- A lower bound within two units of `2 / π * 2 ^ bits`. -/
  twoOverPi : Nat
  /-- A lower bound within two units of `π / 2 * 2 ^ bits`. -/
  halfPi : Nat
  deriving Repr, DecidableEq

/--
`2/π` and `π/2` at `bits` fractional bits from one Machin enclosure `[lo, hi]` of π/4: the floors
of `2 ^ bits / (2 hi)` and of `2 ^ (bits + 1) * lo`, each one integer division.
-/
def piLevel (bits : Nat) : PiLevel :=
  let bounds := piQuarterBounds (piDegree bits)
  { twoOverPi := (bounds.denominator <<< bits) / (2 * bounds.upper.toNat)
    halfPi := (bounds.lower.toNat <<< (bits + 1)) / bounds.denominator }

/-! ## log 2 -/

/--
The degree of `logSeries 2` for `bits` fractional bits. The series runs in `1/3`, and its width
`2 / 3 ^ degree` is far below `2 ^ -bits` at two thirds of `bits` terms and eight more.
-/
def ln2Degree (bits : Nat) : Nat :=
  2 * bits / 3 + 8

/--
The endpoints `c / b - c' / b' ∓ 1 / 3 ^ degree` of `logSeries 2 degree`, where `c / b` and
`c' / b'` are the series of `-log (2/3)` and `-log (4/3)` from binary splitting.
-/
def ln2Bounds (degree : Nat) : FractionBounds :=
  let plus := split (logStep (1 / 3)) 0 degree
  let minus := split (logStep (-1 / 3)) 0 degree
  let power : Nat := 3 ^ degree
  let difference : Int :=
    (plus.constantTerm * minus.denominator - minus.constantTerm * plus.denominator) * power
  { lower := difference - plus.denominator * minus.denominator
    upper := difference + plus.denominator * minus.denominator
    denominator := plus.denominator * minus.denominator * power
    denominator_pos := Nat.mul_pos
      (Nat.mul_pos plus.denominator_pos minus.denominator_pos) (Nat.pow_pos (by decide)) }

/--
A lower bound within two units of `log 2 * 2 ^ bits`: the floor of `2 ^ bits` times the lower
endpoint of `logSeries 2 (ln2Degree bits)`, one integer division.
-/
def ln2Fixed (bits : Nat) : Nat :=
  let bounds := ln2Bounds (ln2Degree bits)
  (bounds.lower.toNat <<< bits) / bounds.denominator

/-! ## The cache -/

/-- Number of cached levels. -/
def Internal.cacheLevels : Nat := 40

/-- Fractional bits of level `level`: 64 at level zero, doubling at each level. -/
def levelBits (level : Nat) : Nat :=
  64 <<< level

/-- First cache level with at least `bits` fractional bits. -/
def levelFor (bits : Nat) : Nat :=
  if bits ≤ 64 then 0 else ((bits - 1) / 64).log2 + 1

set_option compiler.extract_closed false in
/-- `piLevel` at every cached level, each computed on first use and then shared. -/
def Internal.piCache : Array (Thunk PiLevel) :=
  Array.ofFn (n := Internal.cacheLevels) fun level => Thunk.mk fun _ => piLevel (levelBits level)

set_option compiler.extract_closed false in
/-- `ln2Fixed` at every cached level, each computed on first use and then shared. -/
def Internal.ln2Cache : Array (Thunk Nat) :=
  Array.ofFn (n := Internal.cacheLevels) fun level => Thunk.mk fun _ => ln2Fixed (levelBits level)

/-- `piLevel` at a level: cached below `Internal.cacheLevels`, computed on each call above. -/
def piLevelAt (level : Nat) : PiLevel :=
  if h : level < Internal.piCache.size then Internal.forceCache Internal.piCache[level]
  else piLevel (levelBits level)

/-- `ln2Fixed` at a level: cached below `Internal.cacheLevels`, computed on each call above. -/
def ln2FixedAt (level : Nat) : Nat :=
  if h : level < Internal.ln2Cache.size then Internal.forceCache Internal.ln2Cache[level]
  else ln2Fixed (levelBits level)

/-! ## Reads at any precision -/

/-- A lower bound within two units of `π / 2 * 2 ^ bits`, shifted down from its level. -/
def halfPiLower (bits : Nat) : Nat :=
  let level := levelFor bits
  (piLevelAt level).halfPi >>> (levelBits level - bits)

/-- A lower bound within two units of `2 / π * 2 ^ bits`, shifted down from its level. -/
def twoOverPiLower (bits : Nat) : Nat :=
  let level := levelFor bits
  (piLevelAt level).twoOverPi >>> (levelBits level - bits)

/-- A lower bound within two units of `log 2 * 2 ^ bits`, shifted down from its level. -/
def ln2Lower (bits : Nat) : Nat :=
  let level := levelFor bits
  ln2FixedAt level >>> (levelBits level - bits)

/--
`log 2 * 2 ^ bits` within one unit, rounded from a lower bound with 64 more bits. It is the
nearest integer unless the constant lies within `2 ^ -63` of a rounding midpoint.
-/
def ln2Faithful (bits : Nat) : Nat :=
  (ln2Lower (bits + 64) + 1 + 2 ^ 63) >>> 64

/--
An enclosure of `log 2` on the grid of `precision` fractional bits, from a lower bound with 64
more bits. It usually spans one grid unit.
-/
def ln2Grid (precision : Nat) : Interval Int :=
  let lower := ln2Lower (precision + 64)
  ⟨Int.ofNat (lower >>> 64), Int.ofNat ((lower + 2 + (2 ^ 64 - 1)) >>> 64)⟩

end FloatLib.Numerics.Enclosure.Constants
