/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Constants.Runtime

/-!
# Payne-Hanek reduction modulo π/2

An argument `x = m * 2 ^ e` with `m > 0` is reduced modulo `π/2` from a window of the bits of
`2/π`. Let `T` be the cached lower bound of `2/π * 2 ^ N` at a level of `Constants` with
`N ≥ e + window + 6` bits, so that `x * 2/π` exceeds `m * T * 2 ^ (e - N)` by less than
`2 m * 2 ^ (e - N)`. The bits of `T` of weight `2 ^ (N - e + 2)` and above contribute multiples of
four, which change neither the quadrant nor the remainder, and the bits below the window contribute
less than `m` units of its last place. So the reduction multiplies `m` by the `window` bits of `T`
below that weight and keeps the product modulo `2 ^ window`: one shift of `T`, one product and one
remainder, whatever the size of `x * 2/π`. The level is chosen from `e`: the window needs
`b = max e 0 + window + 6` bits of `2/π`, and the level read holds at most `max 64 (2 b)` bits,
computed once, on first use.

The result is a quadrant `q` and a fraction `F` with `x * 2/π = 4 j + q + (F + η) / 2 ^ scale` for
an integer `j` and some `η` with `0 ≤ η < error = 2 m` (`ArgumentReduction.Proof`). The fraction has
magnitude at most half a quarter turn. When `QuarterTurns.accepts bits` holds, `F` has the sign of
`F + η` and relative error at most `2 ^ -bits`. A rejected reduction is retried with a doubled
window: the error stays `2 m` units while the units shrink, so some window is accepted for every
nonzero argument (`ArgumentReduction.Termination`). `reduce` bounds the number of doublings and
returns its first accepted attempt or else its last one, so it needs no search with a termination
proof. Callers check `QuarterTurns.accepts` on its result. `fuelWithin?` gives the most doublings
whose windows stay within a level of the cache.

`QuarterTurns.argumentNumerator` multiplies the fraction by the cached lower bound of `π/2` to give
the reduced argument in radians, and `rotate` gives the sine and cosine of `x` from those of the
reduced argument. Binary sine and cosine read this reduction.

The method is that of M. H. Payne and R. N. Hanek, *Radian reduction for trigonometric functions*,
ACM SIGNUM Newsletter 18(1), 1983, pages 19-24.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.ArgumentReduction

/--
An argument `x` reduced modulo `π/2`: `x * 2/π = 4 j + quadrant + (fraction + η) / 2 ^ scale` for an
integer `j` and an unknown `η` with `0 ≤ η < error`.
-/
structure QuarterTurns where
  /-- The quotient of `x` by `π/2`, modulo four. -/
  quadrant : Fin 4
  /-- The remainder in units of `2 ^ -scale` quarter turns, below the unknown part `η`. -/
  fraction : Int
  /-- Fractional bits of `fraction`. -/
  scale : Nat
  /-- A strict upper bound of `η`, in units of `2 ^ -scale` quarter turns. -/
  error : Nat
  deriving Repr, DecidableEq

/-- The cache level that `reduceWindow` reads: at least `e + window + 6` and `window + 6` bits. -/
def windowLevel (e : Int) (window : Nat) : Nat :=
  Constants.levelFor (max (e + window + 6).toNat (window + 6))

/--
Reduce `m * 2 ^ e` modulo `π/2` with `window` bits of `2/π`.

With `T` the lower bound of `2/π * 2 ^ N` at level `windowLevel e window` and
`shift = N - e + 2 - window`, `piece` holds the bits of `T` from `shift` to `shift + window`. The
product `y = m * piece mod 2 ^ window` is `x * 2/π` modulo four in units of `2 ^ -scale`, with
`scale = window - 2`. Rounding `y` to the nearest unit `2 ^ scale` gives the quadrant, and the
signed difference is the fraction. The bits of `T` below the window and the error of `T` make the
true remainder exceed the fraction by less than `2 m` units.
-/
def reduceWindow (m : Nat) (e : Int) (window : Nat) : QuarterTurns :=
  let level := windowLevel e window
  let shift := ((Constants.levelBits level : Int) - e + 2).toNat - window
  let modulus := 2 ^ window
  let piece := ((Constants.piLevelAt level).twoOverPi >>> shift) % modulus
  let y := m * piece % modulus
  let unit := 2 ^ (window - 2)
  let k := (y + unit / 2) / unit
  { quadrant := ⟨k % 4, Nat.mod_lt _ (by decide)⟩
    fraction := (y : Int) - (k * unit : Nat)
    scale := window - 2
    error := 2 * m }

/--
Whether a reduction keeps `bits` relative bits: `error * 2 ^ (bits + 1) ≤ |fraction|`. Then the
fraction has the sign of the true remainder and differs from it by at most `2 ^ -bits` of it.
-/
def QuarterTurns.accepts (bits : Nat) (q : QuarterTurns) : Bool :=
  q.error <<< (bits + 1) ≤ q.fraction.natAbs

/--
The first window for a significand of `p` bits and `bits` relative bits. Its scale is
`2 p + bits + 18`. A remainder of `f` quarter turns from the nearest multiple of `π/2` gives
`|fraction| > |f| * 2 ^ scale - 2 m`, and acceptance asks for `2 m * 2 ^ (bits + 1)`, so for
`p ≤ bits + 1` the first window accepts every remainder of at least `2 ^ -(p + 16)` quarter turns.
That covers the closest approaches to multiples of `π/2` in the hard-case corpus of binary16,
bfloat16, binary32, binary64 and binary128.
-/
def startWindow (p bits : Nat) : Nat :=
  2 * p + bits + 20

/-- Window of attempt `attempt`: the start window doubled `attempt` times. -/
def attemptWindow (p bits attempt : Nat) : Nat :=
  startWindow p bits <<< attempt

/--
Reduce `m * 2 ^ e` with the start window for a `p`-bit significand, doubling the window until
the reduction passes `QuarterTurns.accepts bits` or `fuel` doublings are used. Returns the first
accepted attempt, or the last attempt when every one is rejected, so callers that need `bits`
relative bits check `QuarterTurns.accepts bits` on the result. Every attempt reads at most level
`windowLevel e (attemptWindow p bits fuel)`.
-/
def reduce (m : Nat) (e : Int) (p bits fuel : Nat) : QuarterTurns :=
  go 0 fuel
where
  /-- Try attempt `attempt` and, while it is rejected, at most `fuel` attempts after it. -/
  go (attempt : Nat) : Nat → QuarterTurns
    | 0 => reduceWindow m e (attemptWindow p bits attempt)
    | fuel + 1 =>
        let q := reduceWindow m e (attemptWindow p bits attempt)
        if q.accepts bits then q else go (attempt + 1) fuel

/--
The fuel of `reduce` within a resource limit: the largest `count ≤ fuel` whose window
`attemptWindow p bits count` reads a cache level of at most `limit` at exponent `e`, or `none` when
not even the first window does. The attempts before it have narrower windows, so they read at most
`limit` too.
-/
def fuelWithin? (e : Int) (p bits limit : Nat) : Nat → Option Nat
  | 0 => if windowLevel e (attemptWindow p bits 0) ≤ limit then some 0 else none
  | fuel + 1 =>
      if windowLevel e (attemptWindow p bits (fuel + 1)) ≤ limit then some (fuel + 1)
      else fuelWithin? e p bits limit fuel

/--
The reduced argument in radians as an integer over `2 ^ (scale + precision)`: the fraction times
the cached lower bound `halfPiLower precision` of `π/2 * 2 ^ precision`. It differs from the reduced
argument `(fraction + η) / 2 ^ scale * π/2` by at most `error / 2 ^ scale * π/2` plus
`|fraction| / 2 ^ scale * 2 ^ (1 - precision)`.
-/
def QuarterTurns.argumentNumerator (q : QuarterTurns) (precision : Nat) : Int :=
  q.fraction * Constants.halfPiLower precision

/--
The sine and cosine of `quadrant * π/2 + r` from the sine and cosine of `r`: each quarter turn
maps `(sin, cos)` to `(cos, -sin)`.
-/
def rotate {α : Type} [Neg α] (quadrant : Fin 4) (sine cosine : α) : α × α :=
  match quadrant.val with
  | 0 => (sine, cosine)
  | 1 => (cosine, -sine)
  | 2 => (-sine, -cosine)
  | _ => (-cosine, sine)

end FloatLib.Numerics.Enclosure.ArgumentReduction
