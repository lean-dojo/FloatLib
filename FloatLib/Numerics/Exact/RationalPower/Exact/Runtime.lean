/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.IntegerRoot.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Basic

/-!
# Exact roots of rational powers

Write a positive base in lowest terms as `A / B` and an exponent as `n / d`. The real power
`(A / B) ^ (n / d)` is rational exactly when `A` and `B` are perfect `d`-th powers, and then it
equals `c ^ n` for the rational root `c` of the base. `exactRoot?` decides this without forming
any power of the base. A radicand `m ≥ 2` with at most `d` bits cannot be a perfect `d`-th power,
since its root would be at least two. That test runs before the integer root, so even an
enormous binary denominator `d` costs one comparison.

The descriptor stores `c` and `n`, never `c ^ n`. The size of that power can be far beyond memory
although its magnitude is moderate. For example, `x = (1 + 2^-26)^2` and `y = (2^35 + 1) / 2` are
binary64 values, `x ^ y` is about `2^738.66`, and the odd part of its numerator has about
`8.9 * 10^11` bits. Equality with a rational boundary is decided instead by capped exponentiation
of the root's numerator and denominator, which stops as soon as a partial power exceeds the
corresponding part of the boundary.

An exact value is built only when it can be a cell boundary of a binary format: its denominator
must be a power of two and its odd significand must stay below `2 ^ (precision + 3)`. The same
bit-length bounds decide this before the odd significand is formed.

The proofs are in `RationalPower.Exact.Proof`.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/--
The exact `degree`-th root of `value`, when `value` is a perfect power.

A radicand of at least two with at most `degree` bits is rejected before the integer root is
computed, because a root of at least two would make it at least `2 ^ degree`. The contract
assumes a positive degree.
-/
def perfectRoot? (degree value : Nat) : Option Nat :=
  if value ≤ 1 then some value
  else if value.log2 < degree then none
  else
    let root := IntegerRoot.newton degree value
    if root ^ degree = value then some root else none

/--
For `base ≥ 1`, `base ^ exponent` when it is at most `cap`, and `none` otherwise.

Binary exponentiation stops as soon as a partial power exceeds the cap. Each partial power is at
most the final power, so the answer is then `none`. Every product is formed from a partial power
at most the cap, so none exceeds the base times the square of the cap, whatever the exponent.
-/
def cappedPow? (base exponent cap : Nat) : Option Nat :=
  if exponent = 0 then
    if 1 ≤ cap then some 1 else none
  else
    match cappedPow? base (exponent / 2) cap with
    | none => none
    | some half =>
      let power := if exponent % 2 = 0 then half * half else half * half * base
      if power ≤ cap then some power else none
termination_by exponent
decreasing_by omega

/--
Decide `base ^ exponent = target` without forming a power of `base` above `base * target ^ 2`.

For `base ≥ 2` the power is at least `2 ^ (exponent * log2 base)`, so bit lengths reject most
unequal pairs at once. Capped exponentiation decides the remaining ones.
-/
def natPowEq (base exponent target : Nat) : Bool :=
  if base ≤ 1 then
    if exponent = 0 then decide (target = 1) else decide (target = base)
  else if target.log2 < exponent * base.log2 then false
  else decide (cappedPow? base exponent target = some target)

/--
A rational power `base ^ (n / d)` described by a rational root.

`root ^ d` is the base and `numerator` is `n`, so the power is `root ^ numerator`. The descriptor
does not store that power, which can be far too large to construct.
-/
structure ExactRoot where
  /-- A rational whose power by the exponent denominator is the base. -/
  root : ℚ
  /-- The exponent numerator. The described power is `root ^ numerator`. -/
  numerator : Int
  deriving DecidableEq, Repr

/--
Classify `base ^ exponent` as rational or irrational without forming a power of the base.

For a base `A / B` and an exponent `n / d` in lowest terms, the power is rational exactly when
`A` and `B` are perfect `d`-th powers. The result then describes it as `root ^ n`. The real
interpretation requires a nonnegative base, and the classification reads the base's magnitude.
-/
def exactRoot? (base exponent : ℚ) : Option ExactRoot :=
  match perfectRoot? exponent.den base.num.natAbs, perfectRoot? exponent.den base.den with
  | some numerator, some denominator =>
    some { root := (numerator : ℚ) / (denominator : ℚ), numerator := exponent.num }
  | _, _ => none

namespace ExactRoot

/--
The rational whose natural power `|numerator|` is the described value: the root itself for a
nonnegative numerator, and its reciprocal otherwise.
-/
def powerBase (exact : ExactRoot) : ℚ :=
  if 0 ≤ exact.numerator then exact.root else exact.root⁻¹

/--
Decide whether the described power equals a rational target.

For a positive root the power is `powerBase ^ |numerator|`, whose numerator and denominator are
the powers of those of `powerBase`. It equals a target exactly when the target is positive and
both parts agree. `natPowEq` decides each part, and no power it forms exceeds the part of
`powerBase` times the square of the corresponding part of the target.
-/
def powEq (exact : ExactRoot) (target : ℚ) : Bool :=
  decide (0 < target) &&
    natPowEq exact.powerBase.num.natAbs exact.numerator.natAbs target.num.natAbs &&
    natPowEq exact.powerBase.den exact.numerator.natAbs target.den

/--
The described power as an exact dyadic, when it can be a cell boundary of a binary format with
`precision` significand bits.

A boundary has a power-of-two denominator and an odd significand below `2 ^ (precision + 3)`.
The denominator test and a bit-length bound on the odd part of the numerator run first, and
capped exponentiation then forms the odd power. The power of two stays in the exponent, so a value
such as `2 ^ (2 ^ 60)` needs no large integer. A zero numerator describes one, whatever the root.
The contract assumes a positive root.
-/
def toDyadic? (exact : ExactRoot) (precision : Nat) : Option Dyadic :=
  let base := exact.powerBase
  let exponent := exact.numerator.natAbs
  let scale := base.den.log2
  if exponent ≠ 0 ∧ base.den ≠ 2 ^ scale then none
  else
    let shift := base.num.trailingZeros
    let odd := (base.num >>> shift).natAbs
    if precision + 3 ≤ exponent * odd.log2 then none
    else
      match cappedPow? odd exponent (2 ^ (precision + 3) - 1) with
      | none => none
      | some significand =>
        some { negative := false, significand, exponent := ((shift : Int) - scale) * exponent }

end ExactRoot

/--
Decide `base ^ exponent = target` for a positive base.

An irrational power equals no rational target. Otherwise the exact-root descriptor compares the
root's powers with the target's numerator and denominator by capped exponentiation. The cost is
polynomial in the bit lengths of the base, the exponent and the target, not in the exponent's
magnitude.
-/
def powEq (base exponent target : ℚ) : Bool :=
  match exactRoot? base exponent with
  | some exact => exact.powEq target
  | none => false

end FloatLib.Numerics.RationalPower
