/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
-- architecture: allow-proof-imports
The adaptive comparison carries an erased proof that the logarithm bounds eventually exclude zero.
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Enclosure.Proof
public import FloatLib.Numerics.Exact.RationalPower.Exact.Proof
public import FloatLib.Numerics.Kernel.Log2

/-!
# Exact comparisons with rational powers

`compare base exponent target` compares the real power `base ^ exponent` with a rational target, for
a nonnegative base. A unit or zero base, a zero exponent, and a nonpositive target are decided up
front.

For an exponent `n / d` in lowest terms the power lies below the target exactly when `base ^ n`
lies below `target ^ d`. When both of these rationals are short, at most 65,536 bits by the bound
`powerBits`, `compare` forms them and compares: a square root is one squaring of the target,
and a small integer power is one power of the base. That covers `rootn`, `cbrt`, and `pow` with an
exponent such as `2`, `-1`, `1 / 2` or `3 / 2`.

Direct exponentiation doesn't work in general, because the integers can be enormous even for small
inputs: a binary exponent with denominator `2 ^ 1074` gives a target power of that degree. So beyond
the bound the target is never raised to a power. Equality is decided from the exact-root descriptor
and capped exponentiation, where the root is raised to the exponent's numerator only against the
target's parts: no power formed that way exceeds a part of the root times the square of the
corresponding part of the target. Any other target differs from the power, so its logarithm
difference is nonzero, and the shared enclosure search doubles the series degree until the bound
excludes zero. Latency is unbounded in principle for a power extremely close to a target, since the
degree grows until the logarithm difference is resolved, as in MPFR.

Its real-number theorem is `RationalPower.compare_eq_real`, and `searchCompare_eq_real` is the
one of the search alone.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/-- A bound on the bits of the numerator and the denominator of `value ^ exponent` together. -/
def powerBits (value : ℚ) (exponent : Nat) : Nat :=
  exponent * (Kernel.log2 value.num.natAbs + Kernel.log2 value.den + 2)

/-- `base ^ exponent` for an integer exponent: a natural power of the base or of its reciprocal. -/
def intPow (base : ℚ) (exponent : Int) : ℚ :=
  if 0 ≤ exponent then base ^ exponent.toNat else base⁻¹ ^ exponent.natAbs

/--
Whether `compare` forms `base ^ exponent.num` and `target ^ exponent.den` to compare them: both
have at most 65,536 bits by the bound `powerBits`.
-/
def direct (base exponent target : ℚ) : Bool :=
  decide (max (powerBits base exponent.num.natAbs) (powerBits target exponent.den) ≤ 65536)

/--
Compare a positive power with a positive target without forming a power of the target: equality
first (`powEq`), then the logarithm search, which only sees a nonzero difference.
-/
def searchCompare (base exponent target : ℚ) (hbase : 0 < base) (htarget : 0 < target) :
    Ordering :=
  if hequal : powEq base exponent target then .eq
  else Enclosure.Comparison.compare
    (fun level => logDifference base exponent target (2 ^ level)) 0
    (exists_logDifference_separating base exponent target hbase htarget
      (fun hpower => hequal ((powEq_iff base exponent target hbase).mpr hpower)))

/--
Compare the real power `base ^ exponent` with a rational target.

The real interpretation requires `0 ≤ base`. Every exponent and target is allowed. Short powers
are compared directly (`direct`), and the others by `searchCompare`.
-/
def compare (base exponent target : ℚ) : Ordering :=
  if base = 1 ∨ exponent = 0 then cmp 1 target
  else if hbase : 0 < base then
    if htarget : 0 < target then
      if direct base exponent target then
        cmp (intPow base exponent.num) (target ^ exponent.den)
      else searchCompare base exponent target hbase htarget
    else .gt
  else cmp 0 target

end FloatLib.Numerics.RationalPower
