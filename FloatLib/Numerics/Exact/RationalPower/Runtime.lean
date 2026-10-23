/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
-- architecture: allow-proof-imports
The adaptive comparison carries an erased proof that the logarithm bounds eventually exclude zero.
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Exact.Proof
public import FloatLib.Numerics.Exact.RationalPower.Enclosure.Proof

/-!
# Exact comparisons with rational powers

`compare base exponent target` compares the real power `base ^ exponent` with a rational
target for a nonnegative base. A unit or zero base, a zero exponent and a nonpositive target are
decided up front. Equality comes next, from the exact-root descriptor and capped exponentiation.
Any other target differs from the power, so its logarithm difference is nonzero, and the shared
enclosure search doubles the series degree until the bound excludes zero.

The target is never raised to a power, and the root is raised to the exponent's numerator only by
capped exponentiation against the target's parts. No power formed that way exceeds a part of the
root times the square of the corresponding part of the target. For an integral exponent the root
is the base itself. Comparing `base ^ exponent.num` with `target ^ exponent.den` directly would
need integers that can be enormous even for small inputs: a binary exponent with denominator
`2 ^ 1074` gives a target power of that degree. Latency is still unbounded in principle for a
power extremely close to a target, since the degree grows until the logarithm difference is
resolved, as in MPFR.

The real-number theorem is `RationalPower.compare_eq_real`.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/--
Compare the real power `base ^ exponent` with a rational target.

The real interpretation requires `0 ≤ base`. Every exponent and target is allowed. Equality is
decided before the logarithm search, so the search only sees a nonzero difference.
-/
def compare (base exponent target : ℚ) : Ordering :=
  if base = 1 ∨ exponent = 0 then cmp 1 target
  else if hbase : 0 < base then
    if htarget : 0 < target then
      if hequal : powEq base exponent target then .eq
      else Enclosure.Comparison.compare
        (fun level => logDifference base exponent target (2 ^ level)) 0
        (exists_logDifference_separating base exponent target hbase htarget
          (fun hpower => hequal ((powEq_iff base exponent target hbase).mpr hpower)))
    else .gt
  else cmp 0 target

end FloatLib.Numerics.RationalPower
