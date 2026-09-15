/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Rat.Defs

/-!
# Exact cross-format benchmark workload

We wanted every cross-format row to begin from the same mathematical inputs, so this module owns
them as exact rationals before any format-specific rounding or carrier conversion. Binary
interchange, posit, MPFR, and extracted Flocq can then consume one workload without pretending
that unlike encodings have identical representable sets.

We use sixteen deterministic, finite, ordinary values near one. Input creation is setup work and
stays outside every timed interval.
-/

@[expose] public section

namespace FloatLibBenchmarks.Support.ExactWorkload

/-- Deterministic ordinary finite input near one, represented exactly. -/
def rational (index salt : Nat) (negative : Bool) : Rat :=
  let numerator : Rat := ((index * salt + salt + 1) % 113 + 7 : Nat)
  let denominator : Rat := ((index * 11 + salt) % 29 + 32 : Nat)
  let magnitude := numerator / denominator
  if negative then -magnitude else magnitude

/-- First exact input vector, including both signs. -/
def xs : Array Rat :=
  (Array.range 16).map fun index =>
    rational index 37 (index % 5 == 0)

/-- Second exact nonzero input vector, including both signs. -/
def ys : Array Rat :=
  (Array.range 16).map fun index =>
    rational index 61 (index % 3 == 0)

/-- Nonnegative exact input vector used by square root. -/
def sqrtXs : Array Rat :=
  (Array.range 16).map fun index =>
    rational index 43 false

end FloatLibBenchmarks.Support.ExactWorkload
