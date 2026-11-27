/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.ElementaryTableProof

/-!
# Settings of the elementary table

At the legacy settings, `Backend.elementaryWith` gives the enclosures of `elementaryBounds?`, the
table of the `interval` tactic. The kernel compares the two on the inputs of the tactic's
examples, and `Backend.elementaryWith_legacy` proves that they agree on every input. The other
settings sharpen sine on a monotone panel, accept the logarithm, the square root and the inverse
sine and cosine where Mathlib's functions are total and `elementaryBounds?` refuses, and run the
exponential and the logarithm on the binary grid. The kernel decides every check on literals.
-/

@[expose] public section

namespace FloatLibTests.Numerics.ElementaryTable

open FloatLib.Numerics FloatLib.Numerics.Interval

-- The default settings are the legacy settings of the default configuration.
example : ElementarySettings.legacy {} = {} := rfl

/-- The configurations, operations and argument intervals of the `interval` tactic's elementary
examples, with the domains it rejects. -/
def tacticInputs : List (Backend.Config × UnaryOp × Interval ℚ) :=
  [({ degree := 12 }, .exp, ⟨0, 1⟩), ({ degree := 12 }, .cos, ⟨0, 1⟩),
    ({ degree := 12 }, .log, ⟨1, 2⟩), ({ degree := 12 }, .sqrt, ⟨1, 2⟩),
    ({}, .log, ⟨-1, 1⟩), ({}, .sqrt, ⟨-1, 1⟩),
    ({ precision := 0, degree := 0 }, .sqrt, ⟨0, 4⟩),
    ({ precision := 0, degree := 0 }, .asin, ⟨-1, 1⟩),
    ({ precision := 0, degree := 0 }, .asin, ⟨1 / 2, 1 / 2⟩),
    ({ precision := 2, degree := 0 }, .asin, ⟨1 / 2, 1 / 2⟩)]

-- The legacy equation, evaluated by the kernel on those inputs.
example : tacticInputs.all (fun (config, op, I) =>
    Backend.elementaryWith (.legacy config) op I == Backend.elementaryBounds? config op I) := by
  decide +kernel

-- The same equation for every configuration, operation and interval.
example (config : Backend.Config) (op : UnaryOp) (I : Interval ℚ) :
    Backend.elementaryWith (.legacy config) op I = Backend.elementaryBounds? config op I := by
  rw [Backend.elementaryWith_legacy]

-- As the tactic's examples expect, the legacy table refuses the logarithm and the square root of
-- an interval that leaves their domain.
example : Backend.elementaryWith (.legacy {}) .log ⟨-1, 1⟩ = none ∧
    Backend.elementaryWith (.legacy {}) .sqrt ⟨-1, 1⟩ = none := by
  decide +kernel

/-- The width of an enclosure, and `-1` when the table refuses. -/
def width : Option (Interval ℚ) → ℚ
  | some J => J.hi - J.lo
  | none => -1

-- Sine increases on `[0, 1]`, so the values at the two ends give a narrower enclosure than the
-- midpoint bound. Tangent divides the sharp enclosures of sine and cosine, and narrows too.
example :
    0 ≤ width (Backend.elementaryWith { trigDegree := 32, sharpTrig := some 128 } .sin ⟨0, 1⟩) ∧
      width (Backend.elementaryWith { trigDegree := 32, sharpTrig := some 128 } .sin ⟨0, 1⟩) <
        width (Backend.elementaryWith { trigDegree := 32 } .sin ⟨0, 1⟩) ∧
      0 ≤ width (Backend.elementaryWith { sharpTrig := some 128 } .tan ⟨0, 1 / 2⟩) ∧
      width (Backend.elementaryWith { sharpTrig := some 128 } .tan ⟨0, 1 / 2⟩) <
        width (Backend.elementaryWith {} .tan ⟨0, 1 / 2⟩) := by
  decide +kernel

example : Backend.elementaryWith { sharpTrig := some 0 } .sin (point 1) = some ⟨0, 1⟩ ∧
    (tanBounds? (point 1) 16).isSome ∧
    Backend.elementaryWith { sharpTrig := some 0 } .tan (point 1) = tanBounds? (point 1) 16 := by
  decide +kernel

-- With `total`, the logarithm of `[-3, -1]` encloses `log |x|`, that is `[0, log 3]`, which the
-- legacy table refuses.
example : Backend.elementaryWith (.legacy {}) .log ⟨-3, -1⟩ = none ∧
    (Backend.elementaryWith { total := true } .log ⟨-3, -1⟩).map
      (fun J => decide (-1 / 10 ^ 6 ≤ J.lo ∧ J.lo ≤ 0 ∧ 1098 / 1000 ≤ J.hi ∧
        J.hi ≤ 1099 / 1000)) = some true := by
  decide +kernel

-- With `total`, the square root of `[-1, 4]` is exactly `[0, 2]`, since `√x = 0` for `x ≤ 0`.
example : Backend.elementaryWith (.legacy {}) .sqrt ⟨-1, 4⟩ = none ∧
    Backend.elementaryWith { total := true } .sqrt ⟨-1, 4⟩ = some ⟨0, 2⟩ := by
  decide +kernel

-- With `total`, the inverse sine of `[2, 3]` is close to `π / 2`, Mathlib's value beyond `1`, and
-- the inverse cosine of `[-3, -2]` is close to `π`. The legacy table refuses both.
example : Backend.elementaryWith (.legacy {}) .asin ⟨2, 3⟩ = none ∧
    (Backend.elementaryWith { total := true } .asin ⟨2, 3⟩).map
      (fun J => decide (15707 / 10000 ≤ J.lo ∧ J.hi ≤ 15708 / 10000)) = some true ∧
    Backend.elementaryWith (.legacy {}) .acos ⟨-3, -2⟩ = none ∧
    (Backend.elementaryWith { total := true } .acos ⟨-3, -2⟩).map
      (fun J => decide (31415 / 10000 ≤ J.lo ∧ J.hi ≤ 31416 / 10000)) = some true := by
  decide +kernel

-- On the binary grid, the exponential of `[0, 1]` reaches `e`. The grid logarithm needs a
-- positive interval, also with `total`.
example : (Backend.elementaryWith { gridExpLog := some 64 } .exp ⟨0, 1⟩).map
      (fun J => decide (J.lo ≤ 1 ∧ 2718281 / 10 ^ 6 ≤ J.hi ∧ J.hi ≤ 2718282 / 10 ^ 6)) =
      some true ∧
    Backend.elementaryWith { gridExpLog := some 64, total := true } .log ⟨-3, -1⟩ = none ∧
    Backend.elementaryWith { gridExpLog := some 64, total := true } .log (point 0) = none := by
  decide +kernel

/-- An upper end of an enclosure of the table, checked against `c`, bounds the value of the
operation at every real member of the input interval. -/
theorem lt_of_check {s : ElementarySettings} {op : UnaryOp} {I : Interval ℚ} {x : ℝ} {c : ℚ}
    (hx : I.ContainsReal some x)
    (h : (Backend.elementaryWith s op I).map (fun J => decide (J.hi < c)) = some true) :
    op.eval x < c := by
  cases hJ : Backend.elementaryWith s op I with
  | none => simp [hJ] at h
  | some J =>
    simp only [hJ, Option.map_some, Option.some.injEq, decide_eq_true_eq] at h
    exact ((containsReal_some_iff _ _).1 (Backend.containsReal_elementaryWith s hJ hx)).2.trans_lt
      (by exact_mod_cast h)

-- A real fact from the total logarithm: `log (-2) = log 2 < 0.7`.
example : Real.log (-2) < 7 / 10 := by
  have h := lt_of_check (s := { total := true }) (op := .log) (I := point (-2)) (x := -2)
    (c := 7 / 10) (by simp [point]) (by decide +kernel)
  simpa [UnaryOp.eval] using h

end FloatLibTests.Numerics.ElementaryTable
