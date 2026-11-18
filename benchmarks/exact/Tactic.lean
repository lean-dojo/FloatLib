/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Harness
import FloatLib.Tactic.Interval
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The `interval` tactic, one goal at a time

Each row is the time to elaborate one `example` closed by FloatLib's `interval` tactic, which
reifies the goal, evaluates the checker in Lean's kernel and adds the proof
(`benchmarks/exact/run.sh tactic`).
-/

open FloatLibBenchmarks.Exact

#time_command "interval/x * (1 - x) ≤ 13/50 on [0, 1]" in
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : x * (1 - x) ≤ 13 / 50 := by interval

#time_command "interval/x ^ 3 - 2 * x ≤ 1/100 on [0, 7/5]" in
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (7 / 5)) : x ^ 3 - 2 * x ≤ 1 / 100 := by interval

#time_command "interval/exp x ≤ 11/4 on [0, 1]" in
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : Real.exp x ≤ 11 / 4 := by interval

#time_command "interval/x * exp (-x) ≤ 2/5 on [0, 3]" in
example (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 3) : x * Real.exp (-x) ≤ 2 / 5 := by interval

#time_command "interval/log x ≤ 7/10 on [1, 2]" in
example (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) : Real.log x ≤ 7 / 10 := by interval

#time_command "interval/sqrt x ≤ 3/2 on [1, 2]" in
example (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) : Real.sqrt x ≤ 3 / 2 := by interval

#time_command "interval/sin x ≤ x on [0, 1]" in
example (x : ℝ) (hx : x ∈ Set.Icc (1 / 10 : ℝ) 1) : Real.sin x ≤ x + 1 / 100 := by interval

#time_command "interval/x * y - x ^ 2 ≤ 1/3 on [0, 1]²" in
example (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    x * y - x ^ 2 ≤ 1 / 3 := by interval
