/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Cast.Widening
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Tactic.CompilerOptimize

/-!
# Standard posit precision conversion

Posit Standard (2022), §6.1, writes the width-parameterized operation as
`pₘToₙ`. Its specification rounds the exact source value at the destination
width and preserves NaR. The proved execution path appends zero bits when
widening and uses the existing exact rounder when narrowing.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Floats.ExecFloat

/-- Posit Standard (2022), §6.1: convert any source width to `target`, rounding once. -/
def pₘToₙ {source : Format} (target : Format) (value : Model source) : Model target :=
  match value.toRat? with
  | none => nar target
  | some exact => roundRat target exact

/-- Section 6.1 preserves NaR at every destination width. -/
@[simp] theorem pₘToₙ_nar (source target : Format) :
    pₘToₙ target (nar source) = nar target := by
  simp [pₘToₙ]

/-- Section 6.1 applies the destination's §4.1 rounder to a finite source value. -/
theorem pₘToₙ_eq_roundRat {source : Format} (target : Format) (value : Model source)
    {q : Rat} (hvalue : value.toRat? = some q) :
    pₘToₙ target value = roundRat target q := by
  simp [pₘToₙ, hvalue]

/-- Section 6.1 widening is exactly the complete source word with zero bits appended. -/
theorem pₘToₙ_eq_append_zero {source : Format} (target : Format)
    (hwidth : source.bits ≤ target.bits) (value : Model source) :
    pₘToₙ target value =
      ofNatBits (value.toNatBits * 2 ^ (target.bits - source.bits)) := by
  cases hvalue : value.toRat? with
  | none =>
      have hwide := (toRat?_widen target hwidth value).trans hvalue
      have hnar := (isNaR_eq_true_iff _).mp ((toRat?_eq_none_iff _).mp hwide)
      simpa [pₘToₙ, hvalue] using hnar.symm
  | some q =>
      rw [pₘToₙ_eq_roundRat target value hvalue]
      exact roundRat_widen target hwidth value q hvalue

/-- Section 6.1 conversion to the same descriptor is the identity, NaR included. -/
@[simp] theorem pₘToₙ_self {format : Format} (value : Model format) :
    pₘToₙ format value = value := by
  simpa using pₘToₙ_eq_append_zero format (le_refl _) value

/-- Section 6.1 execution: append zero bits on widening; use exact rounding on narrowing. -/
def precisionConvert {source : Format} (target : Format) (value : Model source) : Model target :=
  if source.bits ≤ target.bits then
    ofNatBits (value.toNatBits * 2 ^ (target.bits - source.bits))
  else
    match value.toRat? with
    | none => nar target
    | some exact => roundRat target exact

/-- The direct widening branch and exact narrowing branch both implement §6.1. -/
@[kernel_optimize] theorem pₘToₙ_eq_precisionConvert {source : Format}
    (target : Format) (value : Model source) :
    pₘToₙ target value = precisionConvert target value := by
  unfold precisionConvert
  split
  · exact pₘToₙ_eq_append_zero target ‹_› value
  · rfl

/-- Compile §6.1 conversion with the proved word-level widening branch. -/
compiled_as pₘToₙ := precisionConvert by pₘToₙ_eq_precisionConvert

/-- Certified §6.1 precision conversion for every pair of valid posit widths. -/
@[compiler_optimize direct]
def precisionConversion : Backend.Certified (@pₘToₙ) where
  estimate := { name := "posit precision conversion", kind := .generic, steadyCost := 1 }
  run := @precisionConvert
  run_eq_spec := by
    funext source target value
    exact (pₘToₙ_eq_precisionConvert target value).symm

end FloatLib.Floats.Formats.Posit.Model
