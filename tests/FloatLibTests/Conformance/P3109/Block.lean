/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Proof
public import FloatLib.Floats.Formats.P3109.Block.Root.Proof
public import FloatLibTests.Accounting

/-!
# P3109 chapter 5 block regressions

These cases cover explicit and selected scales, special projection rules, exact reductions,
independent source scales, elementwise fused arithmetic, and explicit random words per lane.
Root operations check normalization before rounding, including negative result scales.
-/

@[expose] public section

set_option compiler.extract_closed false

namespace FloatLibTests.Conformance.P3109.Block

open FloatLib.Numerics FloatLib.Floats
open FloatLib.Floats.Formats.P3109
open Arithmetic FloatLibTests.Accounting

/-- Two lanes suffice to distinguish shared attributes from lane-specific random words. -/
abbrev Two : ℕ+ := ⟨2, by decide⟩

/-- Construct a two-lane vector with an intrinsic length proof. -/
def pair {α : Type} (left right : α) : Vector α Two := ⟨#[left, right], rfl⟩

/-- An exact observation destination exposes intermediates without introducing test rounding. -/
def exactDestination : Destination (NumericalValue Rat) := ⟨fun _ value => value⟩

/-- Independently scaled rational source block. -/
def source (scale left right : Rat) : Formats.P3109.Block Rat Rat Two :=
  ⟨scale, pair left right⟩

/-- Closed special normalization, finite conversions, max-finite scales, and exact reductions. -/
def arithmeticFailures : Thunk Nat := ⟨fun _ =>
  let left := source 2 (1 / 2) (3 / 2)
  let right := source 3 (2 / 3) (-1 / 3)
  let scaleDestination : Destination Rat := ⟨fun _ value => value.finite?.getD 0⟩
  let selected := Formats.P3109.Block.convertToMaxAbsFinite scaleDestination
    exactDestination {} {} (pair (-3 : Rat) 1)
  let fused := Formats.P3109.Block.ternary exactDestination {} Arithmetic.fma
    left right (source 1 1 1) (2 : Rat)
  countFailures
    [ decide (Formats.P3109.Block.decode left = pair (.finite 1) (.finite 3))
    , decide (Formats.P3109.Block.convertFrom exactDestination {} left =
        pair (.finite 1) (.finite 3))
    , decide ((Formats.P3109.Block.convertTo exactDestination {} (pair (2 : Rat) 4) 2).values =
        pair (.finite 1) (.finite 2))
    , decide (Formats.P3109.Block.normalize (.finite 0) (.infinity true) = .finite 0)
    , decide (Formats.P3109.Block.normalize (.finite 0) (.exceptional .nan) = Arithmetic.nan)
    , decide (Formats.P3109.Block.normalize (.infinity true) (.finite (-3)) = .finite 1)
    , decide (Formats.P3109.Block.normalize (.infinity false) (.infinity true) = .finite (-1))
    , decide (Formats.P3109.Block.normalize (.infinity true) (.finite 0) = .finite 0)
    , decide (Formats.P3109.Block.maxAbsFinite (pair (.infinity false) (.finite (-3))) =
        .finite 3)
    , decide (Formats.P3109.Block.maxAbsFinite (pair Arithmetic.nan (.infinity true)) =
        .infinity false)
    , decide (selected.scale = 3)
    , decide (selected.values = pair (.finite (-1)) (.finite (1 / 3)))
    , decide (Formats.P3109.Block.reduceAdd exactDestination {} left = .finite 4)
    , decide (Formats.P3109.Block.reduceMultiply exactDestination {} left = .finite 3)
    , decide (Formats.P3109.Block.dotProduct exactDestination {} left right = .finite (-1))
    , decide (fused.values = pair (.finite (3 / 2)) (.finite (-1)))
    , decide (Arithmetic.clamp (.finite 3) (.finite 1) (.finite 2) = .finite 2)
    , decide (Arithmetic.clamp (.finite 0) (.finite 1) (.finite 2) = .finite 1)
    , decide (Arithmetic.clamp (.finite 0) (.finite 2) (.finite 1) = Arithmetic.nan)
    , decide (Arithmetic.clamp Arithmetic.nan (.infinity false) (.infinity false) =
        Arithmetic.nan)
    , decide (Arithmetic.clamp (.finite 0) (.infinity false) (.infinity false) =
        .infinity false)
    , decide (Arithmetic.clamp (.finite 0) (.infinity true) (.infinity true) = .infinity true)
    , decide (Arithmetic.clamp (.finite 0) (.infinity true) (.infinity false) = .finite 0) ]⟩

/-- All three stochastic modes use independently supplied same-width random words. -/
def stochasticFailures : Thunk Nat := ⟨fun _ =>
  let format := Format.signed 6 5 .extended
  let words : Vector (BitVec 2) Two := pair 0 3
  countWhereFailures [BlockRounding.stochasticA 2 words, .stochasticB 2 words,
      .stochasticC 2 words] fun rounding =>
    let result := Formats.P3109.Block.convertTo (Destination.p3109 format) ⟨rounding, .none⟩
      (pair (33 / 32 : Rat) (33 / 32)) (1 : Rat)
    decide (result.values.map Mixed.decode = pair (.finite 1) (.finite (17 / 16)))⟩

/-- Actual projected roots retain exact scale normalization and direction before saturation. -/
def rootFailures : Thunk Nat := ⟨fun _ =>
  let format := Format.signed 8 4 .extended
  let small := Format.signed 6 5 .extended
  let roots := Formats.P3109.Block.sqrt format {} (source 1 25 4) (2 : Rat)
  let negativeRoots := Formats.P3109.Block.sqrt format {} (source 1 25 4) (-2 : Rat)
  let reciprocal := Formats.P3109.Block.rsqrt format {} (source 1 4 16) (1 / 2 : Rat)
  let norms := Formats.P3109.Block.hypot format {} (source 1 3 5) (source 1 4 12) (2 : Rat)
  let directed := Formats.P3109.Block.sqrt small ⟨.scalar .towardPositive, .none⟩
    (source 1 2 2) (-2 : Rat)
  countFailures
    [ decide (roots.values.map Mixed.decode = pair (.finite (5 / 2)) (.finite 1))
    , decide (negativeRoots.values.map Mixed.decode = pair (.finite (-5 / 2)) (.finite (-1)))
    , decide (reciprocal.values.map Mixed.decode = pair (.finite 1) (.finite (1 / 2)))
    , decide (norms.values.map Mixed.decode = pair (.finite (5 / 2)) (.finite (13 / 2)))
    , decide (directed.values.map Mixed.decode = pair (.finite (-11 / 16)) (.finite (-11 / 16)))
    , decide (BlockRoot.normalize (.finite 0) (.finite (-1)) = ⟨false, Arithmetic.nan⟩)
    , decide (BlockRoot.normalize (.infinity true) (.infinity false) = ⟨true, .finite 1⟩) ]⟩

/-- Non-transcendental P3109 block regression failure count. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  arithmeticFailures.get + stochasticFailures.get + rootFailures.get⟩

/-- Report the chapter 5 block checks in the core executable suite. -/
def report : Thunk ReportSection := ⟨fun _ =>
  let failures := totalFailures.get
  { title := "P3109 block operations"
    body := s!"TOTAL: {failures}"
    failures }⟩

end FloatLibTests.Conformance.P3109.Block
