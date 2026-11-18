/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Format
public import FloatLib.Floats.Formats.P3109.Block.Proof
public import FloatLib.Floats.Formats.P3109.Block.Root.Report
public import FloatLib.Floats.Formats.P3109.Arithmetic.Scaled
public import FloatLib.Floats.Formats.P3109.Arithmetic.Instances
public import FloatLibTests.Accounting

/-!
# P3109 chapter 5 block regressions

These cases cover given and selected scales, special projection rules, exact reductions,
independent source scales, elementwise fused arithmetic, and per-lane random words.
Root operations check normalization before rounding, including negative result scales.

P3109 interim report v4.1, §§5.6–5.8, specifies these operation families.
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
  let selected := Formats.P3109.Block.ConvertToBlockMaxAbsFinite scaleDestination
    exactDestination {} {} (pair (-3 : Rat) 1)
  let fused := Formats.P3109.Block.ternary exactDestination {} Arithmetic.FMA
    left right (source 1 1 1) (2 : Rat)
  countFailures
    [ decide (Formats.P3109.Block.decode left = pair (.finite 1) (.finite 3))
    , decide (Formats.P3109.Block.ConvertFromBlock exactDestination {} left =
        pair (.finite 1) (.finite 3))
    , decide ((Formats.P3109.Block.ConvertToBlock exactDestination {} (pair (2 : Rat) 4) 2).values =
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
    , decide (Formats.P3109.Block.BlockReduceAdd exactDestination {} left = .finite 4)
    , decide (Formats.P3109.Block.BlockReduceMultiply exactDestination {} left = .finite 3)
    , decide (Formats.P3109.Block.BlockDotProduct exactDestination {} left right = .finite (-1))
    , decide (fused.values = pair (.finite (3 / 2)) (.finite (-1)))
    , decide (Arithmetic.Clamp (.finite 3) (.finite 1) (.finite 2) = .finite 2)
    , decide (Arithmetic.Clamp (.finite 0) (.finite 1) (.finite 2) = .finite 1)
    , decide (Arithmetic.Clamp (.finite 0) (.finite 2) (.finite 1) = Arithmetic.nan)
    , decide (Arithmetic.Clamp Arithmetic.nan (.infinity false) (.infinity false) =
        Arithmetic.nan)
    , decide (Arithmetic.Clamp (.finite 0) (.infinity false) (.infinity false) =
        .infinity false)
    , decide (Arithmetic.Clamp (.finite 0) (.infinity true) (.infinity true) = .infinity true)
    , decide (Arithmetic.Clamp (.finite 0) (.infinity true) (.infinity false) = .finite 0) ]⟩

/-- All three stochastic modes use independently supplied same-width random words. -/
def stochasticFailures : Thunk Nat := ⟨fun _ =>
  let format := Format.signed 6 5 .extended
  let words : Vector (BitVec 2) Two := pair 0 3
  countWhereFailures [BlockRounding.stochasticA 2 words, .stochasticB 2 words,
      .stochasticC 2 words] fun rounding =>
    let result := Formats.P3109.Block.ConvertToBlock (Destination.p3109 format) ⟨rounding, .none⟩
      (pair (33 / 32 : Rat) (33 / 32)) (1 : Rat)
    decide (result.values.map Mixed.decode = pair (.finite 1) (.finite (17 / 16)))⟩

/-- Projected roots keep exact scale normalization and direction before saturation. -/
def rootFailures : Thunk Nat := ⟨fun _ =>
  let format := Format.binary8p4se
  let small := Format.signed 6 5 .extended
  let roots := Formats.P3109.Block.BlockSqrt format {} (source 1 25 4) (2 : Rat)
  let negativeRoots := Formats.P3109.Block.BlockSqrt format {} (source 1 25 4) (-2 : Rat)
  let reciprocal := Formats.P3109.Block.BlockRSqrt format {} (source 1 4 16) (1 / 2 : Rat)
  let norms := Formats.P3109.Block.BlockHypot format {} (source 1 3 5) (source 1 4 12) (2 : Rat)
  let directed := Formats.P3109.Block.BlockSqrt small ⟨.scalar .up, .none⟩
    (source 1 2 2) (-2 : Rat)
  countFailures
    [ decide (roots.values.map Mixed.decode = pair (.finite (5 / 2)) (.finite 1))
    , decide (negativeRoots.values.map Mixed.decode = pair (.finite (-5 / 2)) (.finite (-1)))
    , decide (reciprocal.values.map Mixed.decode = pair (.finite 1) (.finite (1 / 2)))
    , decide (norms.values.map Mixed.decode = pair (.finite (5 / 2)) (.finite (13 / 2)))
    , decide (directed.values.map Mixed.decode = pair (.finite (-11 / 16)) (.finite (-11 / 16)))
    , decide ((Formats.P3109.Block.BlockSqrt format {} (source 1 0 0) (-2 : Rat)).values.map
        Mixed.decode = pair (.finite 0) (.finite 0))
    , decide (BlockRoot.normalize (.finite 0) (.finite (-1)) = ⟨false, Arithmetic.nan⟩)
    , decide (BlockRoot.normalize (.infinity true) (.infinity false) = ⟨true, .finite 1⟩) ]⟩

/-- Unary block operations under test, with the corresponding scaled operation and exact answers. -/
def unaryCases : List
    ((Formats.P3109.Block Rat Rat Two → Rat → Formats.P3109.Block Rat (NumericalValue Rat) Two) ×
      (Rat → Rat → NumericalValue Rat) × Rat × Rat) :=
  [ (Formats.P3109.Block.BlockConvert exactDestination {},
      Mixed.ScaledConvert exactDestination, 1, -3)
  , (Formats.P3109.Block.BlockAbs exactDestination {}, Mixed.ScaledAbs exactDestination, 1, 3)
  , (Formats.P3109.Block.BlockNegate exactDestination {},
      Mixed.ScaledNegate exactDestination, -1, 3)
  , (Formats.P3109.Block.BlockRecip exactDestination {}, Mixed.ScaledRecip exactDestination,
      1, -1 / 3) ]

/-- Binary block and scaled operations, evaluated at exact decoded operands `(1,2)` and
`(-3,-1)`. -/
def binaryCases : List
    ((Formats.P3109.Block Rat Rat Two → Formats.P3109.Block Rat Rat Two → Rat →
        Formats.P3109.Block Rat (NumericalValue Rat) Two) ×
      (Rat → Rat → Rat → Rat → NumericalValue Rat) × Rat × Rat) :=
  [ (Formats.P3109.Block.BlockCopySign exactDestination {},
      Mixed.ScaledCopySign exactDestination, 1, -3)
  , (Formats.P3109.Block.BlockAdd exactDestination {}, Mixed.ScaledAdd exactDestination, 3, -4)
  , (Formats.P3109.Block.BlockSubtract exactDestination {},
      Mixed.ScaledSubtract exactDestination, -1, -2)
  , (Formats.P3109.Block.BlockMultiply exactDestination {},
      Mixed.ScaledMultiply exactDestination, 2, 3)
  , (Formats.P3109.Block.BlockDivide exactDestination {},
      Mixed.ScaledDivide exactDestination, 1 / 2, 3)
  , (Formats.P3109.Block.BlockMinimum exactDestination {},
      Mixed.ScaledMinimum exactDestination, 1, -3)
  , (Formats.P3109.Block.BlockMaximum exactDestination {},
      Mixed.ScaledMaximum exactDestination, 2, -1)
  , (Formats.P3109.Block.BlockMinimumNumber exactDestination {},
      Mixed.ScaledMinimumNumber exactDestination, 1, -3)
  , (Formats.P3109.Block.BlockMaximumNumber exactDestination {},
      Mixed.ScaledMaximumNumber exactDestination, 2, -1)
  , (Formats.P3109.Block.BlockMinimumMagnitude exactDestination {},
      Mixed.ScaledMinimumMagnitude exactDestination, 1, -1)
  , (Formats.P3109.Block.BlockMaximumMagnitude exactDestination {},
      Mixed.ScaledMaximumMagnitude exactDestination, 2, -3)
  , (Formats.P3109.Block.BlockMinimumMagnitudeNumber exactDestination {},
      Mixed.ScaledMinimumMagnitudeNumber exactDestination, 1, -1)
  , (Formats.P3109.Block.BlockMaximumMagnitudeNumber exactDestination {},
      Mixed.ScaledMaximumMagnitudeNumber exactDestination, 2, -3)
  , (Formats.P3109.Block.BlockMinimumFinite exactDestination {},
      Mixed.ScaledMinimumFinite exactDestination, 1, -3)
  , (Formats.P3109.Block.BlockMaximumFinite exactDestination {},
      Mixed.ScaledMaximumFinite exactDestination, 2, -1) ]

/-- Every named exact unary/binary operation is checked on positive and negative independent
scales. -/
def namedFailures : Thunk Nat := ⟨fun _ =>
  let left := source 2 (1 / 2) (-3 / 2)
  let right := source 3 (2 / 3) (-1 / 3)
  let unaryCount := countWhereFailures unaryCases fun (blockOp, scaledOp, x, y) =>
    decide ((blockOp left 2).values = pair (.finite (x / 2)) (.finite (y / 2))) &&
    decide (scaledOp 2 (1 / 2) = .finite x) &&
    decide (scaledOp 2 (-3 / 2) = .finite y)
  let binaryCount := countWhereFailures binaryCases fun (blockOp, scaledOp, x, y) =>
    decide ((blockOp left right 2).values = pair (.finite (x / 2)) (.finite (y / 2))) &&
    decide (scaledOp 2 (1 / 2) 3 (2 / 3) = .finite x) &&
    decide (scaledOp 2 (-3 / 2) 3 (-1 / 3) = .finite y)
  unaryCount + binaryCount + countFailures
    [ decide ((Formats.P3109.Block.BlockFMA exactDestination {} left right (source 1 1 1)
        (2 : Rat)).values = pair (.finite (3 / 2)) (.finite 2))
    , decide ((Formats.P3109.Block.BlockFAA exactDestination {} left right (source 1 1 1)
        (2 : Rat)).values = pair (.finite 2) (.finite (-3 / 2)))
    , decide ((Formats.P3109.Block.BlockClamp exactDestination {} left
        (source 1 (-2) (-2)) (source 1 2 2) (2 : Rat)).values =
        pair (.finite (1 / 2)) (.finite (-1)))
    , decide (Mixed.ScaledFMA exactDestination (2 : Rat) (1 / 2 : Rat)
        (3 : Rat) (2 / 3 : Rat) (4 : Rat) (1 / 4 : Rat) = .finite 3)
    , decide (Mixed.ScaledFAA exactDestination (2 : Rat) (1 / 2 : Rat)
        (3 : Rat) (2 / 3 : Rat) (4 : Rat) (1 / 4 : Rat) = .finite 4)
    , decide (Mixed.ScaledClamp exactDestination (2 : Rat) (-3 / 2 : Rat)
        (3 : Rat) (-2 / 3 : Rat) (4 : Rat) (1 / 2 : Rat) = .finite (-2))
    , decide (Mixed.decode (Mixed.ScaledSqrt .binary8p4se (4 : Rat) (1 : Rat)) = .finite 2)
    , decide (Mixed.decode (Mixed.ScaledRSqrt .binary8p4se (4 : Rat) (1 : Rat)) = .finite (1 / 2))
    , decide (Mixed.decode (Mixed.ScaledHypot .binary8p4se (3 : Rat) (1 : Rat)
        (2 : Rat) (2 : Rat)) = .finite 5) ]⟩

/-- Mixed encoded source descriptors remain independent even in a scaled ternary expression. -/
def specialFailures : Thunk Nat := ⟨fun _ =>
  let a : ExecFloat.P3109 .binary8p4se := 2
  let b : ExecFloat.P3109 (Format.signed 5 2 .extended) := 3
  let inf : ExecFloat.P3109 .binary8p4se := ExecFloat.P3109.positiveInfinity
  let sourceNaN : ExecFloat.P3109 .binary8p4se := ExecFloat.P3109.nan
  let nan : NumericalValue Rat := Arithmetic.nan
  countFailures
    [ decide (Mixed.ScaledFMA exactDestination (1 : Rat) a (1 : Rat) b
        (1 : Rat) (1 : Rat) = .finite 7)
    , decide (Mixed.ScaledMultiply exactDestination (0 : Rat) inf (1 : Rat) (2 : Rat) = nan)
    , decide (Mixed.ScaledAbs exactDestination sourceNaN (0 : Rat) = nan)
    , decide (Mixed.ScaledDivide exactDestination (1 : Rat) inf (0 : Rat) (1 : Rat) = nan)
    , decide (Mixed.ScaledMinimumNumber exactDestination (1 : Rat) sourceNaN
        (1 : Rat) (2 : Rat) = .finite 2)
    , decide (Mixed.ScaledMaximumFinite exactDestination (1 : Rat) inf
        (1 : Rat) (-2 : Rat) = .finite (-2))
    , decide (Mixed.ScaledClamp exactDestination (1 : Rat) (1 : Rat)
        (1 : Rat) (2 : Rat) (1 : Rat) (-2 : Rat) = nan)
    , decide (Mixed.decode (Mixed.ScaledSqrt .binary8p4se (0 : Rat) inf) = nan)
    , decide (Mixed.decode (Mixed.ScaledRSqrt .binary8p4se (1 : Rat) (0 : Rat)) = nan) ]⟩

/-! The named functions inherit the arity proofs at every result descriptor and scale. -/

example (format : Format) {length : ℕ+} (policy : BlockPolicy length)
    (x : Formats.P3109.Block Rat Rat length) (scale q : Rat) (i : Fin (length : Nat))
    (hs : scale ≠ 0) (hq : (Formats.P3109.Block.decode x)[i.val] = .finite q)
    (hq0 : 0 ≤ q) :
    Format.SameDatum
      (ExecFloat.P3109.decode (Formats.P3109.Block.BlockSqrt format policy x scale).values[i.val])
      (ComparisonRounding.reportValue format (policy.at i)
        (Real.sqrt (q : ℝ) / (scale : ℝ))) :=
  Formats.P3109.Block.decode_projectRoots_report format policy scale
    (Formats.P3109.Block.decode x) i scale q rfl hs hq hq0

example (format : Format) (policy : BlockPolicy Two) (x : Formats.P3109.Block Rat Rat Two)
    (scale : Rat) (i : Fin 2) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (Formats.P3109.Block.BlockAbs (Destination.p3109 format) policy x scale).values[i.val])
      (format.projectRatValue (policy.at i)
        (Formats.P3109.Block.normalize (.finite scale)
          (Arithmetic.Abs (Formats.P3109.Block.decode x)[i.val]))) :=
  Formats.P3109.Block.decode_unary_lane format policy Arithmetic.Abs x scale i

example (format : Format) (policy : BlockPolicy Two) (x y : Formats.P3109.Block Rat Rat Two)
    (scale : Rat) (i : Fin 2) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (Formats.P3109.Block.BlockAdd (Destination.p3109 format) policy x y scale).values[i.val])
      (format.projectRatValue (policy.at i)
        (Formats.P3109.Block.normalize (.finite scale)
          (Arithmetic.Add (Formats.P3109.Block.decode x)[i.val]
            (Formats.P3109.Block.decode y)[i.val]))) :=
  Formats.P3109.Block.decode_binary_lane format policy Arithmetic.Add x y scale i

example (format : Format) (policy : BlockPolicy Two) (x y z : Formats.P3109.Block Rat Rat Two)
    (scale : Rat) (i : Fin 2) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (Formats.P3109.Block.BlockFMA (Destination.p3109 format) policy x y z scale).values[i.val])
      (format.projectRatValue (policy.at i)
        (Formats.P3109.Block.normalize (.finite scale)
          (Arithmetic.FMA (Formats.P3109.Block.decode x)[i.val]
            (Formats.P3109.Block.decode y)[i.val] (Formats.P3109.Block.decode z)[i.val]))) :=
  Formats.P3109.Block.decode_ternary_lane format policy Arithmetic.FMA x y z scale i

example (format : Format) (s x : Rat) (mode : Formats.P3109.RoundingMode) (sat : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode (Mixed.ScaledAbs (Destination.p3109 format) s x mode sat))
      (format.projectRatValue ⟨mode, sat⟩ (Arithmetic.Abs (.finite (s * x)))) :=
  Mixed.decode_scaledUnary format Arithmetic.Abs s x mode sat

example (format : Format) (s x t y u z : Rat)
    (mode : Formats.P3109.RoundingMode) (sat : SaturationMode) :
    Format.SameDatum
      (ExecFloat.P3109.decode (Mixed.ScaledFMA (Destination.p3109 format) s x t y u z mode sat))
      (format.projectRatValue ⟨mode, sat⟩ (.finite ((s * x) * (t * y) + u * z))) :=
  Mixed.decode_scaledTernary format Arithmetic.FMA s x t y u z mode sat

example (s x : Rat) :
    Mixed.ScaledAbs exactDestination s x =
      Arithmetic.Divide (Arithmetic.Abs (.finite (s * x))) (.finite 1) :=
  Mixed.scaledUnary_eq_project_div_one exactDestination Arithmetic.Abs
    (by intro value; cases value <;> rfl) s x .nearest .none

example (s x t y u z : Rat) :
    Mixed.ScaledFMA exactDestination s x t y u z =
      Arithmetic.Divide (.finite ((s * x) * (t * y) + u * z)) (.finite 1) :=
  Mixed.scaledTernary_eq_project_div_one exactDestination Arithmetic.FMA
    (fun _ _ _ => Mixed.canonical_add _ _) s x t y u z .nearest .none

/-! ## The general block format with P3109 codecs

The general quantizer with the largest-magnitude rule and target `1` stores the words of the
conversion of §5.5.3, on these two blocks. `Block.convertTo_lane` proves the element rule for
every block with a finite nonzero scale. -/

/-- The general block quantizer on two lanes of `binary8p4se` with a `binary8p4se` scale. -/
def general (left right : Rat) :=
  (Formats.P3109.Block.format .binary8p4se .binary8p4se Two).quantize
    [Formats.Block.Selection.ofMax (fun _ => ()) 1 0]
    (fun lane => SignedRat.ofRat (pair left right)[lane.val])

/-- The report's conversion with a selected scale, on the same lanes. -/
def selected (left right : Rat) :=
  Formats.P3109.Block.ConvertToBlockMaxAbsFinite (Destination.p3109 .binary8p4se)
    (Destination.p3109 .binary8p4se) {} {} (pair left right)

example : ((general (-3) 1).scales.1 ()).toCode = (selected (-3) 1).scale.toCode ∧
    ∀ lane : Fin 2, ((general (-3) 1).elements lane).toCode =
      ((selected (-3) 1).values[lane.val]).toCode := by
  decide +kernel

example : ((general (1 / 3) (7 / 5)).scales.1 ()).toCode =
      (selected (1 / 3) (7 / 5)).scale.toCode ∧
    ∀ lane : Fin 2, ((general (1 / 3) (7 / 5)).elements lane).toCode =
      ((selected (1 / 3) (7 / 5)).values[lane.val]).toCode := by
  decide +kernel

/-- Non-transcendental P3109 block regression failure count. -/
def totalFailures : Thunk Nat := ⟨fun _ =>
  arithmeticFailures.get + stochasticFailures.get + rootFailures.get +
    namedFailures.get + specialFailures.get⟩

/-- Report the chapter 5 block checks in the core executable suite. -/
def report : Thunk ReportSection := ⟨fun _ =>
  let failures := totalFailures.get
  { title := "P3109 block operations"
    body := s!"TOTAL: {failures}"
    failures }⟩

end FloatLibTests.Conformance.P3109.Block
