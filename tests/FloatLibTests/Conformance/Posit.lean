/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Certificate
public import FloatLib.Floats.Formats.Posit
public import FloatLibTests.Accounting
public import FloatLibTests.Conformance.Posit.ExecutionBoundaries
public import FloatLibTests.Conformance.Posit.Quire

/-!
# Posit Standard conformance gates

This module checks the current, width-only Posit Standard surface. It does not contain a historical
`posit(n, es)` mode or a second posit family.

The general theorem below checks that every configured posit width exposes the common six-operation
`ExecFloat` refinement certificate. Closed checks exhaust every encoded word at widths 2 through
8: ordinary values decode to an exact rational and round back to the same word. Separate checks
cover the NaR word, standard extrema, basic functions, and backend selection.

The standard formulas also imply that an eight-bit posit has
`minPos = 2⁻²⁴`, `maxPos = 2²⁴`, and encodes one as `0x40`. These are checked against the
executable decoder and rounding implementation rather than duplicated as a lookup table.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 3--5, <https://posithub.org/docs/posit_standard-2.pdf>.
* John L. Gustafson, *Standard Posit Arithmetic*, Supercomputing Frontiers and Innovations 9(1),
  2022, <https://doi.org/10.14529/jsfi220102>.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Posit

open FloatLib.Floats
open FloatLib.Floats.Formats.Posit
open FloatLibTests.Accounting

/-! ## Arbitrary-width public refinement -/

/--
Every statically configured standard posit receives the complete universal arithmetic
certificate, independently of whether its carrier is a byte, machine word, or exact-width model.
-/
theorem all_operations_refine
    (format : Format) (plan : Configured.StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Configured.Family format code plan)] :
    FloatLib.Floats.ExecFloat.Proof.FullArithmeticCertificate
      (Configured.Family format code plan) :=
  FloatLib.Floats.ExecFloat.Proof.fullArithmeticCertificate
    (Configured.Family format code plan)

/-! ## Exhaustive tiny-format representation checks -/

/-- Exact descriptor for the smallest standard posit width. -/
abbrev posit2Format : Format :=
  FloatLib.Floats.ExecFloat.Posit.format 2

/--
Check one encoded word against the exact decode-then-round law.

NaR has no rational value and is checked as its own value class. Every other word must decode to a
rational and round back to precisely the same encoding.
-/
def roundTripAt (format : Format) (bits : Nat) : Bool :=
  let value := Model.ofNatBits (format := format) bits
  if value.isNaR then
    true
  else
    match value.toRat? with
    | some rational => Model.roundRat format rational == value
    | none => false

/-- Number of decode-then-round failures over every word of a closed descriptor. -/
def roundTripFailures (format : Format) : Nat :=
  countWhereFailures (List.range format.modulus) (roundTripAt format)

/--
Every posit word at widths 2 through 8 satisfies the exact representation round trip, with NaR
handled separately.

Each theorem is reduced by the ordinary `decide` tactic in the trusted kernel; these are not
external test assertions, native-code oracles, or admitted facts.
-/
theorem posit2_all_words_round_trip :
    roundTripFailures posit2Format = 0 := by
  decide +kernel

theorem posit3_all_words_round_trip :
    roundTripFailures (FloatLib.Floats.ExecFloat.Posit.format 3) = 0 := by
  decide +kernel

theorem posit4_all_words_round_trip :
    roundTripFailures (FloatLib.Floats.ExecFloat.Posit.format 4) = 0 := by
  decide +kernel

theorem posit5_all_words_round_trip :
    roundTripFailures (FloatLib.Floats.ExecFloat.Posit.format 5) = 0 := by
  decide +kernel

theorem posit6_all_words_round_trip :
    roundTripFailures (FloatLib.Floats.ExecFloat.Posit.format 6) = 0 := by
  decide +kernel

theorem posit7_all_words_round_trip :
    roundTripFailures (FloatLib.Floats.ExecFloat.Posit.format 7) = 0 := by
  decide +kernel

theorem posit8_all_words_round_trip :
    roundTripFailures (FloatLib.Floats.ExecFloat.Posit.format 8) = 0 := by
  decide +kernel

/-! ## Standard extrema and canonical words -/

/-- The two-bit edge format represents exactly zero, one, NaR, and negative one. -/
theorem posit2_standard_words :
    List.map
      (fun bits =>
        Model.decode (Model.ofNatBits (format := posit2Format) bits))
      (List.range posit2Format.modulus) =
      [ .finite 0
      , .finite 1
      , .exceptional .notAReal
      , .finite (-1)
      ] := by
  decide +kernel

/-- Exact descriptor used by the standard posit8 examples. -/
abbrev posit8Format : Format :=
  FloatLib.Floats.ExecFloat.Posit.format 8

/-- The eight-bit minimum positive value is the standard `2⁻²⁴`. -/
theorem posit8_minPos :
    Model.minPositiveRat posit8Format = (1 : Rat) / 16777216 := by
  decide +kernel

/-- The eight-bit maximum positive value is the standard `2²⁴`. -/
theorem posit8_maxPos :
    Model.nonnegativeRatAt posit8Format (posit8Format.signMaskNat - 1) =
      (16777216 : Rat) := by
  decide +kernel

/-- The sixteen-bit extrema follow the standard width-only formula `2^(±(4n - 8))`. -/
theorem posit16_extrema :
    let format := FloatLib.Floats.ExecFloat.Posit.format 16
    Model.minPositiveRat format = (1 : Rat) / 72057594037927936 ∧
      Model.nonnegativeRatAt format (format.signMaskNat - 1) =
        (72057594037927936 : Rat) := by
  decide +kernel

/-- The thirty-two-bit extrema follow the same standard formula without a format-specific table. -/
theorem posit32_extrema :
    let format := FloatLib.Floats.ExecFloat.Posit.format 32
    Model.minPositiveRat format =
        (1 : Rat) / 1329227995784915872903807060280344576 ∧
      Model.nonnegativeRatAt format (format.signMaskNat - 1) =
        (1329227995784915872903807060280344576 : Rat) := by
  decide +kernel

/-- Exact one has the canonical posit8 word `0x40`. -/
theorem posit8_one_word :
    (Model.roundRat posit8Format 1).toNatBits = 0x40 := by
  decide +kernel

/-- Exact negative one is whole-word two's complement of the one word. -/
theorem posit8_negative_one_word :
    (Model.roundRat posit8Format (-1)).toNatBits = 0xc0 := by
  decide +kernel

/-- The posit8 NaR word is the unique sign-mask word `0x80`. -/
theorem posit8_nar_word :
    (Model.nar posit8Format).toNatBits = 0x80 := by
  decide +kernel

/--
The standard encoded comparison makes NaR equal to itself and strictly less than every real
posit8 value, including the zero word.
-/
theorem posit8_nar_comparison :
    Model.compareEqual (Model.nar posit8Format) (Model.nar posit8Format) = true ∧
      Model.compareLess (Model.nar posit8Format) (Model.zero posit8Format) = true := by
  decide +kernel

/-! ## Current-standard basic functions -/

/--
The representation successor and predecessor adjacent to zero are the signed minimum-positive
values. Their general mutual-inverse laws are proved in `Model.prior_next` and `Model.next_prior`.
-/
theorem posit8_next_prior_zero_words :
    (Model.next (Model.zero posit8Format)).toNatBits = 0x01 ∧
      (Model.prior (Model.zero posit8Format)).toNatBits = 0xff := by
  decide +kernel

/-- The sign function returns exact `±1`, zero, and NaR for the four semantic cases. -/
theorem posit8_sign_cases :
    List.map Model.decode
      [ Model.sign (Model.roundRat posit8Format 7)
      , Model.sign (Model.roundRat posit8Format (-7))
      , Model.sign (Model.zero posit8Format)
      , Model.sign (Model.nar posit8Format)
      ] =
      [ .finite 1
      , .finite (-1)
      , .finite 0
      , .exceptional .notAReal
      ] := by
  decide +kernel

/-- Absolute value is numerical on ordinary values and propagates the distinguished NaR word. -/
theorem posit8_abs_cases :
    List.map Model.decode
      [ Model.abs (Model.roundRat posit8Format 7)
      , Model.abs (Model.roundRat posit8Format (-7))
      , Model.abs (Model.zero posit8Format)
      , Model.abs (Model.nar posit8Format)
      ] =
      [ .finite 7
      , .finite 7
      , .finite 0
      , .exceptional .notAReal
      ] := by
  decide +kernel

/--
The rational-free square-root kernel returns exact ordinary results for perfect squares and
propagates the standard NaR result for a negative radicand.

This exercises the dedicated dyadic implementation, not merely the reference rational
specification to which it is proved equal.
-/
theorem posit8_dyadic_sqrt_cases :
    List.map Model.decode
      [ Model.DyadicArithmetic.sqrt (Model.zero posit8Format)
      , Model.DyadicArithmetic.sqrt (Model.roundRat posit8Format 1)
      , Model.DyadicArithmetic.sqrt (Model.roundRat posit8Format 4)
      , Model.DyadicArithmetic.sqrt (Model.roundRat posit8Format (-1))
      , Model.DyadicArithmetic.sqrt (Model.nar posit8Format)
      ] =
      [ .finite 0
      , .finite 1
      , .finite 2
      , .exceptional .notAReal
      , .exceptional .notAReal
      ] := by
  decide +kernel

/--
The rational-free division kernel returns exact signed results and the standard NaR result for
zero divisors and exceptional operands.

This exercises cross-multiplied quotient rounding directly rather than the rational reference.
-/
theorem posit8_dyadic_div_cases :
    List.map Model.decode
      [ Model.DyadicArithmetic.div
          (Model.roundRat posit8Format 6) (Model.roundRat posit8Format 3)
      , Model.DyadicArithmetic.div
          (Model.roundRat posit8Format (-6)) (Model.roundRat posit8Format 3)
      , Model.DyadicArithmetic.div
          (Model.roundRat posit8Format 6) (Model.roundRat posit8Format (-3))
      , Model.DyadicArithmetic.div
          (Model.zero posit8Format) (Model.roundRat posit8Format 3)
      , Model.DyadicArithmetic.div
          (Model.roundRat posit8Format 6) (Model.zero posit8Format)
      , Model.DyadicArithmetic.div
          (Model.nar posit8Format) (Model.roundRat posit8Format 3)
      ] =
      [ .finite 2
      , .finite (-2)
      , .finite (-2)
      , .finite 0
      , .exceptional .notAReal
      , .exceptional .notAReal
      ] := by
  decide +kernel

/-- Positive and negative half-integers distinguish nearest-even, ceiling, and floor. -/
example :
    ([-2.5, -1.5, -0.5, 0.5, 1.5, 2.5].map fun (value : ExecFloat.Posit (bits := 8)) =>
      (ExecFloat.Posit.toRat? (ExecFloat.Posit.nearestInt value),
       ExecFloat.Posit.toRat? (ExecFloat.Posit.ceil value),
       ExecFloat.Posit.toRat? (ExecFloat.Posit.floor value))) =
      [ (some (-2), some (-2), some (-3))
      , (some (-2), some (-1), some (-2))
      , (some 0, some 0, some (-1))
      , (some 0, some 1, some 0)
      , (some 2, some 2, some 1)
      , (some 2, some 3, some 2) ] := by
  decide +kernel

/-! ## Closed automatic-dispatch checks -/

/--
The balanced policy selects complete encoded-value tables for posit4 unary and binary operations.

The direct packed-word FMA is faster than the generic ternary table lookup even though the
4,096-byte table satisfies the default resident-memory bound.
-/
theorem posit4_balanced_backend_kinds :
    [ (FloatLib.Floats.ExecFloat.Add.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 4)).kind
    , (FloatLib.Floats.ExecFloat.Sub.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 4)).kind
    , (FloatLib.Floats.ExecFloat.Mul.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 4)).kind
    , (FloatLib.Floats.ExecFloat.Div.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 4)).kind
    , (FloatLib.Floats.ExecFloat.Sqrt.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 4)).kind
    , (FloatLib.Floats.ExecFloat.Fma.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 4)).kind
    ] =
      [ .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      , .exhaustiveTable, .exhaustiveTable
      , .custom "direct packed-word kernel" 0
      ] := by
  decide +kernel

/--
For posit6, balanced planning selects all unary and binary tables. Its 262,144-byte FMA table is
admissible but does not amortize over the balanced workload, so FMA uses the certified
direct packed-word kernel.
-/
theorem posit6_balanced_backend_kinds :
    [ (FloatLib.Floats.ExecFloat.Add.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 6)).kind
    , (FloatLib.Floats.ExecFloat.Sub.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 6)).kind
    , (FloatLib.Floats.ExecFloat.Mul.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 6)).kind
    , (FloatLib.Floats.ExecFloat.Div.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 6)).kind
    , (FloatLib.Floats.ExecFloat.Sqrt.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 6)).kind
    , (FloatLib.Floats.ExecFloat.Fma.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 6)).kind
    ] =
      [ .exhaustiveTable, .exhaustiveTable, .exhaustiveTable
      , .exhaustiveTable, .exhaustiveTable
      , .custom "direct packed-word kernel" 0
      ] := by
  decide +kernel

/--
At posit8, direct packed execution beats the 65,536-byte binary tables under the balanced policy.
The tiny 256-byte square-root table still amortizes, while the 16,777,216-byte FMA table exceeds
the memory ceiling outright.
-/
theorem posit8_balanced_backend_kinds :
    [ (FloatLib.Floats.ExecFloat.Add.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).kind
    , (FloatLib.Floats.ExecFloat.Sub.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).kind
    , (FloatLib.Floats.ExecFloat.Mul.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).kind
    , (FloatLib.Floats.ExecFloat.Div.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).kind
    , (FloatLib.Floats.ExecFloat.Sqrt.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).kind
    , (FloatLib.Floats.ExecFloat.Fma.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).kind
    ] =
      [ .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .exhaustiveTable
      , .custom "direct packed-word kernel" 0
      ] := by
  decide +kernel

/--
Only the selected posit8 square-root table consumes persistent storage.
-/
theorem posit8_balanced_table_residency :
    [ (FloatLib.Floats.ExecFloat.Add.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).residentBytes
    , (FloatLib.Floats.ExecFloat.Sub.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).residentBytes
    , (FloatLib.Floats.ExecFloat.Mul.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).residentBytes
    , (FloatLib.Floats.ExecFloat.Div.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).residentBytes
    , (FloatLib.Floats.ExecFloat.Sqrt.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).residentBytes
    ] = [0, 0, 0, 0, 256] := by
  decide +kernel

/--
Posit16 selects the certified packed-word tier for all six universal operations. Operands decode
directly from `UInt16`; direct candidates and their neighboring codes stay in `UInt64`; division
uses one scaled integer quotient plus exact cross-products, and square root uses one integer root
plus exact squared comparisons. Every operation restores signs at the code level and packs the
final code directly.
-/
theorem posit16_balanced_backend_kinds :
    [ (FloatLib.Floats.ExecFloat.Add.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 16)).kind
    , (FloatLib.Floats.ExecFloat.Sub.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 16)).kind
    , (FloatLib.Floats.ExecFloat.Mul.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 16)).kind
    , (FloatLib.Floats.ExecFloat.Div.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 16)).kind
    , (FloatLib.Floats.ExecFloat.Sqrt.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 16)).kind
    , (FloatLib.Floats.ExecFloat.Fma.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 16)).kind
    ] =
      [ .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      ] := by
  rfl

/--
Posit32 receives the same certified packed execution tier as posit16. This closed check prevents
the user-visible planner report from silently falling back to representation-independent model
conversion at the most common word width.
-/
theorem posit32_balanced_backend_kinds :
    [ (FloatLib.Floats.ExecFloat.Add.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 32)).kind
    , (FloatLib.Floats.ExecFloat.Sub.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 32)).kind
    , (FloatLib.Floats.ExecFloat.Mul.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 32)).kind
    , (FloatLib.Floats.ExecFloat.Div.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 32)).kind
    , (FloatLib.Floats.ExecFloat.Sqrt.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 32)).kind
    , (FloatLib.Floats.ExecFloat.Fma.selectedCandidate
        (F := FloatLib.Floats.ExecFloat.Posit.Family 32)).kind
    ] =
      [ .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      , .custom "direct packed-word kernel" 0
      ] := by
  rfl

namespace ThroughputPlan

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

/--
For sustained posit6 workloads, the direct packed-word FMA remains faster than the generic
ternary table lookup. The numerical semantics and public `ExecFloat.Posit 6` value type are
unchanged.
-/
theorem posit6_throughput_fma_backend :
    (FloatLib.Floats.ExecFloat.Fma.selectedCandidate
      (F := FloatLib.Floats.ExecFloat.Posit.Family 6)).kind =
        .custom "direct packed-word kernel" 0 := by
  decide +kernel

/--
Throughput planning admits posit8's 16 MiB FMA table to cost comparison, but its construction
still cannot amortize at the five-million-call horizon. It therefore retains the direct
packed-word FMA kernel.
-/
theorem posit8_throughput_fma_backend :
    (FloatLib.Floats.ExecFloat.Fma.selectedCandidate
      (F := FloatLib.Floats.ExecFloat.Posit.Family 8)).kind =
        .custom "direct packed-word kernel" 0 := by
  decide +kernel

end ThroughputPlan

end FloatLibTests.Conformance.Posit
