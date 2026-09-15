/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Info.Profile
public meta import FloatLib.Floats.Formats.BinaryInterchange.Info.Command

/-!
# Proof-aware inspection of executable binary intervals

The `#float_info` registration for `Model.Interval fmt` describes its carrier and proved
enclosure contracts. Interval operations are deliberately reported as an outward-rounded
specialized API, not as scalar `ExecFloat` capabilities. The report distinguishes the raw
two-endpoint carrier from `Interval.Valid`, and it names the exact hypotheses under which each
operation is a proved real or extended-real enclosure.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.FloatInfo

open FloatLib.Floats.ExecFloat

/-- Descriptor summary reused by the interval-format inspection report. -/
meta abbrev BinarySummary :=
  FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.Summary

/-- Build the execution and enclosure-proof profile for a binary endpoint interval. -/
meta def profile (summary : BinarySummary) : FormatProfile where
  family := "binary-interchange closed interval"
  standard :=
    "outward-rounded interval carrier over " ++
      FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.standardName summary
  declarationPrefix := "FloatLib.Floats.Formats.BinaryInterchange.Model.Interval."
  representation :=
    [ ⟨"storage", "one lower and one upper binary `Model` endpoint"⟩
    , ⟨"endpoint payload bits", toString summary.bitWidth⟩
    , ⟨"combined endpoint payload", s!"{2 * summary.bitWidth} bits"⟩
    , ⟨"endpoint exponent bits", toString summary.expWidth⟩
    , ⟨"endpoint fraction bits", toString summary.fracWidth⟩
    , ⟨"endpoint encoding",
        FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.encodingName summary.encoding⟩
    ]
  values :=
    [ ⟨"raw carrier", "every pair of endpoint encodings, including unordered or exceptional pairs"⟩
    , ⟨"valid interval", "both endpoints finite and ordered by the executable numerical order"⟩
    , ⟨"valid extended interval", "ordered non-NaN endpoints; infinities are permitted"⟩
    , ⟨"whole interval",
        "[-∞,+∞] when supported; otherwise the two maximal finite endpoints"⟩
    , ⟨"NaN endpoints",
        "representable when the endpoint format has NaN, but excluded by `Interval.Valid`"⟩
    ]
  rounding :=
    [ ⟨"lower endpoints", "rounded toward negative infinity"⟩
    , ⟨"upper endpoints", "rounded toward positive infinity"⟩
    , ⟨"multiplication / division", "all four endpoint corners contribute to the enclosure"⟩
    , ⟨"division through zero",
        "returns the whole interval because one closed interval cannot represent two rays"⟩
    ]
  execution :=
    [ ⟨"carrier", "a pair of endpoints with precision fixed by their shared format descriptor"⟩
    , ⟨"dispatch", "composes the endpoint format's directed kernels and executable comparisons"⟩
    , ⟨"soundness domain",
        "neg/relu/abs support infinite endpoints; directed arithmetic and sqrt require " ++
        "their stated input and format hypotheses"⟩
    ]
  specializedOperations :=
    [ ⟨"point / hull / whole",
        "construct degenerate, endpoint-hull, and conservative full-range intervals"⟩
    , ⟨"neg / add / sub",
        "endpoint-reversing negation and outward-rounded additive arithmetic"⟩
    , ⟨"mul / div / inv",
        "four-corner outward arithmetic with conservative zero-denominator handling"⟩
    , ⟨"relu / abs / sqrt",
        "executable activation ranges with checked enclosure theorems"⟩
    ]
  theoremSurfaces :=
    [ { topic := "validity and real/extended-real membership"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.mem_iff
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.realMem_iff
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.eRealMem_iff
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.Valid.lo_isFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.Valid.hi_isFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.Valid.toReal_ordered
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.eRealMem_coe_iff_of_valid
          ]
        applicability := .verifiedForType
        scope := "raw membership is executable; real semantics requires finite ordered endpoints"
        numericalGuarantee? := some {
          kinds := [.range]
          statement :=
            "A valid endpoint pair denotes exactly the closed real interval between its decoded endpoints." } }
    , { topic := "order and point-interval semantics"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.le_iff_leB_eq_true
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.leB_eq_true_iff_toReal_le_of_isFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.le_iff_toReal_le_of_isFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.valid_point_of_isFinite
          ]
        applicability := .verifiedForType
        scope := "finite endpoints for the real-order equivalences"
        numericalGuarantee? := some {
          kinds := [.range, .exactness]
          statement :=
            "Executable endpoint order agrees with real order, and a finite point interval contains exactly its represented value." } }
    , { topic := "outward-rounded arithmetic enclosures"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.add_sound
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.sub_sound
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.mul_sound
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.div_sound
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.inv_sound
          ]
        applicability :=
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.ieeeApplicability summary
        scope :=
          "valid finite input intervals; division uses the whole interval when the denominator contains zero"
        numericalGuarantee? := some {
          kinds := [.range]
          statement :=
            "Outward-rounded add, subtract, multiply, divide, and reciprocal contain every exact real result." } }
    , { topic := "format-generic negation and activation enclosures"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.neg_sound_extended
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.relu_sound_extended
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.abs_sound_extended
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.neg_validExtended
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.relu_validExtended
          , ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.abs_validExtended
          ]
        applicability := .verifiedForType
        scope := "ValidExtended input and a real member interpreted in EReal; every descriptor"
        numericalGuarantee? := some {
          kinds := [.range]
          statement :=
            "Negation, ReLU, and absolute value preserve validity and real-member enclosure, " ++
            "including infinite endpoints." } }
    , { topic := "outward-rounded square-root enclosure"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.sqrt_sound ]
        applicability :=
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.ieeeApplicability summary
        scope :=
          "valid input interval with a nonnegative decoded lower endpoint and a represented real member"
        numericalGuarantee? := some {
          kinds := [.range]
          statement :=
            "The outward-rounded square-root interval contains the exact square root of every represented member." } }
    ]
  nonclaims :=
    [ "every raw endpoint pair is a valid or nonempty mathematical interval"
    , "ordinary scalar `ExecFloat` arithmetic is installed on the interval carrier"
    , "a scalar conversion policy determines whether casts should preserve endpoints, width, or enclosure"
    , "division through zero returns a disconnected interval set; the executable result is one conservative hull"
    , "compiled MPFI, Arb, SIMD, or hardware interval arithmetic is equivalent to these kernels"
    ]

end FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.FloatInfo

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ←
            unfoldUntilAppArgs?
              ``FloatLib.Floats.Formats.BinaryInterchange.Model.Interval 1 typeExpr
          | throwUnsupportedSyntax
        let summary ←
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.inspectSummary arguments[0]!
        logInfoAt tk <| ←
          Inspection.renderProfile
            (FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.FloatInfo.profile summary)
            typeExpr
            .none

end FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.FloatInfo.Command
