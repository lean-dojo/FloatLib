/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.NumericalSystem
public import FloatLib.Floats.Formats.BinaryInterchange.Info.Profile
public meta import FloatLib.Floats.Formats.BinaryInterchange.Info.Command

/-!
# Proof-aware inspection of binary complex values

This module registers `ExecComplex fmt` with `#float_info`. The report describes its component
format, sign operations, arithmetic, squared magnitude, and scaled magnitude. It links the
operation theorems and lists their finite-intermediate hypotheses. The rounded operations are
not identified with exact complex field operations, and no scalar conversion policy is installed.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.FloatInfo

open FloatLib.Floats.ExecFloat

/-- Descriptor summary reused by the complex-format inspection report. -/
meta abbrev BinarySummary :=
  FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.Summary

/-- Build the execution and proof profile for two-component binary complex values. -/
meta def profile (summary : BinarySummary) : FormatProfile where
  family := "binary-interchange complex"
  standard :=
    "Cartesian complex carrier over " ++
      FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.standardName summary
  declarationPrefix := "FloatLib.Floats.Formats.BinaryInterchange.ExecComplex."
  representation :=
    [ ⟨"storage", "two binary `Model` components in Cartesian form"⟩
    , ⟨"component bits", toString summary.bitWidth⟩
    , ⟨"combined component payload", s!"{2 * summary.bitWidth} bits"⟩
    , ⟨"component exponent bits", toString summary.expWidth⟩
    , ⟨"component fraction bits", toString summary.fracWidth⟩
    , ⟨"component encoding",
        FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.encodingName summary.encoding⟩
    ]
  values :=
    [ ⟨"finite complex values",
        "yes; both components must be finite and denote the corresponding real coordinates"⟩
    , ⟨"signed zeros",
        "retained independently in each component when the component format supports them"⟩
    , ⟨"infinity", "available independently in either component when the component format has it"⟩
    , ⟨"NaN", "available independently in either component when the component format has it"⟩
    ]
  rounding :=
    [ ⟨"negation / conjugation", "exact on finite components under the format's zero conventions"⟩
    , ⟨"addition / subtraction", "each real and imaginary component is rounded once"⟩
    , ⟨"multiplication",
        "four rounded products followed by one rounded subtraction and one rounded addition"⟩
    , ⟨"division", "nine scalar rounding sites in the selected component-ratio branch"⟩
    , ⟨"squared magnitude", "two rounded squares followed by a rounded sum"⟩
    , ⟨"magnitude", "scale, round two ratios, square and sum, round sqrt, then round rescaling"⟩
    ]
  execution :=
    [ ⟨"carrier", "a direct pair of format-generic binary model values"⟩
    , ⟨"dispatch", "monomorphic composition of the component format's executable kernels"⟩
    , ⟨"multiplication order",
        "real = round(round(ac) - round(bd)); imaginary = round(round(ad) + round(bc))"⟩
    , ⟨"division pivot",
        "larger denominator component by magnitude; imaginary pivot exchanges coordinates and conjugates the result"⟩
    , ⟨"magnitude exceptions",
        "infinity takes priority over quiet NaN; signaling NaNs retain scalar addition's selection and quieting policy"⟩
    , ⟨"magnitude intermediate range",
        "normalized ratios, squares, and sum must fit; a custom bias can make the sum overflow even when the exact norm fits"⟩
    ]
  specializedOperations :=
    [ ⟨"negation / conjugation", "exact for finite inputs; theorem-linked complex semantics"⟩
    , ⟨"addition / subtraction",
        "componentwise rounded semantics with explicit finite-result hypotheses"⟩
    , ⟨"multiplication",
        "six visible scalar rounding sites with a checked evaluation-order refinement theorem"⟩
    , ⟨"division",
        "ratio formula with finite-intermediate and nonzero-pivot/denominator conditions"⟩
    , ⟨"squared magnitude / magnitude",
        "real-valued scalar results with checked rounded expressions and numerical automation"⟩
    ]
  theoremSurfaces :=
    [ { topic := "finite complex representation"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.isFinite_eq_true_iff
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.numericalSystem_represents_of_isFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.represents_iff
          ]
        definitions := [``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.numericalSystem]
        applicability := .verifiedForType
        scope :=
          "both components are finite; a NaN or infinite component gives undefined denotation" }
    , { topic := "exact complex sign transformations"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.toComplex_neg
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.toComplex_conj
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.neg_refines
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.conj_refines
          ]
        applicability := .verifiedForType
        scope := "finite real and imaginary components"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "The results equal exact complex negation and conjugation on finite inputs." } }
    , { topic := "rounded addition and subtraction"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.toComplex_add_eq_roundedAdd
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.toComplex_sub_eq_roundedSub
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.add_refines
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.sub_refines
          ]
        definitions :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.roundedAdd
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.roundedSub
          ]
        applicability :=
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.ieeeApplicability summary
        scope := "finite inputs and finite componentwise output"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Each output component is one nearest-even rounding of the corresponding exact component sum or difference." } }
    , { topic := "non-fused rounded multiplication"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.toComplex_mul_eq_roundedMul
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.mul_refines
          ]
        definitions :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.MulFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.roundedMul
          ]
        applicability :=
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.ieeeApplicability summary
        scope :=
          "finite inputs, four finite rounded component products, and finite final components"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "The theorem fixes the six visible scalar rounding sites and their evaluation order; no smaller whole-complex error bound is inferred." } }
    , { topic := "rounded ratio division"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.toComplex_div_eq_roundedDiv
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.isFinite_div
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.div_refines
          ]
        definitions :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.DivFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.Internal.DivBranchFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.roundedDiv
          ]
        applicability :=
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.ieeeApplicability summary
        scope :=
          "finite inputs, all selected-branch intermediates and outputs finite, pivot and rounded denominator nonzero"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "The selected ratio expression has nine scalar rounding sites; an imaginary pivot adds exact final conjugation. Intermediate overflow is still possible." } }
    , { topic := "rounded squared magnitude"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.toReal_normSq_eq_roundedNormSq
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.normSq_refines
          ]
        definitions :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.NormSqFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.roundedNormSq
          ]
        applicability :=
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.ieeeApplicability summary
        scope := "finite inputs, both rounded squares finite, and their rounded sum finite"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "The scalar result is round(round(re*re) + round(im*im)); no exact squared norm or whole-operation error bound is claimed." } }
    , { topic := "rounded scaled magnitude"
        declarations :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.toReal_magnitude_eq_roundedMagnitude
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.magnitude_refines
          ]
        definitions :=
          [ ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.MagnitudeFinite
          , ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.roundedMagnitude
          ]
        applicability :=
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.ieeeApplicability summary
        scope :=
          "finite input and output; for nonzero scale, finite ratios, squares and sum, and a zero or nonnegative-sign square-root input"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "The scale is max(abs(re),abs(im)); the nonzero branch records seven scalar rounding sites. Zero scale returns zero. Correct rounding of the exact norm is not inferred." } }
    ]
  nonclaims :=
    [ "the six-rounding multiplication is equal to exact multiplication in `ℂ`"
    , "ratio division is overflow-free or agrees with exact complex division"
    , "squared magnitude or magnitude is correctly rounded from the exact norm"
    , "scaled magnitude avoids intermediate overflow for every custom descriptor"
    , "complex square root, fused complex multiplication, or transcendental operations are installed"
    , "a scalar `ExactDecoder` or destination `Quantizer` preserves all componentwise exceptional metadata"
    , "compiled BLAS, SIMD, GPU, or host complex arithmetic is equivalent to this evaluation order"
    ]

end FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.FloatInfo

namespace FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some arguments ←
            unfoldUntilAppArgs?
              ``FloatLib.Floats.Formats.BinaryInterchange.ExecComplex 1 typeExpr
          | throwUnsupportedSyntax
        let summary ←
          FloatLib.Floats.Formats.BinaryInterchange.FloatInfo.inspectSummary arguments[0]!
        logInfoAt tk <| ←
          Inspection.renderProfile
            (FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.FloatInfo.profile summary)
            typeExpr
            .none

end FloatLib.Floats.Formats.BinaryInterchange.ExecComplex.FloatInfo.Command
