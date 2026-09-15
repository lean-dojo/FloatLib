/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Conversion.Runtime
public import FloatLib.Floats.Formats.P3109.Conversion.Proof
public import FloatLib.Floats.Formats.P3109.Conversion.Instances
public import FloatLib.Floats.Formats.P3109.Projection.Direction
public import FloatLib.Floats.Formats.P3109.Arithmetic.Instances
public import FloatLib.Floats.Formats.P3109.Arithmetic.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Proof
public meta import Lean.Elab.Command
public import FloatLib.Floats.ExecFloat.Info

/-!
# Inspection reports for P3109 formats

This optional meta module registers `#float_info` for `ExecFloat.P3109`. The report reads the
closed descriptor and the actual installed arithmetic and conversion capabilities. It describes
P3109 itself rather than exposing the generic codebook carrier used to store its exact-width
codes.
-/

public meta section

namespace FloatLib.Floats.Formats.P3109.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

/-- Recover the P3109 descriptor from its zero-cost codebook carrier. -/
private meta def extractFormat?
    (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (family, arguments) ←
      Inspection.execFamilyApplication?
        ``FloatLib.Floats.ExecFloat.Codebook.Family 3 type
    | return none
  let book := arguments[2]!
  let some codebookArguments ←
      unfoldUntilAppArgs?
        ``FloatLib.Floats.Formats.P3109.Format.codebook 1 book
    | return none
  return some (family, codebookArguments[0]!)

elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        let some (family, format) ← extractFormat? typeExpr
          | throwUnsupportedSyntax
        let bitWidth ←
          Inspection.readNatProjection
            "P3109 descriptor"
            ``FloatLib.Floats.Formats.P3109.Format.bitWidth format
        let precision ←
          Inspection.readNatProjection
            "P3109 descriptor"
            ``FloatLib.Floats.Formats.P3109.Format.precision format
        let trailingBits ←
          Inspection.readNatProjection
            "P3109 descriptor"
            ``FloatLib.Floats.Formats.P3109.Format.trailingBits format
        let exponentBits ←
          Inspection.readNatProjection
            "P3109 descriptor"
            ``FloatLib.Floats.Formats.P3109.Format.exponentBits format
        let exponentBias ←
          Inspection.readNatProjection
            "P3109 descriptor"
            ``FloatLib.Floats.Formats.P3109.Format.exponentBias format
        let signed ←
          Inspection.readFlagProjection "P3109 descriptor"
            ``FloatLib.Floats.Formats.P3109.Format.signedness
            ``FloatLib.Floats.Formats.P3109.Signedness.signed
            ``FloatLib.Floats.Formats.P3109.Signedness.unsigned
            format
        let extended ←
          Inspection.readFlagProjection "P3109 descriptor"
            ``FloatLib.Floats.Formats.P3109.Format.domain
            ``FloatLib.Floats.Formats.P3109.Domain.extended
            ``FloatLib.Floats.Formats.P3109.Domain.finite
            format
        let baseProfile : FormatProfile :=
          {
            family := "P3109 binary floating-point format"
            standard :=
              "IEEE P3109 Interim Report v4.0.3, revision 34f5964 (working-group report)"
            declarationPrefix := "FloatLib.Floats."
            representation :=
              [ ⟨"storage", s!"exact-width BitVec {bitWidth}"⟩
              , ⟨"total bits (K)", toString bitWidth⟩
              , ⟨"precision (P)", toString precision⟩
              , ⟨"signed", yesNo signed⟩
              , ⟨"datum set", if extended then "extended" else "finite"⟩
              , ⟨"exponent bits", toString exponentBits⟩
              , ⟨"stored trailing bits", toString trailingBits⟩
              , ⟨"exponent bias", toString exponentBias⟩
              ]
            values :=
              [ ⟨"finite values", "yes; normal values, zero, and subnormals when P > 1"⟩
              , ⟨"negative finite values", yesNo signed⟩
              , ⟨"zero", "one unsigned zero code"⟩
              , ⟨"positive infinity", yesNo extended⟩
              , ⟨"negative infinity", yesNo (signed && extended)⟩
              , ⟨"NaN", "one descriptor-dependent code"⟩
              ]
            rounding :=
              [ ⟨"projection order", "round to precision, then saturate, then encode"⟩
              , ⟨"deterministic modes",
                  "toward zero, ±infinity, nearest-away, nearest-even, and to-odd"⟩
              , ⟨"stochastic modes", "P3109 stochastic A, B, and C with explicit random bits"⟩
              , ⟨"saturation modes", "finite, propagate, and none"⟩
              , ⟨"default conversion", "nearest-even with no saturation request"⟩
              ]
            execution :=
              [ ⟨"carrier", s!"ExecFloat over a descriptor-indexed BitVec {bitWidth}"⟩
              , ⟨"projection",
                  "direct exact-integer/rational round, saturate, encode path; no host float"⟩
              , ⟨"width policy",
                  "one parameterized implementation; no named-width dispatch branches"⟩
              , ⟨"backend proof",
                  "decoding the executable result matches the exact projected datum"⟩
              ]
            specializedOperations :=
              [ ⟨"project / ofDyadic",
                  "explicit projection from exact dyadic values under a named policy"⟩
              , ⟨"projectRat / ofRat",
                  "single-rounding projection from exact rational values"⟩
              , ⟨"encode?",
                  "checked encoding of an already representable datum; performs no rounding"⟩
              , ⟨"ofFiniteFields?",
                  "checked construction from named P3109 representation fields"⟩
              , ⟨"mixed and scaled operations",
                  "independent source and destination formats, FMA, fused addition, and exact scaling"⟩
              , ⟨"external destinations",
                  "binary16, binary32, and BFloat16 with exact encoding after report projection"⟩
              , ⟨"extrema and queries",
                  "numeric and magnitude extrema, classification, format limits, and neighbors"⟩
              ]
            theoremSurfaces :=
              [ {
                  topic := "exact representation and checked encoding"
                  declarations :=
                    [ ``FloatLib.Floats.ExecFloat.P3109.decode_eq_format_decode
                    , ``FloatLib.Floats.Formats.P3109.Format.encodeDatumNat_decode
                    , ``FloatLib.Floats.Formats.P3109.Format.encode?_decode
                    , ``FloatLib.Floats.Formats.P3109.Format.sameDatum_decode_of_encode?_eq_some
                    ]
                  applicability := .verifiedForType
                  scope := "every code and every successfully checked datum"
                }
              , {
                  topic := "parameterized finite ordering"
                  declarations :=
                    [ ``FloatLib.Floats.Formats.P3109.Format.decodePositiveFinite_strictMono
                  ]
                  applicability := .verifiedForType
                  scope :=
                    "all positive finite code magnitudes, including P = 1 and the " ++
                      "subnormal boundary"
                }
              , {
                  topic := "dyadic and rational projection representation"
                  declarations :=
                    [ ``FloatLib.Floats.ExecFloat.P3109.decode_project
                    , ``FloatLib.Floats.ExecFloat.P3109.decode_projectRat
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_fitsPrecisionGrid
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteRatToPrecision_fitsPrecisionGrid
                    ]
                  applicability := .verifiedForType
                  scope :=
                    "every valid descriptor, rounding mode, saturation mode, and exact input"
                  numericalGuarantee? := some {
                    kinds := [.range]
                    statement :=
                      "The rounded finite value lies on the descriptor's precision grid, and " ++
                      "the encoded code decodes to the value produced by the executable " ++
                      "round-then-saturate kernel. This is a representation theorem about that " ++
                      "kernel; the rounding direction of each mode is a separate claim."
                  }
                }
              , {
                  topic := "deterministic rounding direction of dyadic projection"
                  declarations :=
                    [ ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_toRat_eq_int_mul
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_towardZero
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_towardZero_maximal
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_towardPositive
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_towardPositive_minimal
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_towardNegative
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_towardNegative_maximal
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_nearestTiesToAway_abs_sub_le
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_nearestTiesToAway_tie
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_nearestTiesToEven_abs_sub_le
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_nearestTiesToEven_tie
                    , ``FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_toOdd_abs_sub_lt
                    ]
                  applicability := .verifiedForType
                  scope :=
                    "exact dyadic inputs under the six deterministic rounding modes, before " ++
                    "saturation"
                  numericalGuarantee? := some {
                    kinds := [.rounding]
                    statement :=
                      "towardZero truncates to the nearest grid point of smaller magnitude; " ++
                      "towardPositive and towardNegative select the adjacent grid point on the " ++
                      "requested side; nearestTiesToAway and nearestTiesToEven stay within half " ++
                      "a quantum and resolve exact ties toward larger magnitude, respectively " ++
                      "toward the candidate with an even P3109 code; toOdd stays within one " ++
                      "quantum and, when precision exceeds one, returns an odd significand " ++
                      "when inexact."
                  }
                }
              , {
                  topic := "rational and external precision-rounding formulas"
                  declarations :=
                    [ ``FloatLib.Floats.Formats.P3109.Format.roundFiniteRatToPrecision_toRat
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.External.roundFinite_toRat
                    ]
                  applicability := .verifiedForType
                  scope :=
                    "every rational input and all nine rounding modes, including each supplied " ++
                    "stochastic word; external formats use their declared precision and bias"
                  numericalGuarantee? := some {
                    kinds := [.rounding]
                    statement :=
                      "The executable precision rounder equals the report's mathematical " ++
                      "floor, fractional-part, and nearest-integer formulas. The proofs " ++
                      "include precision-one code parity and exact ties. Direction and " ++
                      "error bounds concern precision rounding before saturation."
                  }
                }
              , {
                  topic := "exact arithmetic before one destination projection"
                  declarations :=
                    [ ``FloatLib.Floats.ExecFloat.P3109.decode_unaryTo
                    , ``FloatLib.Floats.ExecFloat.P3109.decode_binaryTo
                    , ``FloatLib.Floats.ExecFloat.P3109.decode_ternaryTo
                    , ``FloatLib.Floats.ExecFloat.P3109.decode_fmaTo_finite
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.fma_finite_real
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.div_zero
                    ]
                  applicability := .verifiedForType
                  scope :=
                    "exact rational arithmetic, closed-domain special cases, and one supplied " ++
                    "report projection; source and destination P3109 descriptors may differ"
                }
              , {
                  topic := "square-root arithmetic against the exact real root"
                  declarations :=
                    [ ``FloatLib.Floats.Formats.P3109.Arithmetic.sqrtRoundAway_eq_real
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.roundSqrtRatToPrecision_eq_real
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.sqrtValue_eq_real
                    , ``FloatLib.Floats.ExecFloat.P3109.decode_sqrtTo
                    , ``FloatLib.Floats.ExecFloat.P3109.decode_rsqrtTo
                    , ``FloatLib.Floats.ExecFloat.P3109.decode_hypotTo
                    ]
                  applicability := .verifiedForType
                  scope :=
                    "integer threshold comparisons refine the real square root under the " ++
                    "supplied rounding and saturation policies, including exceptional inputs"
                }
              , {
                  topic := "mixed, fused, and scaled arithmetic"
                  declarations :=
                    [ ``FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.faa_eq_project_finite
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.scaledAdd_eq_project_finite
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.scaledMul_eq_project_finite
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.External.project_refines
                    , ``FloatLib.Floats.Formats.P3109.Arithmetic.External.mixed_ternary_refines
                    ]
                  applicability := .verifiedForType
                  scope :=
                    "exact intermediates with one supplied destination projection; external " ++
                    "encoding preserves the projected value without a second rounding"
                }
              , {
                  topic := "classification and adjacent finite values"
                  declarations :=
                    [ ``FloatLib.Floats.Formats.P3109.Format.no_decodePositiveFinite_between
                    , ``FloatLib.Floats.Formats.P3109.Format.no_subnormal_of_precision_eq_one
                    , ``FloatLib.Floats.ExecFloat.P3109.isNormal_or_isSubnormal
                    , ``FloatLib.Floats.ExecFloat.P3109.nextGreaterThan_of_isNaN
                    , ``FloatLib.Floats.ExecFloat.P3109.nextLessThan_of_isNaN
                    ]
                  applicability := .verifiedForType
                  scope :=
                    "descriptor-specific finite classes, adjacent positive codes, and NaN " ++
                    "propagation in neighbor operations"
                }
              , {
                  topic := "ordinary conversion capability"
                  declarations :=
                    [ ``FloatLib.Floats.ExecFloat.P3109.Conversion.implements_run
                    , ``FloatLib.Floats.ExecFloat.P3109.Conversion.sameDatum_decode_run_value
                    ]
                  applicability := .verifiedForType
                  scope :=
                    "all exact-rational finite, infinity, and exceptional observations"
                }
              ]
            nonclaims :=
              [ "the P3109 interim report is an approved IEEE standard"
              , "the operation proofs establish complete report-wide formal certification"
              , "the direct software projection is equivalent to a particular hardware instruction"
              , "P3109's single NaN retains IEEE NaN payload or signaling metadata"
              ]
          }
        logInfoAt tk <| ← Inspection.renderExecProfile baseProfile typeExpr family

end FloatLib.Floats.Formats.P3109.FloatInfo.Command
