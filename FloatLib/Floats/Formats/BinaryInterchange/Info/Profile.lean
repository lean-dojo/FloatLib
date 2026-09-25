/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz
public meta import FloatLib.Floats.Formats.BinaryInterchange.Format.Runtime
public meta import FloatLib.Floats.Formats.BinaryInterchange.Format.Storage
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Contract

/-!
# Inspection profiles for binary-interchange formats

Representation, exceptional values, rounding rules, and theorem groups used by `#float_info`.
`Info.Command` resolves the carrier and supplies its storage and execution details. Complex and
interval profiles also use `inspectSummary` to read their component descriptor.

Each theorem group states its scope. IEEE-specific theorems are marked unavailable when the
descriptor does not meet their encoding and bias requirements.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

namespace FloatInfo

open Lean Meta
open FloatLib.Floats.ExecFloat

/-- Closed descriptor data extracted by the `#float_info` elaborator. -/
meta structure Summary where
  /-- Number of stored exponent bits. -/
  expWidth : Nat
  /-- Number of stored fraction bits. -/
  fracWidth : Nat
  /-- Bias subtracted from a stored normal exponent. -/
  exponentBias : Nat
  /-- Exceptional-value encoding policy. -/
  encoding : FloatFormat.Encoding
  /-- Total encoded width, including the sign bit. -/
  bitWidth : Nat
  /-- Smallest unbiased exponent of a normal value. -/
  minNormalExponent : Int
  /-- Largest unbiased exponent of a finite normal value. -/
  maxNormalExponent : Int
  /-- Whether the descriptor uses the conventional IEEE bias and exceptional-value encoding. -/
  isIEEE : Bool

/-- Read the exceptional-value policy of a closed binary descriptor. -/
private meta def readEncoding (format : Expr) : MetaM FloatFormat.Encoding := do
  let value ← Inspection.reduceProjection ``FloatFormat.encoding format
  if value.isConstOf ``FloatFormat.Encoding.ieee then
    return .ieee
  if value.isConstOf ``FloatFormat.Encoding.finiteMaxNaN then
    return .finiteMaxNaN
  if value.isConstOf ``FloatFormat.Encoding.finiteUnsignedZero then
    return .finiteUnsignedZero
  if value.isConstOf ``FloatFormat.Encoding.finite then
    return .finite
  throwError "failed to inspect the binary exceptional-value encoding"

/-- Read the descriptor fields used by scalar, complex, and interval reports. -/
meta def inspectSummary (format : Expr) : MetaM Summary := do
  let expWidth ←
    Inspection.readNatProjection "binary descriptor" ``FloatFormat.expWidth format
  let fracWidth ←
    Inspection.readNatProjection "binary descriptor" ``FloatFormat.fracWidth format
  let exponentBias ←
    Inspection.readNatProjection "binary descriptor" ``FloatFormat.exponentBias format
  let encoding ← readEncoding format
  let maxFiniteExponent := encoding.maxFiniteExponent expWidth
  pure
    { expWidth
      fracWidth
      exponentBias
      encoding
      bitWidth := ←
        Inspection.readNatProjection "binary descriptor" ``FloatFormat.bitWidth format
      minNormalExponent := 1 - Int.ofNat exponentBias
      maxNormalExponent := Int.ofNat maxFiniteExponent - Int.ofNat exponentBias
      isIEEE := ←
        Inspection.readFlagProjection "binary descriptor"
          ``FloatFormat.isIEEE ``Bool.true ``Bool.false format }

/-- Human-readable name of a binary exceptional-value policy. -/
meta def encodingName : FloatFormat.Encoding → String
  | .ieee => "IEEE exceptional encodings"
  | .finiteMaxNaN => "finite values with maximum-fraction NaN"
  | .finiteUnsignedZero => "finite values with unsigned zero (FNUZ)"
  | .finite => "finite-only"

/-- Identify named IEEE layouts; arbitrary widths retain the more general IEEE-style label. -/
meta def standardName (summary : Summary) : String :=
  if summary.isIEEE then
    match summary.expWidth, summary.fracWidth with
    | 5, 10 => "IEEE 754-2019 binary16"
    | 8, 23 => "IEEE 754-2019 binary32"
    | 11, 52 => "IEEE 754-2019 binary64"
    | 15, 112 => "IEEE 754-2019 binary128"
    | _, _ => "IEEE-style binary descriptor"
  else
    "binary descriptor with format-specific encoding or bias"

/-- Precise NaN population and metadata retained by an encoding policy. -/
meta def nanDescription (encoding : FloatFormat.Encoding) : String :=
  match encoding with
  | .ieee =>
      "yes; sign, signaling/quiet class, and complete fraction payload are decoded"
  | .finiteMaxNaN =>
      "yes; one maximum-fraction quiet NaN per sign"
  | .finiteUnsignedZero =>
      "yes; the negative-zero bit pattern is the sole quiet NaN"
  | .finite =>
      "no"

/--
Whether the encoding has a signaling NaN. IEEE signaling NaNs require a nonzero fraction
with a clear quiet bit, so at least one fraction bit must lie below the quiet bit.
-/
meta def signalingNaNDescription (encoding : FloatFormat.Encoding) (fracWidth : Nat) : String :=
  match encoding with
  | .ieee =>
      if fracWidth > 1 then "yes"
      else "no; no payload bit is available below the quiet bit"
  | .finiteMaxNaN | .finiteUnsignedZero =>
      "no; every NaN in this encoding is quiet"
  | .finite => "no; the encoding has no NaN"

/-- Descriptor-level applicability of theorem families specialized to conventional IEEE layouts. -/
meta def ieeeApplicability
    (summary : Summary) : FloatLib.Floats.ExecFloat.TheoremApplicability :=
  if summary.isIEEE then
    .verifiedForType
  else
    .unavailable
      "the theorem requires `format.isIEEE = true`, but this descriptor reduces it to `false`"

/--
Applicability of a cross-format IEEE theorem when the inspected descriptor may occupy either side.
-/
meta def ieeeCrossFormatApplicability
    (summary : Summary) : FloatLib.Floats.ExecFloat.TheoremApplicability :=
  if summary.isIEEE then
    .conditional "the other source or destination descriptor must also satisfy `isIEEE = true`"
  else
    .unavailable
      "the theorem requires both source and destination descriptors to satisfy `isIEEE = true`"

/-- Applicability of the all-words-finite range-limited enclosure theorems. -/
meta def finiteOnlyApplicability
    (summary : Summary) : FloatLib.Floats.ExecFloat.TheoremApplicability :=
  if summary.encoding == .finite then
    .verifiedForType
  else
    .unavailable
      "the theorem requires `format.encoding = .finite`; NaN-reserving finite encodings have a different boundary"

/-- Build the complete user-facing inspection profile for a binary descriptor. -/
meta def profile
    (summary : Summary)
    (standard : String)
    (storage : String)
    (executionIdentity : List FloatLib.Floats.ExecFloat.InfoEntry) :
    FloatLib.Floats.ExecFloat.FormatProfile where
  family := "binary interchange"
  standard
  declarationPrefix := "FloatLib.Floats.Formats.BinaryInterchange."
  representation :=
    [ ⟨"storage", storage⟩
    , ⟨"total bits", toString summary.bitWidth⟩
    , ⟨"sign bits", "1"⟩
    , ⟨"exponent bits", toString summary.expWidth⟩
    , ⟨"stored fraction bits", toString summary.fracWidth⟩
    , ⟨"normal significand precision", s!"{summary.fracWidth + 1} bits"⟩
    , ⟨"exponent bias", toString summary.exponentBias⟩
    , ⟨"minimum normal exponent", toString summary.minNormalExponent⟩
    , ⟨"maximum finite normal exponent", toString summary.maxNormalExponent⟩
    , ⟨"encoding", encodingName summary.encoding⟩
    ]
  values :=
    [ ⟨"finite numbers", "yes"⟩
    , ⟨"subnormals", "yes; exponent field zero with a nonzero fraction"⟩
    , ⟨"distinct signed zeros", yesNo (summary.encoding != .finiteUnsignedZero)⟩
    , ⟨"signed infinities", yesNo (summary.encoding == .ieee)⟩
    , ⟨"NaN", nanDescription summary.encoding⟩
    , ⟨"signaling NaN", signalingNaNDescription summary.encoding summary.fracWidth⟩
    ]
  rounding :=
    [ ⟨"numeric literals",
        "exact integer/rational input rounded once to nearest, ties to even"⟩
    , ⟨"public ExecFloat arithmetic", "nearest, ties to even"⟩
    , ⟨"family APIs",
        "directed rounding and status-bearing operations are also available"⟩
    , ⟨"status flags",
        "invalid, divide-by-zero, overflow, underflow, and inexact are modeled explicitly"⟩
    ]
  execution := executionIdentity ++
    [ ⟨"backend proof",
        "each reported arithmetic path is proved equal to its reference definition"⟩ ]
  theoremSurfaces :=
    [ { topic := "exact encoded interpretation"
        declarations := []
        definitions := [``Model.exactValue, ``Model.AtExact, ``Model.AtValue]
        applicability := .verifiedForType
        scope :=
          "all bit patterns; finite dyadics plus signed-zero, infinity, and NaN metadata when represented by the encoding" }
    , { topic := "descriptor-indexed arithmetic refinement"
        declarations :=
          [ ``Model.Proof.add_eq_spec
          , ``Model.Proof.sub_eq_spec
          , ``Model.Proof.mul_eq_spec
          , ``Model.Proof.div_eq_spec
          , ``Model.Proof.sqrt_eq_spec
          , ``Model.Proof.fma_eq_spec
          ]
        applicability := .verifiedForType
        scope :=
          "all encoded operands for every valid descriptor; each automatically dispatched proof-model operation equals its descriptor-aware specification" }
    , { topic := "IEEE nearest-even operation semantics"
        declarations :=
          [ ``Model.toReal_add_eq_roundAt
          , ``Model.toReal_sub_eq_roundAt
          , ``Model.toReal_mul_eq_roundAt
          , ``Model.toReal_div_eq_roundAt
          , ``Model.toReal_sqrt_eq_roundAt
          , ``Model.isFinite_sqrt_of_isFinite
          , ``Model.toReal_fma_eq_roundAt
          ]
        applicability := ieeeApplicability summary
        scope :=
          "the finiteness, sign, nonzero, domain, and result-range hypotheses in each theorem"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Each listed finite primitive equals one nearest-even rounding of its exact real operation." } }
    , { topic := "status-bearing operations and flag classifiers"
        declarations :=
          [ ``Model.addWithStatus_value
          , ``Model.subWithStatus_value
          , ``Model.mulWithStatus_value
          , ``Model.divWithStatus_value
          , ``Model.sqrtWithStatus_value
          , ``Model.fmaWithStatus_value
          , ``Model.addWithStatus_of_toDyadic
          , ``Model.mulWithStatus_of_toDyadic
          , ``Model.divWithStatus_of_toDyadic_nonzero
          , ``Model.fmaWithStatus_of_toDyadic
          , ``Model.addWithStatus_invalid
          , ``Model.mulWithStatus_invalid
          , ``Model.divWithStatus_invalid
          , ``Model.divWithStatus_divideByZero
          , ``Model.sqrtWithStatus_invalid
          , ``Model.fmaWithStatus_invalid
          , ``Model.dyadicRoundingStatus_inexact_of_underflow
          , ``Model.dyadicRoundingStatus_inexact_of_overflow
          , ``Model.rationalRoundingStatusScaled_inexact_of_underflow
          , ``Model.rationalRoundingStatusScaled_inexact_of_overflow
          ]
        definitions :=
          [ ``Model.IEEEStatus
          , ``Model.OutcomeAt
          , ``Model.addWithStatus
          , ``Model.subWithStatus
          , ``Model.mulWithStatus
          , ``Model.divWithStatus
          , ``Model.sqrtWithStatus
          , ``Model.fmaWithStatus
          ]
        applicability := .verifiedForType
        scope :=
          "all binary descriptors; value preservation, finite rounding classification, invalid operations, divide-by-zero, and the overflow/underflow/inexact invariants stated by the listed theorems" }
    , { topic := "standard classification, comparison, adjacency, remainder, integral, and exponent operations"
        declarations :=
          [ ``Model.compare_eq_some_lt_iff_toEReal_lt
          , ``Model.compare_eq_some_eq_iff_toEReal_eq
          , ``Model.compare_eq_some_gt_iff_toEReal_gt
          , ``Model.toEReal_minimum_eq_min
          , ``Model.toEReal_maximum_eq_max
          , ``Model.toEReal_minNum_eq_min
          , ``Model.toEReal_maxNum_eq_max
          , ``Model.toEReal_minimumNumber_eq_min
          , ``Model.toEReal_maximumNumber_eq_max
          , ``Model.minimumNumber_of_isNaN_left
          , ``Model.maximumNumber_of_isNaN_left
          , ``Model.minimumNumberWithStatus_invalid
          , ``Model.maximumNumberWithStatus_invalid
          , ``Model.nextUpWithStatus_invalid
          , ``Model.nextDownWithStatus_invalid
          , ``Model.adjacencyRank_nextUp
          , ``Model.adjacencyRank_nextDown
          , ``Model.no_rank_between_nextUp
          , ``Model.no_rank_between_nextDown
          , ``Model.remainderDyadic_toRat
          , ``Model.remainderWithStatus_of_finite
          , ``Model.remainderWithStatus_exact
          , ``Model.remainderWithStatus_of_zero_divisor
          , ``Model.roundToIntegralExactWithStatus_of_finite
          , ``Model.roundToIntegralExactWithStatus_inexact_iff
          , ``Model.roundToIntegralExactWithStatus_overflow_eq_false
          , ``Model.isFinite_roundToIntegral
          , ``Model.toReal_roundToIntegral_towardNegativeInfinity
          , ``Model.toReal_roundToIntegral_towardPositiveInfinity
          , ``Model.toReal_roundToIntegral_towardZero
          , ``Model.toReal_roundToIntegral_nearestEven
          , ``Model.scaleWithStatus_of_finite
          , ``Model.binaryExponentWithStatus_of_finite_nonzero
          ]
        definitions :=
          [ ``Model.signBit
          , ``Model.isZero
          , ``Model.isFinite
          , ``Model.isSubnormal
          , ``Model.isInf
          , ``Model.isNaN
          , ``Model.isSNaN
          , ``Model.isQNaN
          , ``Model.neg
          , ``Model.abs
          , ``Model.copySign
          , ``Model.compare
          , ``Model.minimum
          , ``Model.maximum
          , ``Model.minNum
          , ``Model.maxNum
          , ``Model.minimumNumber
          , ``Model.maximumNumber
          , ``Model.minimumNumberWithStatus
          , ``Model.maximumNumberWithStatus
          , ``Model.nextUp
          , ``Model.nextDown
          , ``Model.nextUpWithStatus
          , ``Model.nextDownWithStatus
          , ``Model.remainderWithStatus
          , ``Model.roundToIntegralExactWithStatus
          , ``Model.scaleWithStatus
          , ``Model.binaryExponentWithStatus
          ]
        applicability := .verifiedForType
        scope :=
          "all binary descriptors under the non-NaN, finite, nonzero, and endpoint hypotheses stated by each theorem; the declaration list is validated when the inspection profile is constructed" }
    , { topic := "IEEE directed rounding and interval enclosures"
        declarations :=
          [ ``Model.toEReal_addDown_le
          , ``Model.le_toEReal_addUp
          , ``Model.toEReal_subDown_le
          , ``Model.le_toEReal_subUp
          , ``Model.toEReal_mulDown_le
          , ``Model.le_toEReal_mulUp
          , ``Model.toEReal_divDown_le
          , ``Model.le_toEReal_divUp
          , ``Model.toEReal_sqrtDown_le
          , ``Model.le_toEReal_sqrtUp
          , ``Model.Interval.add_sound
          , ``Model.Interval.sub_sound
          , ``Model.Interval.mul_sound
          , ``Model.Interval.div_sound
          , ``Model.Interval.sqrt_sound
          ]
        applicability := ieeeApplicability summary
        scope :=
          "the finite-input, interval-validity, and operation-domain hypotheses stated by each theorem"
        numericalGuarantee? := some {
          kinds := [.range]
          statement :=
            "Directed endpoints and interval operations enclose the exact real result." } }
    , { topic := "finite-only range-limited directed rounding and dyadic interval arithmetic"
        declarations :=
          [ ``Model.toReal_roundDyadicDown_le_of_encoding_finite
          , ``Model.le_toReal_roundDyadicUp_of_encoding_finite
          , ``Model.toReal_addDown_le_of_encoding_finite
          , ``Model.le_toReal_addUp_of_encoding_finite
          , ``Model.toReal_subDown_le_of_encoding_finite
          , ``Model.le_toReal_subUp_of_encoding_finite
          , ``Model.toReal_mulDown_le_of_encoding_finite
          , ``Model.le_toReal_mulUp_of_encoding_finite
          , ``Model.Interval.add_sound_of_encoding_finite
          , ``Model.Interval.sub_sound_of_encoding_finite
          , ``Model.Interval.mul_sound_of_encoding_finite
          ]
        applicability := finiteOnlyApplicability summary
        scope :=
          "all-words-finite encoding only; exact add/sub endpoint expressions and all four multiplication corners must lie within the largest-finite magnitude"
        numericalGuarantee? := some {
          kinds := [.range]
          statement :=
            "Range-limited directed endpoints enclose exact dyadic add, subtract, and multiply results." } }
    , { topic := "generic rounding-grid error bounds"
        declarations :=
          [ ``Model.abs_roundAt_sub_le
          , ``Model.roundAt_mem_Icc
          , ``Model.relativeError_roundAt_le_of_normal
          ]
        applicability := .verifiedForType
        scope :=
          "roundAt uses this descriptor's precision and bias with no upper exponent bound. " ++
          "Executable operations require a separate refinement theorem; relative error requires " ++
          "nonzero normal-range input."
        numericalGuarantee? := some {
          kinds := [.range, .rounding, .absoluteError, .relativeError]
          statement :=
            "The real-valued roundAt grid has absolute error at most 1/2 ULP; " ++
            "for nonzero normal-range inputs, relative error is at most " ++
            s!"2^-{summary.fracWidth + 1}."
        } }
    , { topic := "exact compatible widening"
        declarations := [``Model.cast_exact_of_compatibleWidening]
        applicability := .verifiedForType
        scope :=
          "source and destination have equal exponent width, bias, and encoding, while destination precision is at least the source precision"
        numericalGuarantee? := some {
          kinds := [.exactness]
          statement :=
            "A compatible widening preserves the represented finite value with zero rounding error." } }
    , { topic := "mixed-precision sequential reduction and matrix entry bounds"
        declarations :=
          [ ``Model.mulAccError_eq_site_residuals
          , ``Model.mulAcc_abs_error_le_budget
          , ``Model.sequentialAccumulator_error_eq_sum
          , ``Model.dotSequential_abs_error_le_budget
          , ``Model.matmul_refines
          , ``Model.matmul_entry_abs_error_le_budget
          ]
        definitions := [``Model.SitePolicy, ``Model.MatmulRefines]
        applicability := ieeeCrossFormatApplicability summary
        scope :=
          "arbitrary storage, product, accumulator, and output descriptors under the IEEE, finiteness, length, shape, and per-site premises stated by each theorem"
        numericalGuarantee? := some {
          kinds := [.absoluteError]
          statement :=
            "Sequential dot products and matrix entries are bounded by the sum of their checked per-site rounding residual budgets." } }
    , { topic := "IEEE operation error bounds and Sterbenz exactness"
        declarations :=
          [ ``Model.abs_toReal_add_sub_le
          , ``Model.abs_toReal_sub_sub_le
          , ``Model.abs_toReal_mul_sub_le
          , ``Model.abs_toReal_div_sub_le
          , ``Model.abs_toReal_sqrt_sub_le
          , ``Model.abs_toReal_fma_sub_le
          , ``Model.toReal_sub_eq_of_sterbenz
          ]
        applicability := ieeeApplicability summary
        scope :=
          "the finiteness, result-range, positivity, normality, and factor-of-two hypotheses stated by each theorem"
        numericalGuarantee? := some {
          kinds := [.absoluteError, .exactness]
          statement :=
            "Each finite primitive has at most 1/2 ULP absolute error; Sterbenz subtraction is exact in its proved factor-of-two domain." } }
    , { topic := "IEEE cross-format cast semantics"
        declarations :=
          [ ``Model.cast_eq_roundAt
          , ``Model.cast_exact_of_gridExtension
          , ``Model.abs_toReal_cast_sub_le
          ]
        applicability := ieeeCrossFormatApplicability summary
        scope :=
          "the source/destination finiteness, result-range, precision, and minimum-subnormal-exponent hypotheses stated by each theorem"
        numericalGuarantee? := some {
          kinds := [.rounding, .absoluteError, .exactness]
          statement :=
            "A finite cast is one destination rounding with at most 1/2 destination ULP error, and grid extensions are exact." } }
    , { topic := "transcendental enclosures and whole-algorithm proof contracts"
        declarations :=
          [ ``Model.Transcendentals.Contract.RealEnclosure.abs_sub_le_width
          , ``Model.Transcendentals.Contract.StableEnclosure.roundAt_eq_roundAt_lower
          , ``Model.Transcendentals.Contract.CertifiedRoundedResult.toReal_value_eq_roundAt
          ]
        definitions :=
          [ ``Model.Transcendentals.Contract.RealEnclosure
          , ``Model.Transcendentals.Contract.RealEnclosure.exp
          , ``Model.Transcendentals.Contract.RealEnclosure.log
          , ``Model.Transcendentals.Contract.RealEnclosure.sqrt
          , ``Model.Transcendentals.Contract.RealEnclosure.sin
          , ``Model.Transcendentals.Contract.RealEnclosure.cos
          , ``Model.Transcendentals.Contract.RealEnclosure.sinh
          , ``Model.Transcendentals.Contract.RealEnclosure.cosh
          , ``Model.Transcendentals.Contract.RealEnclosure.tanh
          , ``Model.Transcendentals.Contract.ApproximationCertificate
          , ``Model.Transcendentals.Contract.CorrectlyRoundedCertificate
          ]
        applicability := .conditional
          "a whole-algorithm certificate for the selected executable kernel; the built-in approximations supply none"
        scope :=
          "generic finite-real proof interfaces, not certificates for this type's executable kernels; numerical accuracy or correct rounding requires an inhabited certificate connecting the selected kernel to the real function" }
    ]
  nonclaims :=
    [ "equivalence between compiled Float32/Float arithmetic and this type; only the explicit conversion boundary is checked"
    , "every clause of IEEE 754 follows from the six backend-refinement equations"
    , "bitwise format/parse round trips for NaN payloads; the formatter intentionally emits a canonical `nan` spelling"
    , "the built-in deterministic transcendental kernels currently carry a whole-algorithm approximation or correctly-rounded certificate"
    , "external MPFR, Arb, compiler lowering, or FFI behavior is inside this certificate"
    ]

end FloatInfo

end FloatLib.Floats.Formats.BinaryInterchange
