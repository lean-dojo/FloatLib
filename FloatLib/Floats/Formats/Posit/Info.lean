/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Info
import FloatLib.Floats.Formats.Posit.Arithmetic.WordLimb.Proof
public import FloatLib.Floats.Formats.Posit.Configured
public import FloatLib.Floats.Formats.Posit.Quire.Info
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Proof -- shake: keep
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Runtime -- shake: keep
public import FloatLib.Floats.Formats.Posit.Semantics.Ordinary.Real
public import FloatLib.Floats.Formats.Posit.Semantics.Projective

/-!
# Posit inspection

`#float_info` reports posit storage, arithmetic capabilities, and applicable rounding and quire
theorems. The descriptor and synthesized instances determine which width-dependent backends
apply. The quire theorem list is shared with `Quire.Info`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.FloatInfo

open FloatLib.Floats.ExecFloat

/-- Describe posit representations, operation contracts, and applicable refinement theorems. -/
meta def profile (bits : Nat) (storage : String) : FormatProfile where
  family := "posit"
  standard := "Standard for Posit Arithmetic (2022)"
  declarationPrefix := "FloatLib.Floats.Formats.Posit."
  representation :=
    [ ⟨"storage", storage⟩
    , ⟨"total bits", toString bits⟩
    , ⟨"sign bits", "1"⟩
    , ⟨"regime", "value-dependent run with an opposite-bit terminator when space remains"⟩
    , ⟨"maximum exponent bits", "2, as fixed by the current Posit Standard"⟩
    , ⟨"fraction bits", "tapered; all payload bits remaining after regime and exponent"⟩
    , ⟨"associated quire width", toString (16 * bits)⟩
    , ⟨"quire least-significant-bit scale",
        s!"2^({16 - 8 * Int.ofNat bits})"⟩
    ]
  values :=
    [ ⟨"finite numbers", "yes; every code except NaR is finite"⟩
    , ⟨"zero", "one unsigned zero code"⟩
    , ⟨"Not-a-Real", "one NaR code; exact semantics uses ExceptionalValue.notAReal"⟩
    , ⟨"infinities", "none"⟩
    , ⟨"NaNs", "none; NaR is a distinct posit value class, not an IEEE NaN payload family"⟩
    , ⟨"subnormals", "none; tapered precision replaces the IEEE normal/subnormal split"⟩
    , ⟨"comparisons",
        "Mathlib LinearOrder and six Boolean predicates match signed two's-complement word comparison; NaR is least but has no real denotation"⟩
    , ⟨"ordinary-value subtype",
        "Model.Ordinary excludes NaR and supplies a total exact Rat coordinate plus canonical Real coordinate"⟩
    , ⟨"projective view",
        "available explicitly through mathlib OnePoint/projectivization; maps finite values to their exact coordinates and NaR to the added point"⟩
    ]
  rounding :=
    [ ⟨"numeric literals",
        "exact rational input; appended-bit threshold with ties to even retained low bit"⟩
    , ⟨"overflow", "saturates to signed maxpos; no infinity encoding exists"⟩
    , ⟨"underflow", "every nonzero magnitude below minpos rounds to signed minpos"⟩
    , ⟨"proof boundary",
        "global rational, exact-dyadic, native-word, and two-limb refinement theorems cover the complete search, tie handling, sign symmetry, and encoded result"⟩
    ]
  execution :=
    [ ⟨"carrier", storage⟩
    , ⟨"conversion reference",
        "exact Rat decoder plus logarithmic code search; no host Float conversion"⟩
    , ⟨"exact intermediates",
        "all six core operations avoid Rat at runtime: add, subtract, multiply, and FMA round an exact dyadic result; division rounds a quotient prefix using its exact remainder; square root rounds an integer-root prefix using its exact square remainder"⟩
    , ⟨"2-64 bit execution",
        "operations decode the built-in UInt carrier with proved shifts, masks, and a masked UInt64.log2 regime count, then pack the result code directly; multiply and FMA stay scalar when the exact intermediate fits and otherwise use the shared two-limb rounder"⟩
    , ⟨"65-128 bit execution",
        "operations decode the stored UInt64 pair directly; add, subtract, multiply, and FMA use proved packed kernels; division and square root reuse the generic quotient-prefix and square-root rounders"⟩
    , ⟨"standard basic functions",
        "wrapping next/prior, abs, sign, nearestInt, ceil, and floor are executable on the configured carrier; integer functions use exact Rat bounds"⟩
    , ⟨"elementary functions",
        "natural and base-two/base-ten exponentials and logarithms, radian and pi-scaled trigonometric functions, and hyperbolic functions use total exact comparisons with posit rounding boundaries"⟩
    , ⟨"decimal text",
        "exact decimal display and parsing with one rational-to-posit rounding; parsing the display recovers every value, including NaR"⟩
    , ⟨"standard quire",
        "16n-bit signed fixed-point exact accumulator with integer/dyadic pToQ, qNegate, qAbs, qAddP, qSubP, qAddQ, qSubQ, qMulAdd, qMulSub, and one-rounding qToP; the most-negative word is quire NaR"⟩
    , ⟨"dispatch",
        "core operations appear below only when a proof-carrying capability instance is synthesized"⟩
    ]
  theoremSurfaces :=
    [ { topic := "exact zero and NaR semantics"
        declarations :=
          [ ``Model.decode_zero
          , ``Model.decode_nar
          , ``Model.zero_ne_nar
          , ``Model.isZero_eq_true_iff
          , ``Model.isNaR_eq_true_iff
          , ``Model.toRat?_eq_none_iff
          , ``Model.toReal?_eq_none_iff
          ]
        applicability := .verifiedForType
        scope := "all valid static widths" }
    , { topic := "standard comparison order and finite enumeration"
        declarations :=
          [ ``Model.signedCode_injective
          , ``Model.compareEqual_eq_true_iff
          , ``Model.compareNotEqual_eq_true_iff
          , ``Model.compareLess_eq_true_iff
          , ``Model.compareLessEqual_eq_true_iff
          , ``Model.compareGreater_eq_true_iff
          , ``Model.compareGreaterEqual_eq_true_iff
          ]
        definitions := [``Model.bitsEquiv, ``Configured.Family.modelEquiv]
        applicability := .verifiedForType
        scope :=
          "all valid static widths; standard two's-complement word order, including NaR as least; not an order embedding of NaR into Rat or Real" }
    , { topic := "ordinary-value exact coordinates"
        declarations :=
          [ ``Model.Ordinary.toRat_isSome
          , ``Model.Ordinary.model_toRat?_eq_some
          , ``Model.Ordinary.model_toReal?_eq_some
          , ``Model.Ordinary.toRat_zero
          , ``Model.Ordinary.toReal_zero
          ]
        applicability := .verifiedForType
        scope :=
          "all non-NaR words at every valid static width; provides exact Rat and canonical Real coordinates without assigning NaR a number" }
    , { topic := "exact tapered-field decoder"
        declarations :=
          [ ``Configured.Family.toModel_ofModel
          , ``Configured.Family.ofModel_toModel
          ]
        definitions := [``Model.decodeExact, ``Model.ExactValue.forget]
        applicability := .verifiedForType
        scope := "every encoded word; carrier packing is proved inverse to the exact-width model" }
    , { topic := "mathlib rational/real one-point and projective-line interoperability"
        declarations :=
          [ ``Model.toProjectiveRat_eq_infty_iff
          , ``Model.toProjectiveRat_eq_coe_iff
          , ``Model.toProjectiveRatLine_eq_finite_iff
          , ``Model.toProjectiveRatLine_eq_nar_iff
          , ``Model.toProjectiveReal_eq_infty_iff
          , ``Model.toProjectiveReal_eq_coe_iff
          , ``Model.toProjectiveRealLine_eq_finite_iff
          , ``Model.toProjectiveRealLine_eq_nar_iff
          ]
        applicability := .verifiedForType
        scope :=
          "finite values embed exactly from Rat into Real; projective views are optional and deliberately identify NaR with the added point; primary NumericalValue semantics does not" }
    , { topic := "current-standard basic functions"
        declarations :=
          [ ``Model.prior_next
          , ``Model.next_prior
          , ``Model.abs_zero
          , ``Model.abs_nar
          , ``Model.sign_zero
          , ``Model.sign_nar
          , ``Model.nearestEvenInteger_int
          , ``Model.nearestInt_zero
          , ``Model.nearestInt_nar
          , ``Model.ceil_zero
          , ``Model.ceil_nar
          , ``Model.floor_zero
          , ``Model.floor_nar
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths; next/prior are mutual inverses on every encoded word, and value functions preserve the proved zero/NaR cases" }
    , { topic := "executable exact-rational conversion"
        declarations :=
          [ ``Model.nonnegativeRatAt_lt_of_lt
          , ``Model.nonnegativeRatAt_strictMonoOn
          , ``Model.nonnegativeRatAt_le_iff
          , ``Model.nonnegativeRatAt_injOn
          , ``Model.nonnegativeRatAt_nextPrecision_two_mul
          , ``Model.lowerCodeForPositive_nonnegativeRatAt
          , ``Model.nonnegativeRatAt_lt_roundingThreshold
          , ``Model.roundPositiveCode_nonnegativeRatAt
          , ``Model.roundPositiveRat_nonnegativeRatAt
          , ``Model.roundRat_nonnegativeRatAt
          , ``Model.roundRat_zero
          , ``Model.roundPositiveCode_zero
          , ``Model.roundRat_of_neg
          ]
        definitions := [``Model.roundRat]
        applicability := .verifiedForType
        scope :=
          "all valid static widths; unsigned finite codes are globally strictly ordered by exact rational value, U0 preserves U across the standard's next-precision embedding, U1 is strictly above it, bisection recovers every code, and public rational rounding re-encodes every nonnegative finite word; negative inputs use proved encoding symmetry and optimized refinements below prove equality to this reference"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Exact rational inputs are rounded by the proved current-standard tapered-grid rule, including ties, underflow, saturation, and sign symmetry." } }
    , { topic := "certified exact-dyadic arithmetic refinement"
        declarations :=
          [ ``Model.DyadicArithmetic.add_eq_spec
          , ``Model.DyadicArithmetic.sub_eq_spec
          , ``Model.DyadicArithmetic.mul_eq_spec
          , ``Model.DyadicArithmetic.div_eq_spec
          , ``Model.DyadicArithmetic.sqrt_eq_spec
          , ``Model.DyadicArithmetic.fma_eq_spec
          , ``Model.DirectDyadicArithmetic.add_eq_dyadic
          , ``Model.DirectDyadicArithmetic.sub_eq_dyadic
          , ``Model.DirectDyadicArithmetic.mul_eq_dyadic
          , ``Model.DirectDyadicArithmetic.sqrt_eq_dyadic
          , ``Model.DirectDyadicArithmetic.fma_eq_dyadic
          , ``Model.DirectDyadicArithmetic.add_eq_spec
          , ``Model.DirectDyadicArithmetic.sub_eq_spec
          , ``Model.DirectDyadicArithmetic.mul_eq_spec
          , ``Model.DirectDyadicArithmetic.div_eq_spec
          , ``Model.DirectDyadicArithmetic.sqrt_eq_spec
          , ``Model.DirectDyadicArithmetic.fma_eq_spec
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths; add/subtract/multiply/FMA directly pack an exact dyadic result with one guard-and-sticky rule, division uses a destination-width quotient prefix with exact remainder rounding, and square root uses an exact integer-root kernel; all six implementations refine the rational specification"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "All six core operations refine their exact rational or real specification with one final posit rounding; no uniform global relative-error constant is claimed for tapered precision." } }
    , { topic := "once-rounded algebraic functions"
        declarations :=
          [ ``Model.rSqrt_eq_roundPositive
          , ``Model.hypot_eq_roundPositive
          , ``Model.fMM_eq_roundRat
          , ``Model.rootN_eq_roundPositive
          , ``Model.rootN_eq_neg_roundPositive
          , ``Model.powInt_eq_roundRat
          , ``Model.compound_eq_roundRat
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths; finite inputs in each operation's real domain, with " ++
          "separate NaR and invalid-domain theorems"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Reciprocal square root, hypotenuse, triple multiplication, integer roots, integer " ++
            "powers, and compound evaluate exact intermediates before one standard posit " ++
            "rounding. Integer-root comparisons use exact powers of rounding boundaries." } }
    , { topic := "rational powers and base-two/base-ten exponentials"
        declarations :=
          [ ``Model.pow_eq_roundPositive
          , ``Model.pow_eq_roundRat_of_neg
          , ``Model.exp2_eq_roundPositive
          , ``Model.exp10_eq_roundPositive
          , ``Model.exp2Minus1_eq_round
          , ``Model.exp10Minus1_eq_round
          ]
        applicability := .verifiedForType
        scope :=
          "finite inputs in the real domain; negative bases require integer exponents; " ++
          "zero and NaR cases have separate theorems"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Exact integer shortcuts and certified logarithmic comparisons with an exact " ++
            "power fallback select one real rounding. Minus1 subtracts before rounding, " ++
            "including exact-boundary cases." } }
    , { topic := "base-two and base-ten logarithms"
        declarations :=
          [ ``Model.log2_eq_real
          , ``Model.log10_eq_real
          , ``Model.log2Plus1_eq_real
          , ``Model.log10Plus1_eq_real
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths and finite inputs in the logarithm's domain; NaR and " ++
          "nonpositive exact arguments have separate rejection theorems"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Each result equals signed real posit rounding of the exact logarithm. Plus1 " ++
            "forms its addition exactly. Boundary comparisons use proved logarithm bounds " ++
            "with an exact rational-power fallback, including ties." } }
    , { topic := "natural exponential and logarithm"
        declarations :=
          [ ``Model.exp_eq_real
          , ``Model.expMinus1_eq_real
          , ``Model.log_eq_real
          , ``Model.logPlus1_eq_real
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths and finite inputs in the function's domain; NaR " ++
          "propagation and invalid logarithm domains are proved separately"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Total adaptive rational comparisons determine the exact signed real rounding. " ++
            "Convergence and rational-input irrationality prove termination; exp 0 and log 1 " ++
            "are exact cases. Minus1 and Plus1 introduce no intermediate posit rounding." } }
    , { topic := "radian trigonometric functions"
        declarations :=
          [ ``Model.sin_eq_real
          , ``Model.cos_eq_real
          , ``Model.tan_eq_real
          , ``Model.arcSin_eq_real
          , ``Model.arcCos_eq_real
          , ``Model.arcTan_eq_real
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths and finite inputs in the function's real domain; " ++
          "NaR propagation and inverse-function domain rejection are proved separately"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Each function equals standard posit rounding of its exact real value. " ++
            "Certified argument reduction and convergent rational enclosures determine " ++
            "boundary ordering; exact special cases and irrationality prove termination." } }
    , { topic := "pi-scaled trigonometric functions"
        declarations :=
          [ ``Model.sinPi_eq_real
          , ``Model.cosPi_eq_real
          , ``Model.tanPi_eq_real
          , ``Model.tanPi_eq_nar_of_pole
          , ``Model.arcSinPi_eq_real
          , ``Model.arcCosPi_eq_real
          , ``Model.arcTanPi_eq_real
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths and finite inputs in the function's real domain; " ++
          "half-integer tangent arguments produce NaR"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Pi multiplication or division is part of the exact expression before rounding. " ++
            "Complete rational special-value classifiers handle equality; convergent " ++
            "enclosures and principal-branch inversion settle all other comparisons." } }
    , { topic := "two-argument arctangent"
        declarations :=
          [ ``Model.arcTan2_eq_real
          , ``Model.arcTan2Pi_eq_real
          , ``Model.arcTan2_origin
          , ``Model.arcTan2Pi_origin
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths and finite coordinate pairs outside the origin; " ++
          "the origin and either NaR coordinate produce NaR"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "The result rounds the principal argument of x + i*y in (-pi, pi], " ++
            "or that exact argument divided by pi. Quadrants and axis values follow " ++
            "the Posit Standard's x-then-y coordinate order." } }
    , { topic := "hyperbolic functions"
        declarations :=
          [ ``Model.sinH_eq_real
          , ``Model.cosH_eq_real
          , ``Model.tanH_eq_real
          , ``Model.arcSinH_eq_real
          , ``Model.arcCosH_eq_real
          , ``Model.arcTanH_eq_real
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths; arcCosH requires an input at least one, and arcTanH " ++
          "requires an input strictly between minus one and one"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Direct and inverse hyperbolic functions compare exact expressions with each " ++
            "rounding boundary, without rounding intermediate exponentials or logarithms." } }
    , { topic := "exact decimal input and output"
        declarations :=
          [ ``Model.parse_eq_roundRat
          , ``Model.parse_display
          , ``Model.parse_toString
          , ``ExecFloat.Posit.parse_display
          , ``ExecFloat.Posit.parse_toString
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths, including NaR; exact decimal output, without a " ++
          "shortest-string guarantee"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Decimal input is parsed exactly before one posit rounding. The decimal " ++
            "representation of a posit recovers the complete value when parsed." } }
    , { topic := "width-aware signed-integer conversions"
        declarations :=
          [ ``Model.ofFixedInt_minCode
          , ``Model.toFixedInt_nar
          , ``Model.toInt_toFixedInt_of_inRange
          , ``Model.toFixedInt_error_le_half
          , ``Model.toFixedInt_even_of_half
          ]
        applicability := .verifiedForType
        scope :=
          "positive integer widths; the MSB-only word is the Posit Standard sentinel"
        numericalGuarantee? := some {
          kinds := [.rounding, .range]
          statement :=
            "Integer input sentinel maps to NaR. The reverse conversion rounds to nearest " ++
            "integer with even ties, checks range before encoding, and returns the sentinel " ++
            "for NaR or overflow." } }
    , { topic := "mathematical square-root refinement"
        declarations :=
          [ ``Model.lowerSqrtCode_eq_realRounding_lowerCode
          , ``Model.roundSqrtCode_eq_roundPositiveCode
          , ``Model.roundSqrtRat_eq_roundPositive
          , ``Model.DyadicSquareRoot.round_eq_realRounding_sqrt_of_nonnegative
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths and nonnegative finite inputs; the executable integer/dyadic squared-comparison path is proved to equal Posit Standard rounding of mathlib's Real.sqrt, including exact roots, nonzero underflow, saturation, appended-bit boundaries, and ties to even"
        numericalGuarantee? := some {
          kinds := [.rounding]
          statement :=
            "Executable square root equals current-standard rounding of the exact nonnegative real square root." } }
    , { topic := "direct exact result construction"
        declarations :=
          [ ``FloatLib.Numerics.Dyadic.compareFields_eq
          , ``FloatLib.Numerics.Dyadic.isLessFields_eq
          , ``FloatLib.Numerics.Dyadic.isLessOrEqualFields_eq
          , ``FloatLib.Numerics.Dyadic.isLessPowerOfTwoAtLeading_eq
          , ``Model.DirectDyadicPacking.leadingBit_eq_log2
          , ``Model.DirectDyadicPacking.roundPositiveCode_eq_dyadic
          , ``Model.DirectDyadicQuotient.roundPositiveCode_prefix_eq_reference
          , ``Model.DirectDyadicQuotient.roundPositiveCode_eq_reference
          , ``Model.DirectDyadicQuotient.roundPositiveCode_lt_signMask
          , ``Model.DirectDyadicQuotient.roundPositive_eq_reference
          , ``Model.DirectDyadicQuotient.round_eq_reference
          , ``Model.DirectDyadicSquareRoot.exponentParity_lt_two
          , ``Model.DirectDyadicSquareRoot.sourceExponent_eq
          , ``Model.DirectDyadicSquareRoot.roundCode_eq_fraction
          , ``Model.DirectDyadicSquareRoot.roundCode_eq_dyadic
          , ``Model.DirectDyadicSquareRoot.roundCode_lt_signMask
          , ``Model.DirectDyadicSquareRoot.roundCode_lt_modulus
          , ``Model.DirectDyadicSquareRoot.round_eq_dyadic_of_not_negative
          , ``Model.DirectDyadicSquareRoot.round_eq_reference_of_not_negative
          ]
        applicability := .verifiedForType
        scope :=
          "all valid static widths; ordinary exact dyadic results use one-pass regime/exponent/fraction packing with direct guard-and-sticky rounding; division generates one normalized quotient prefix with an exact remainder sticky bit; square root generates one destination-width integer-root prefix and jams its exact square remainder; neither direct kernel has a candidate certificate or search path" }
    , { topic := "proved direct packed-word decoding, rounding, and arithmetic"
        declarations :=
          [ ``Model.NativeWord.signMaskWord_toNat
          , ``Model.NativeWord.bitAt_eq_testBit
          , ``Model.NativeWord.bitAt_complement
          , ``Model.NativeWord.lowBits_toNat_of_le
          , ``Model.NativeWord.countLeadingZeros_eq_model
          , ``Model.NativeWord.countLeadingRun_eq_model
          , ``Model.NativeWord.magnitudeWord_eq_ofNat_magnitudeNat
          , ``Model.NativeWord.nonnegativeDyadicAt_negative
          , ``Model.NativeWord.withDyadicFieldsValid_eq
          , ``Model.NativeWord.withTwoDyadicFieldsValid_eq
          , ``Model.NativeWord.withThreeDyadicFieldsValid_eq
          , ``Model.NativeWord.toDyadic?_eq_model
          , ``Model.NativeWordRounding.GuardSticky.roundPositiveCodeWord_toNat_eq_direct
          , ``Model.NativeWordRounding.GuardSticky.roundPositiveCode_eq_direct
          , ``Model.NativeWordLimb.roundCodeWordLow_toNat_eq_direct
          , ``Model.NativeWordRounding.GuardSticky.roundCodeWord_toNat_eq_direct
          , ``Model.NativeWordRounding.GuardSticky.roundCodeNat_eq_direct
          , ``Model.NativeWordRounding.GuardSticky.roundCodeNat_lt_modulus
          , ``Model.NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_eq_direct
          , ``Model.NativeWordRounding.GuardSticky.DyadicTarget.roundCodeNat_lt_modulus
          , ``Model.DyadicRounding.restoreSignCode_lt_modulus
          , ``Model.DyadicRounding.ofNatBits_restoreSignCode
          , ``Model.DirectDyadicQuotient.roundCode_eq_toNatBits
          , ``Model.DirectDyadicQuotient.roundCode_lt_modulus
          , ``Model.DirectDyadicQuotient.ofNatBits_roundCode
          , ``Model.NativeWordArithmetic.addWordsCode_lt_modulus
          , ``Model.NativeWordArithmetic.addWordsCodeFlatValid_eq
          , ``Model.NativeWordArithmetic.addWordsCodeFlatValid_lt_modulus
          , ``Model.NativeWordArithmetic.subWordsCode_lt_modulus
          , ``Model.NativeWordArithmetic.subWordsCodeFlatValid_eq
          , ``Model.NativeWordArithmetic.subWordsCodeFlatValid_lt_modulus
          , ``Model.NativeWordArithmetic.mulWordsCode_lt_modulus
          , ``Model.NativeWordArithmetic.mulWordsCodeFlatValid_eq
          , ``Model.NativeWordArithmetic.mulWordsCodeFlatValid_lt_modulus
          , ``Model.NativeWordArithmetic.divWordsCode_lt_modulus
          , ``Model.NativeWordArithmetic.sqrtWordCode_lt_modulus
          , ``Model.NativeWordArithmetic.fmaWordsCode_lt_modulus
          , ``Model.NativeWordArithmetic.fmaWordsCodeFlatValid_eq
          , ``Model.NativeWordArithmetic.fmaWordsCodeFlatValid_lt_modulus
          , ``Model.NativeWordArithmetic.addWords_eq_add
          , ``Model.NativeWordArithmetic.subWords_eq_sub
          , ``Model.NativeWordArithmetic.mulWords_eq_mul
          , ``Model.NativeWordArithmetic.divWords_eq_div
          , ``Model.NativeWordArithmetic.sqrtWord_eq_sqrt
          , ``Model.NativeWordArithmetic.fmaWords_eq_fma
          , ``Configured.NativeCode.toModel_pack
          , ``Configured.Backend.storedNativeWordAdd_eq_spec
          , ``Configured.Backend.storedNativeWordSub_eq_spec
          , ``Configured.Backend.storedNativeWordMul_eq_spec
          , ``Configured.Backend.storedNativeWordDiv_eq_spec
          , ``Configured.Backend.storedNativeWordSqrt_eq_spec
          , ``Configured.Backend.storedNativeWordFma_eq_spec
          ]
        applicability :=
          if bits ≤ 64 then
            .verifiedForType
          else
            .unavailable
              "formats wider than 64 bits require the next fixed-limb execution tier"
        scope :=
          "built-in statically packed carriers through 64 bits; division uses the same width-generic quotient-prefix theorem as arbitrary-width posits after direct packed decoding; square root and the remaining arithmetic kernels retain their proved packed implementations, while direct operand decoding, code-level sign restoration, result-code packing, capacity-directed scalar or two-limb intermediates, and the fixed UInt64 entry points are proved equal to the common exact model" }
    , { topic := "proved direct packed-pair decoding, rounding, and arithmetic"
        declarations :=
          [ ``Model.NativeLimb.isZero_eq_true_iff
          , ``Model.NativeLimb.bitAt_eq_testBit
          , ``Model.NativeLimb.lowBits_toNat
          , ``Model.NativeLimb.countLeadingZeros_eq_model
          , ``Model.NativeLimb.countLeadingRun_eq_model
          , ``Model.NativeLimb.toDyadic?_eq_model
          , ``Model.NativeLimbRounding.roundPositiveCode_eq_direct
          , ``Model.NativeLimbRounding.roundCodeNat_eq_direct
          , ``Model.NativeLimbRounding.roundCodeNat_lt_modulus
          , ``Model.NativeLimbRounding.ofNatBits_roundCodeNat
          , ``Model.NativeLimbPacked.addCode_lt_modulus
          , ``Model.NativeLimbPacked.subCode_lt_modulus
          , ``Model.NativeLimbPacked.mulCode_lt_modulus
          , ``Model.NativeLimbPacked.sqrtCode_lt_modulus
          , ``Model.NativeLimbPacked.fmaCode_lt_modulus
          , ``Model.NativeLimbPacked.ofNatBits_addCode_eq_add
          , ``Model.NativeLimbPacked.ofNatBits_subCode_eq_sub
          , ``Model.NativeLimbPacked.ofNatBits_mulCode_eq_mul
          , ``Model.NativeLimbPacked.ofNatBits_sqrtCode_eq_sqrt
          , ``Model.NativeLimbPacked.ofNatBits_fmaCode_eq_fma
          , ``Configured.PairCode.toModel_pack
          , ``Configured.Backend.storedNativeLimbAdd_eq_spec
          , ``Configured.Backend.storedNativeLimbSub_eq_spec
          , ``Configured.Backend.storedNativeLimbMul_eq_spec
          , ``Configured.Backend.storedNativeLimbDiv_eq_spec
          , ``Configured.Backend.storedNativeLimbSqrt_eq_spec
          , ``Configured.Backend.storedNativeLimbFma_eq_spec
          ]
        applicability :=
          if 65 ≤ bits ∧ bits ≤ 128 then
            .verifiedForType
          else
            .unavailable
              "the public fixed two-limb storage tier applies exactly from 65 through 128 bits"
        scope :=
          "built-in pair storage from 65 through 128 bits; regime and value decoding agree with the exact model; addition, subtraction, multiplication, and FMA use proved packed kernels; division and square root combine pair decoding with the generic quotient-prefix and square-root rounders" }
    , { topic := "current-standard exact quire representation and semantics"
        declarations :=
          [ ``Quire.Model.eq_nar_iff_coefficient_eq_min
          , ``Quire.Model.ordinaryCoefficient_iff_isNaR_eq_false
          , ``Quire.Model.toRat?_eq_toDyadic?_map
          , ``Quire.Model.toRat?_eq_none_iff
          , ``Quire.Model.toReal?_eq_none_iff
          , ``Quire.Model.toProjectiveRatLine_eq_nar_iff
          , ``Quire.Model.toProjectiveRealLine_eq_nar_iff
          ]
        definitions := [``Quire.width, ``Quire.scaleExponent]
        applicability := .verifiedForType
        scope :=
          "the standard 16n-bit quire at every valid static width; ordinary words are exact signed integer multiples of 2^(16-8n), and the reserved minimum word alone is quire NaR" }
    , { topic := "current-standard quire execution and refinement"
        declarations := Quire.FloatInfo.executionDeclarations
        applicability := .verifiedForType
        scope :=
          "integer/dyadic execution at every valid static width; pToQ globally preserves exact optional rational meaning without overflow, qToP globally equals standard rational rounding, and accumulation refinements state the exact ordinary-result conditions under which a longer accumulation does not overflow to quire NaR"
        numericalGuarantee? := some {
          kinds := [.range, .rounding, .exactness]
          statement :=
            "Quire conversion and accumulation preserve exact rational meaning while the proved capacity condition prevents NaR; qToP performs one final standard posit rounding." } }
    ]
  nonclaims :=
    [ "the optional projective view gives NaR a signed or ordered infinity meaning"
    , "an independent second mechanization of the English Posit Standard exists against which roundRat has been proved"
    , "the six core arithmetic operations are available unless their capability status below says verified"
    , "SoftPosit, hardware, compiler lowering, MPFR, or an FFI lies inside these certificates"
    ]

end FloatLib.Floats.Formats.Posit.FloatInfo

namespace FloatLib.Floats.Formats.Posit.FloatInfo.Command

open Lean Elab Command Meta
open FloatLib.Floats.ExecFloat

/-- Recover the posit descriptor and storage plan from a configured family. -/
private meta def configuredFormatPlan? (family : Expr) : Option (Expr × Expr) :=
  if family.isAppOfArity ``Configured.Family 3 then
    some (family.getAppArgs[0]!, family.getAppArgs[2]!)
  else
    none

/-- Describe the carrier specified by the storage plan. -/
private meta def readStorage (plan : Expr) : MetaM String := do
  let plan ← withTransparency .all <| whnf plan
  let constructor := plan.getAppFn
  if constructor.isConstOf ``Configured.StoragePlan.byte then
    return "UInt8 with erased range evidence, selected automatically"
  if constructor.isConstOf ``Configured.StoragePlan.word16 then
    return "UInt16 with erased range evidence, selected automatically"
  if constructor.isConstOf ``Configured.StoragePlan.word32 then
    return "UInt32 with erased range evidence, selected automatically"
  if constructor.isConstOf ``Configured.StoragePlan.word64 then
    return "UInt64 with erased range evidence, selected automatically"
  if constructor.isConstOf ``Configured.StoragePlan.pair then
    return "two fixed UInt64 limbs with erased range evidence, selected automatically"
  if constructor.isConstOf ``Configured.StoragePlan.wide then
    return "exact-width BitVec proof model; additional fixed-limb tiers pending"
  throwError "failed to inspect posit storage plan"

/--
Width-generic certified operations available directly on the posit proof model.

These remain separate from universal `ExecFloat` capabilities because the raw model deliberately
has no configured storage plan or capability-selection dictionary.
-/
private meta def modelOperations : List InfoEntry :=
  [ ⟨"add",
      "`Model.DirectDyadicArithmetic.add`; exact dyadic addition and proved direct packing"⟩
  , ⟨"sub",
      "`Model.DirectDyadicArithmetic.sub`; exact dyadic subtraction and proved direct packing"⟩
  , ⟨"mul",
      "`Model.DirectDyadicArithmetic.mul`; exact integer product and proved direct packing"⟩
  , ⟨"div",
      "`Model.DirectDyadicArithmetic.div`; destination-width quotient prefix with exact remainder rounding"⟩
  , ⟨"sqrt",
      "`Model.DirectDyadicArithmetic.sqrt`; destination-width integer-root prefix with exact square-remainder rounding"⟩
  , ⟨"fma",
      "`Model.DirectDyadicArithmetic.fma`; exact product-plus-addend with one final rounding"⟩
  ]

open FloatLib.Floats.ExecFloat in
elab_rules : command
  | `(#float_info%$tk $type:term) =>
      FloatLib.Floats.ExecFloat.FloatInfo.Command.withElaboratedType
          type fun typeExpr => do
        match ← Inspection.execFamily? typeExpr with
        | some family => do
            let family ← withTransparency .all <| whnf family
            let some (format, plan) := configuredFormatPlan? family
              | throwUnsupportedSyntax
            let bits ←
              Inspection.readNatProjection "posit descriptor" ``Format.bits format
            let storage ← readStorage plan
            let operations ← Inspection.coreOperations family
            let selectedBackends ← Inspection.selectedBackends family
            let profile := FloatInfo.profile bits storage
            let profile :=
              { profile with execution := profile.execution ++ selectedBackends }
            logInfoAt tk <| ← Inspection.renderProfile profile typeExpr operations
        | none => do
            let some arguments ←
                unfoldUntilAppArgs? ``FloatLib.Floats.Formats.Posit.Model 1 typeExpr
              | throwUnsupportedSyntax
            let bits ←
              Inspection.readNatProjection
                "posit descriptor" ``Format.bits arguments[0]!
            let profile := FloatInfo.profile bits s!"BitVec {bits} descriptor-indexed proof carrier"
            let profile :=
              { profile with
                execution :=
                  [ ⟨"carrier",
                      s!"BitVec {bits}; the descriptor-indexed proof model"⟩
                  , ⟨"purpose",
                      "specification, conformance vectors, and width-generic backend refinement"⟩
                  , ⟨"arithmetic",
                      "exact dyadic/integer kernels with direct result construction and proved nearest-even rounding"⟩
                  , ⟨"dispatch",
                      "explicit family operations; no configured storage planner or universal capability dictionary"⟩
                  ]
                specializedOperations := modelOperations }
            logInfoAt tk <| ← Inspection.renderProfile profile typeExpr .none

end FloatLib.Floats.Formats.Posit.FloatInfo.Command
