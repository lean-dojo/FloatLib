# Theorem index

We've collected FloatLib's major theorems here: agreement between executable arithmetic and its
specification, rounding and error bounds, exact conversions, and results for each format family.
Each table pairs the Lean names with a short statement of what we prove, and the imports you need
sit beside their tables. Proofs about individual algorithms live alongside their kernels.

For example, you can ask Lean for the full statement of the binary addition theorem with `#check`:

```lean
import FloatLib.Floats.Formats.BinaryInterchange.Semantics

#check FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt
```

We put the family and model in the namespace and let the theorem name describe its conclusion, so
once you open that namespace, applications stay short. Each full Lean statement includes the
finiteness, range, and encoding assumptions its result needs.

## Format-independent executable operations

Import `FloatLib.Floats.ExecFloat`.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Proof.add_eq_spec` | Executable addition is exactly the format's reference addition. |
| `ExecFloat.Proof.sub_eq_spec` | Executable subtraction is exactly the format's reference subtraction. |
| `ExecFloat.Proof.mul_eq_spec` | Executable multiplication is exactly the format's reference multiplication. |
| `ExecFloat.Proof.div_eq_spec` | Executable division is exactly the format's reference division. |
| `ExecFloat.Proof.sqrt_eq_spec` | Executable square root is exactly the format's reference square root. |
| `ExecFloat.Proof.fma_eq_spec` | Executable fused multiply-add is exactly the format's reference fused operation, with one final rounding. |
| `ExecFloat.Proof.add_notation_eq_spec`, `sub_notation_eq_spec`, `mul_notation_eq_spec`, `div_notation_eq_spec` | The same equations stated for `x + y`, `x - y`, `x * y`, and `x / y`. Notation elaborates to `HAdd.hAdd` and its siblings, so `rw`, `simp`, and `grind` need these forms to match it. |

These lemmas connect the arithmetic we write in a program to the reference operation we use in a
proof. For `+`, `-`, `*`, and `/` they apply to ordinary notation as written, with no `change` or
unfolding step. Each format supplies its own reference operation, and its refinement theorems give
that operation a numerical meaning (with real-valued results where the format supports them).

For casts and mixed-format operations, `ExecFloat.spec_cast` and
`ExecFloat.Mixed.preparedSpec_add`, `preparedSpec_sub`, `preparedSpec_mul`, `preparedSpec_div`, and
`preparedSpec_fma` state that exact decoding followed by one destination quantization satisfies the
destination's `Quantizer.spec` relation. The relation holds in
`RoundingModes.withMode mode context`, the quantizer context with the call's rounding direction
and the policies of `context`, which has no direction of its own. To use these results by name,
import `FloatLib.Floats.ExecFloat.Conversion.Proof`.

Each destination's contract gives the numerical meaning of a conversion next to its complete
outcome. For a conventional IEEE binary descriptor, nearest-even conversion with native overflow and
gradual underflow selects a nearest finite value whenever the result is finite, and
`ExecFloat.Binary.Conversion.nearestFinite_of_spec` extracts that property from a successful
configured conversion. For every context, the shared `ExecFloat.Binary.Conversion.specWith` also
determines the complete word and status, by equality with the reference `runWith`. Its
runtime-free nearest-value clause says nothing about other policies, tie selection, zero signs, or
overflow to infinity, which only that equality fixes. Some of them have an independent statement
elsewhere: the real value of a finite nearest-even result is the descriptor's `roundAt`, and
`ExecFloat.Binary.Conversion.runWith_nearest_of_abs_le_posMaxFinite` shows the result is finite
whenever the exact magnitude is at most the largest finite value.

What the numerical clauses say depends on the destination:

| Destination | What its conversion contract exposes |
| --- | --- |
| IEEE binary | Distance to the input is no greater than that of any finite destination value, under the conditions above. |
| Posit | The decoded result equals real posit rounding, including minPos and maxPos behavior. |
| P3109 | The decoded datum equals the selected round-then-saturate projection; a separate word equality preserves payload details. |
| Fixed point | The nearest-even coefficient has at most half a unit of error and is even at a tie. |
| Bounded fixed point | The nearest-even coefficient is preserved or rejected when range-checked, reduced modulo `2^width` to its signed representative when wrapped, or clamped when saturated. |

Every family keeps the complete status and failure outcome, and the `spec_iff_eq_run` theorems (with
binary's `specWith_iff_eq_runWith`) show that the numerical clauses still determine exactly one
complete executable outcome.

For rewriting a concrete binary conversion, `ExecFloat.Binary.Conversion.run_default_finite` reduces
a default-context finite conversion to `Model.roundRat`, and
`ExecFloat.Binary.Conversion.cast_eq_roundRat_of_decodeTo_eq_finite` does the same for a `cast`
whose source decodes to a finite value. From there, `Model.Policy.roundRat_nearest_eq_execFloat` in
`Rounding/Policy/Proof.lean` identifies the policy rounder with `Model.roundRat`, and
`Model.toReal_roundRatScaled_eq_roundAt` in
`DirectedSemantics/Rational/RoundingSemantics/Executable.lean`, together with the `cast_eq_roundAt`
family, gives `Model.roundRat` its real-number semantics. Each of the other formats develops its own
rounding and projection theorems in its section.

Non-IEEE NaN encodings have diagnostic payload zero, because their reserved fraction bits are
encoding markers. `Model.ExactValue` and external NaN text keep the complete stored fraction field,
while `Model.nanPayload`, numerical observations, checked integer failures, and cross-format casts
use the diagnostic payload. IEEE NaNs keep every payload bit below the quiet bit.

For NaN sources, `ExecFloat.Binary.Conversion.run_default_decode_of_isNaN` shows that the default
conversion returns the value and invalid flag of `Model.cast` with `status := true`. An IEEE
destination keeps the sign and any payload that fits, and an oversized payload becomes zero.
Maximum-NaN encodings keep only the sign, while FNUZ has a single NaN. A signaling source raises
invalid (IEEE 754-2019 §6.2.3, §7.2). That theorem needs a destination with a NaN encoding. For a
fully finite destination, `run_default_decode_of_isNaN_of_encoding_finite` shows that the conversion
fails with the source NaN as `.exceptional .source`, while `Model.cast` delivers positive zero and
raises invalid (`Model.cast_invalid_of_isNaN_of_encoding_finite`, whose carrier-generic form is
`runWith_default_nan_of_encoding_finite`). Both paths treat the conversion as invalid. `ExecFloat`
just refuses to invent a value. `ExecFloat.Binary.Conversion.decode_of_isNaN` gives the NaN
observation that a configured NaN decodes to.

On the complete packed result, the policy engine and the directed engine agree:
`Model.Policy.roundDyadicGeneral_toRoundingMode` in `Rounding/Policy/Agreement.lean` covers every
`FloatFormat`, all six `IEEERoundingMode` values, both signs, and every exact dyadic input. Its
nearest-away case is `Model.Policy.roundDyadicGeneral_nearestAway_eq_roundDyadicNearestAway` in
`Rounding/Policy/NearestAwayAgreement.lean`. Because `Policy.roundDyadic` sends all six directions
with native overflow and gradual underflow to the dyadic rounders, the agreement says that this
dispatch changes no result. We keep these proofs outside `Rounding/Policy/Proof.lean`, so a program
that needs only the policy rounder doesn't compile the extra arguments connecting the engines.

Every binary destination uses `Numerics.SignedRat` as its exact domain: a rational with an IEEE sign
bit. A cast or mixed-format operation carries that sign to the destination's encoding policy.
`ExecFloat.Binary.Conversion.run_default_negZero_value?` states that converting an exact `-0` into a
binary destination delivers its `zero true`, and a destination with only unsigned zero maps this to
positive zero. Among the `SignedRat` arithmetic lemmas, `SignedRat.value_add`, `value_sub`,
`value_mul`, `value_div`, and `value_neg` say that the rational part is ordinary rational
arithmetic, while `negative_mul`, `negative_div`, `negative_add_of_eq_zero`, and
`negative_add_of_ne_zero` state the IEEE sign rules. An exact zero sum is negative only when both
operands are negative, which is the round-to-nearest rule. Sources whose exact domain is `Rat` enter
through `ExactMap.run_ratToSignedRat`, and binary sources decode through `SignedRat.ofDyadic`, which
keeps the dyadic sign (`SignedRat.negative_ofDyadic`). A binary `Model` value decodes the same way
(`ExecFloat.Binary.Conversion.modelDecoder_run`), and
`ExecFloat.Binary.Conversion.convert_model_eq_cast_ofModel` shows that converting it gives the
outcome of casting the configured value that stores it.

For a longer finite algebraic calculation, `ExecFloat.ConversionProof.preparedSpec_roundOnce` states
that successful exact evaluation is followed by a single destination quantization, in its `context`
with the direction of its `mode`. `ExactExpression.div_zero` and `div_of_not_is_zero`
expose the checked-division boundary. Each exact domain gets one decidable zero predicate from the
`ExactZero` capability, and that predicate includes canonical `0`. For `SignedRat`, the bridge
theorems identify it with `value = 0`, so both signed zeros are recognized. The three
`ExactExpression.operand_eq_*` theorems state how finite, infinite, and exceptional operands enter
the expression.

Posit integer functions and conversions reuse the shared exact rational-to-integer rounder in
`FloatLib.Numerics.Quantization.Deterministic.Rational`, so they don't maintain separate tie rules.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.roundRatEven_nearest` | The rounded integer is at least as close as every other integer. |
| `Numerics.roundRatEven_error_le_half` | Its absolute error is at most one half. |
| `Numerics.roundRatEven_eq_of_error_lt_half` | A candidate strictly within half a unit is the unique rounded result. |
| `Numerics.roundRatEven_half_step` | Every half-integer, positive or negative, rounds to its even neighbor. |
| `Numerics.roundRatEven_eq_floor_ceil` | Quotient-based execution equals the floor/ceiling distance-and-parity decision for every rational. |

## Exact comparisons with rational powers

Import `FloatLib.Numerics.Exact`. These comparators decide how an exact real value compares
with a rational boundary, including equality, so a format can round the value once.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.RationalPower.exactRoot?_spec` | For a positive base, a descriptor gives `base ^ exponent` as an integer power of a rational root, and no descriptor means the power is irrational. |
| `Numerics.RationalPower.powEq_iff` | For a positive base, the exact test decides `base ^ exponent = target`, at a cost polynomial in the bit lengths of the base, the exponent and the target. |
| `Numerics.RationalPower.cappedPow?_eq`, `Numerics.RationalPower.natPowEq_iff` | For `b ≥ 1`, capped exponentiation returns `b ^ e` exactly when it is at most the cap. The equality test built on it decides `b ^ e = t` for every `b`. |
| `Numerics.RationalPower.ExactRoot.toDyadic?_spec`, `Numerics.RationalPower.ExactRoot.ne_of_toDyadic?_eq_none` | For a positive root, a dyadic built from a descriptor denotes the described power, with a significand below `2 ^ (p + 3)`; when none is built, the power is no such dyadic. |
| `Numerics.RationalPower.compare_eq_real` | The comparator returns the ordering of `base ^ exponent` and the target for every nonnegative base. |
| `Numerics.compareReciprocal_eq_real` | Given an exact comparator for a nonzero real, the adapter compares its reciprocal. |
| `Numerics.cmp_sub_eq_cmp_add` | Comparing `x - c` with `b` is comparing `x` with `b + c`, which is how the `Minus1` operations shift their boundaries. |
| `Numerics.TrigonometricComparison.prepareAtan2_neg_one_eq_real` | The argument comparator at `(-1, 0)` compares π. |

We describe a rational power by its root and build its exact value only when it can be a cell
boundary. Take the binary64 power `0x1.0000008000001p+0 ^ 17179869184.5`: it is about `2^738.66`,
but its odd significand has about `8.9 * 10^11` bits. Capped exponentiation decides equality with a
boundary at a cost polynomial in the bit lengths of the base, the exponent and the boundary, not in
the exponent's magnitude. Logarithm enclosures of increasing degree separate every other boundary,
and the search ends because the logarithm difference is then nonzero.

## Binary interchange formats

Import `FloatLib.Floats.Formats.BinaryInterchange.Semantics`. The names below are in
`FloatLib.Floats.Formats.BinaryInterchange.Model`.

### Finite real semantics

| Theorem | Informal statement |
| --- | --- |
| `toReal_add_eq_roundAt` | IEEE addition whose executable sum is finite is the exact real sum rounded once to the format. |
| `toReal_sub_eq_roundAt` | IEEE subtraction whose executable difference is finite is the exact real difference rounded once. |
| `toReal_mul_eq_roundAt` | IEEE multiplication whose executable product is finite is the exact real product rounded once. |
| `toReal_div_eq_roundAt` | Division by a finite value, when the executable quotient is finite, is the exact real quotient rounded once. |
| `toReal_fma_eq_roundAt` | Fused multiply-add whose executable result is finite forms the exact product-plus-addend and rounds once. |
| `isFinite_of_isFinite_add`, `isFinite_of_isFinite_sub`, `isFinite_of_isFinite_mul`, `isFinite_of_isFinite_fma`, `isFinite_left_of_isFinite_div`, `isZero_eq_false_of_isFinite_div` | A finite IEEE result has finite operands; a finite quotient has a finite dividend and a nonzero divisor. |
| `toReal_sqrt_eq_roundAt` | A finite nonnegative square root, including both signed zeros, is the exact real square root rounded once; no result-finiteness premise is needed. |
| `isFinite_sqrt_of_isFinite` | The square root of a finite nonnegative IEEE value never overflows. |
| `toReal_add_of_isZero_left`, `toReal_sub_of_isZero_left`, `toReal_sub_self`, `toReal_mul_of_isZero_left`, `toReal_mul_of_abs_toReal_eq_one_left`, `toReal_div_of_abs_toReal_eq_one_right`, `toReal_sqrt_of_isZero` | Sums and differences with a zero, products with a zero or with a value of magnitude one, quotients by a value of magnitude one and the square root of a zero are exact, and `x - x` of a finite `x` is exactly zero. The other operand is finite. The `_right` variants take the special operand second, and the square root needs no IEEE premise. |
| `toRat?_add_of_representable`, `toRat?_sub_of_representable`, `toRat?_mul_of_representable` | A sum, difference or product of values that decode to `p` and `q`, whose exact value is the decoded value of some encoding, decodes to that exact value. |
| `toRat?_sub_self`, `toRat?_add_of_toRat?_eq_some_zero_left`, `toRat?_mul_of_toRat?_eq_some_zero_left`, `toRat?_mul_of_abs_eq_one_left` | For a finite `x`, `x - x` decodes to `some 0`. When the other operand decodes to `p`, adding a value that decodes to zero and multiplying by a value that decodes to `1` or `-1` are exact, and a product of a finite value with one that decodes to zero decodes to `some 0`. The `_right` variants take the special operand second. |
| `Algebraic.toReal_of_toRat?_eq_some`, `Algebraic.isFinite_of_toRat?_eq_some`, `Algebraic.exists_toRat?_of_isFinite`, `Algebraic.toRat?_eq_some_of_toReal_eq` | `toRat?` succeeds exactly on finite values, and the rational it returns is the real value. |

The `toReal_*_eq_roundAt` theorems assume a conventional IEEE descriptor and the finiteness conditions
a real-valued interpretation needs. The decoding facts in the last row hold in every encoding, and the
`toRat?` exactness results derive finiteness from successful decodes. For addition, subtraction, multiplication, division, and fused multiply-add,
the finiteness of the executable result is a named hypothesis (`hfin` or `hout`). It excludes
overflow, which has no value in `ℝ`, and it's decidable on the result. It also forces finite
operands, so only division, where a finite value over an infinity is a finite zero, asks for a
finite divisor. Variants named
`*_of_abs_*_le_posMaxFinite` replace it by a symbolic bound on the operands. Square root is the
exception, since `isFinite_sqrt_of_isFinite` shows it cannot overflow. NaNs, infinities, invalid
operations, and the signs of zeros are all described by the executable specification as well, and
equality over `ℝ` alone can't express those distinctions.

To get the result-finiteness premise from a symbolic magnitude bound, use the corresponding
`isFinite_*_of_abs_*_le_posMaxFinite` lemmas. That's usually easier than evaluating the output
first.

### Real rounding in every direction

`roundAt fmt x (mode := m)` rounds a real onto the grid of `fmt` in any `IEEERoundingMode`,
nearest-even by default, with gradual underflow and no upper exponent bound. For nearest-even and
the two infinity directions it unfolds to Flocq's `round` with `nearestEven`, `ceilRound`, and
`floorRound`. Nearest-away rounding is Flocq's `nearestChoice nearestAwayChoice` and rounding away
from zero is `awayRound`.

| Theorem | Informal statement |
| --- | --- |
| `roundAt_eq_round` | Every direction is Flocq's rounding with the direction's integer rule, `Flocq.roundingFunction mode`. |
| `roundAt_towardZero` | Toward zero truncates the scaled mantissa. |
| `roundAt_nearestAway`, `roundAt_away` | Nearest-away rounding rounds the scaled mantissa to nearest with ties away from zero, and away-from-zero rounding rounds it away from zero. |
| `roundAt_zero`, `roundAt_one`, `roundAt_mono`, `genericFormat_roundAt`, `roundAt_of_genericFormat` | Every direction fixes zero and one, is monotone, returns a grid value, and fixes grid values. |
| `roundAt_neg` | Rounding `-x` gives the negation of rounding `x` in `mode.negate`, which exchanges the two infinity directions. |
| `roundAt_of_nonneg` | On a nonnegative input a directed mode, one of the four besides the two nearest modes, is upward rounding when `mode.roundsAwayFromZero false` holds and downward rounding otherwise. |
| `roundAt_eq_of_scaledBracket` | Two inputs with the same canonical exponent, whose scaled mantissas have the same integer bracket and location, round alike in every direction. |
| `Policy.overflowRoundsMagnitudeUp_toRoundingMode` | The policy engine carries an overflow upward under an embedded IEEE mode exactly when `IEEERoundingMode.overflowRoundsMagnitudeUp` says so. |

`IEEERoundingMode.roundsAwayFromZero` is the directed magnitude-up predicate, false for both nearest
modes and true for every sign under rounding away from zero. `IEEERoundingMode.zeroSumSign` is the
IEEE sign of an exactly cancelling sum, positive except toward negative infinity, also under
rounding away from zero as in MPFR. `zeroForExactSum` passes it to `zero`, which keeps a negative
sign only in formats with a signed zero. The policy-aware finite operations take the same sign from
`Policy.zeroSumSign`, which agrees with it on every IEEE direction
(`Policy.zeroSumSign_toRoundingMode`) and gives stochastic rounding the nearest sign.
`addFinite?_eq_zero_of_toRat_add_eq_zero`, `fmaFinite?_eq_zero_of_toRat_add_eq_zero`, and
`mulAddFinite?_eq_zero_of_toRat_add_eq_zero` state the cancelled zero under every policy, and
`Policy.roundDyadic_significand_zero` says that every policy rounds an exact zero to the zero of
its sign.

Policy-aware finite division rounds a numerator and denominator whose signed quotient is the exact
rational quotient (`divValue_eq_quantizedRatValue`). Under nearest-even rounding in an IEEE format
a finite result is `roundAt` of the real quotient (`toReal_divFinite?_nearest`), and a zero dividend
gives the zero signed by the exclusive or of the operand signs under every policy
(`divFinite?_eq_zero_of_toRat_eq_zero`).

### Rounding rules and nearest-away rounding

`Numerics.MagnitudeRounding` names the four ways of rounding a nonnegative quotient: `down`, `up`,
`nearestEven`, and `nearestAway`. `MagnitudeRounding.increment` decides each from the least retained
bit, the guard bit, and the sticky bit. `Numerics.roundShiftRight` applies a rule to a division by a
power of two and `Numerics.roundQuotient` to any division, and their nearest-even versions are
`roundShiftRightEven` and `roundQuotientEven`. `Numerics.shiftRightCeil` and `roundQuotient .up` are
the shared ceilings of the dyadic and rational rounders. With a zero denominator, `down`, `up`, and
`nearestAway` return `0`, while nearest-even keeps the convention of `roundQuotientEven`.
`IEEERoundingMode.magnitudeRounding` gives the rule that a direction applies to a result of known
sign.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.roundShiftRight_eq_guard_sticky` | For a positive shift, every rule is the truncated quotient plus its increment decision on the three rounding bits. |
| `Numerics.roundShiftRight_shiftRightJam` | Jamming the bits below position `j` into one sticky bit does not change a rounding by at least `j + 2` bits, under every rule. |
| `Numerics.roundShiftRight_eq_roundQuotient` | Shift rounding under every rule is quotient rounding by the corresponding power of two. |
| `Numerics.roundShiftRight_nearestAway_eq`, `Numerics.roundQuotient_nearestAway_eq` | Nearest-away rounding is nearest-even rounding with an exact tie sent to the ceiling. |
| `Numerics.roundQuotient_nearestAway_eq_div_add`, `Numerics.lt_roundQuotient_nearestAway_iff` | Nearest-away quotient rounding increments exactly when twice the remainder reaches the denominator. |
| `Numerics.compare_roundShiftRight_mul_two_pow`, `Numerics.compare_roundShiftRight_mul_two_pow_signed` | A rounding is exact exactly when no guard or sticky bit is set; otherwise the delivered value is above the exact one exactly when the increment decision differs from the sign. |
| `Numerics.two_mul_mod_eq_iff_of_mul_eq`, `Model.two_mul_mod_eq_iff_of_rat_eq` | Whether a quotient is an exact tie depends only on the rational it represents. |
| `Model.dyadicIsGridTie_eq_true_iff`, `Model.dyadicIsGridTie_eq_false_of_far_below` | A dyadic is a grid tie when its bits below the grid spacing are one half of it; no value below half the least subnormal is a tie. |
| `Model.Policy.roundDyadicGeneral_nearestAway_eq_roundDyadicNearestAway` | The general policy engine with nearest-away rounding, native overflow, and gradual underflow is `roundDyadicNearestAway` on every descriptor, including signed zero and the overflow midpoint. |
| `Model.Policy.roundRatGeneralOfDenNeZero_congr_rounding` | Two rounding modes give the same engine result when they agree on the overflow direction, on the decision below half the least subnormal, and at the one quotient the engine rounds. |
| `Model.rationalNearestAwayOverflowsScaled_eq_true_iff`, `Model.rationalIsTinyAfterRoundingScaled_nearest_eq` | For a rational `n / d` with `d ≠ 0` and no further binary scale, nearest-away overflow is reaching the top finite midpoint, and nearest tininess is a tiny result or a magnitude below `underflowMidpoint`. |
| `Model.Policy.isTinyAfterRounding_roundRatGeneralOfDenNeZero_nearestAway_eq_false` | At or above `underflowMidpoint` the nearest-away engine never delivers a tiny result, under every overflow and underflow policy. |
| `ExecFloat.Binary.Conversion.finiteStatus_of_nearestAway` | The status of a nearest-away conversion is the status built from those two classifiers, under every overflow and underflow policy. |
| `ExecFloat.Binary.Conversion.roundedSignificandStatus_nearestAway` | For nearest-away rounding of every nonzero rational, the significand-based status calculation that `finiteStatus` uses for stochastic rounding matches the nearest-away overflow classifier and the comparison with `underflowMidpoint`. |
| `ExecFloat.Binary.Conversion.finiteStatus_eq_roundedSignificandStatus_of_nearestAway` | For the value that `Policy.roundRat` delivers, the status of a nearest-away conversion equals the status assembled from that significand-based calculation, under every overflow and underflow policy. |

`Model.roundDyadicAway` rounds a magnitude up, as MPFR's `MPFR_RNDA` does.
`Model.roundDyadicNearestAway` is IEEE 754-2019 `roundTiesToAway`: `roundDyadic` off a grid tie and
`roundDyadicAway` at one, which `Model.dyadicIsGridTie` detects on the grid with gradual underflow
and no upper exponent bound. `Model.rationalIsGridTieScaled` and `Model.roundRatNearestAwayScaled`
are the rational versions. Our policy regression suite compares the rational rounder with the
general engine and the rational tie test with `dyadicIsGridTie` at denominator one.
`Model.dyadicNearestAwayOverflows` and `Model.rationalNearestAwayOverflowsScaled` classify overflow
at the top finite midpoint, which overflows under nearest-away whatever the parity of the largest
finite significand. Tininess for nearest-away uses the nearest-even boundary `underflowMidpoint`,
because both nearest rules round that midpoint up to the smallest normal value.

### The nearest-away and away-from-zero directions

`IEEERoundingMode` has six constructors: the five rounding-direction attributes of IEEE 754-2019,
with `nearestAway` (roundTiesToAway) after `nearest`, and `away` (MPFR's `MPFR_RNDA`, not an IEEE
attribute) last. `Numerics.RoundingMode` has `away` as well, and `Policy.ieeeRoundingMode?` maps
`nearestAway` and `away`, so `Policy.roundDyadic` and the conversion status `finiteStatus` treat
them as directions. Every operation that takes a rounding direction accepts them: arithmetic,
square root, casts, reductions, integral rounding, integer conversion, and text input and output.
Nearest-away square root uses the nearest-even square root, because the square root of a value of
a format is never a tie of its grid, as `Model.Internal.Directed.sqrt` explains. No theorem states
that fact.

| Theorem | Informal statement |
| --- | --- |
| `Model.dyadicIsGridTie_eq_false_of_eq_mul_pow2` | A representable dyadic is never a grid tie, so `Internal.Directed.roundDyadic_of_eq_mul_pow2` fixes it in all six directions. |
| `Model.roundDyadicToInt_nearestAway`, `Model.roundDyadicToInt_away` | Integer rounding with ties away from zero is `nearestChoice nearestAwayChoice` of the exact value, and rounding away from zero takes the ceiling of a nonnegative value and the floor of a negative one. |
| `Model.toReal_roundToIntegral_nearestAway`, `Model.toReal_roundToIntegral_away` | For an IEEE descriptor whose exponent range reaches its precision, `roundToIntegral` denotes those integers. |
| `ExecFloat.Binary.Conversion.finiteStatus_of_ieeeRoundingMode?_eq_some` | A conversion whose rounding mode has an `IEEERoundingMode` direction reports the overflow and tininess of that direction's exact classifiers. |
| `Model.dyadicIsTinyAfterRounding_nearestAway`, `Model.rationalIsTinyAfterRoundingScaled_nearestAway` | Nearest-away rounding detects tininess at the nearest-even boundary. |
| `Model.FiniteQuotientRound.roundAtExponent_eq`, `Model.FiniteQuotientRound.isGridTieAtExponent_eq` | The single-quotient rounder agrees with the exact rational rounder in all six directions; its nearest-away tie test is `rationalIsGridTieScaled`. |
| `Model.Policy.roundQuot_away_eq_roundQuotDirected`, `Model.Policy.overflowResult_native_away` | Policy rounding away from zero takes the ceiling of every quotient and overflows to the native overflow value of either sign. |
| `Model.lt_roundTextMagnitude_nearestAway_iff` | Nearest-away text output of a nonnegative magnitude exceeds a natural bound exactly when the magnitude reaches the bound plus one half. |
| `Model.sqrt_of_isZero` | Square root fixes a finite zero of either sign in every direction. |

### Powers, roots, and hypotenuse

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Algebraic.Proof`. Each `Model` theorem
below has a matching version in `ExecFloat.Binary` that applies to configured values as they are.
Their real statements require a conventional IEEE descriptor, finite operands in the function's
domain, and a finite output.

| Theorem | Informal statement |
| --- | --- |
| `Model.toReal_rsqrt_eq_roundAt` | For a finite input and a finite result, reciprocal square root rounds the exact real reciprocal root once; a finite result already rules out zero and negative inputs. |
| `Model.toReal_hypot_eq_roundAt`, `Model.isFinite_of_isFinite_hypot` | Hypotenuse rounds the root of the exact sum of squares, with no intermediate product rounding; a finite result forces finite operands. |
| `Model.toReal_powInt_eq_roundAt` | A finite base raised to an integer exponent is rounded once, including negative exponents and a zero base. |
| `Model.toReal_rootN_eq_roundAt` | A finite input with a finite root gives the rounded signed real root; the finite result rules out degree zero and even roots of negative values. |
| `ExecFloat.Binary.toModel_rootN`, `toModel_powInt`, `toModel_hypot`, `toModel_rsqrt` | Every storage codec preserves the complete model result, including exceptional encodings. |

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Square` for
`ExecFloat.Binary.square_eq_spec` and `square_eq_mul`: the unary square kernel produces the
same complete result as the certified multiplication specification and selected multiplication
backend. P3109 and posit squaring have corresponding `square_eq_mul` theorems, and
`ExecFloat.Posit.toModel_square` states the configured posit square as `Model.square` for every
built-in storage plan.

### Casting and exact widening

Import `FloatLib.Floats.Formats.BinaryInterchange.Conversion`.

| Theorem | Informal statement |
| --- | --- |
| `cast_self_of_finite` | Casting a finite value to its own format preserves its exact encoding, including signed zero. |
| `cast_eq_roundAt`, `isFinite_of_isFinite_cast` | A finite cast to an IEEE destination is one nearest-even rounding, from any source descriptor including FP8; a finite result forces a finite source. |
| `cast_exact_of_gridExtension` | A finite cast is exact when the IEEE destination contains the source's dyadic grid, for any source encoding. |
| `cast_exact_of_compatibleWidening` | Increasing only fraction width while preserving exponent semantics and encoding is exact. |
| `cast_eq_widenExact_of_compatibleWidening` | Every rounding mode gives the same widened encoding for a finite value with compatible exponent fields and encoding. |
| `isFinite_quietNaN`, `isFinite_canonicalNaN` | Quieting does not change finiteness, and the canonical NaN of an IEEE encoding is not finite. |
| `cast_of_isNaN`, `propagatedNaN_eq_quietNaN` | An IEEE destination quiets the NaN, keeps its sign, and keeps its payload when it fits, otherwise using payload zero (IEEE 754-2019 §6.2.3). Other encodings follow their own NaN rule; a cast to its own format is `quietNaN`. |
| `toReal_widenExact` | The direct widening constructor preserves the decoded real value, including zeros and subnormals. |

`cast_exact_of_gridExtension` is the general theorem behind standard widenings such as binary32 to
binary64. It permits a larger exponent range, so the exponent widths don't have to be equal.

### Accuracy and exact subtraction

Import `FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error`,
`FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel`, or
`FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz` for scalar bounds. Import
`FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof` for the mixed-precision dot and
matrix theorems.

| Theorem | Informal statement |
| --- | --- |
| `roundAt_sub_eq_of_sterbenz`, `roundAt_sub_eq_of_sterbenz_of_same_sign` | Nearby representable values have an exact rounded-real difference, including zero and same-sign negative operands. |
| `toReal_sub_eq_of_sterbenz_of_same_sign` | Same-sign finite IEEE values within a factor of two have the exact executable real difference. |
| `isFinite_sub_of_same_sign` | Same-sign finite IEEE subtraction stays finite, without a factor-of-two premise. |
| `abs_toReal_cast_sub_le`, `cast_exact_mem_Icc`, `toReal_cast_standardModel` | Any source encoding inherits the IEEE destination's half-ULP bound, enclosure and standard error model when the cast result is finite. |
| `cast_refines`, `At.cast`, `At.value_cast` | The general finite-source cast contract also transports proof-indexed values through one destination rounding while retaining the executable carrier. |
| `abs_roundAt_sub_le` | Nearest-even rounding differs from its real input by at most half an ULP. |
| `relativeError_roundAt_le_of_normal` | A nonzero normal-range input satisfies the standard relative-error bound. |
| `abs_toReal_add_sub_le`, `abs_toReal_sub_sub_le`, `abs_toReal_mul_sub_le`, `abs_toReal_div_sub_le`, `abs_toReal_sqrt_sub_le`, `abs_toReal_fma_sub_le` | An IEEE operation with a finite result inherits the half-ULP bound under its domain hypotheses: a finite divisor for division, a finite nonnegative input for square root. |
| `add_exact_mem_Icc`, `sub_exact_mem_Icc`, `mul_exact_mem_Icc`, `div_exact_mem_Icc`, `sqrt_exact_mem_Icc`, `fma_exact_mem_Icc` | Under the same IEEE, domain, and finiteness hypotheses, the exact operation result lies in the computed value's half-ULP enclosure. |
| `roundAt_standardModel` | Nearest-even rounding satisfies the standard model with gradual underflow, `roundAt x = x * (1 + δ) + η` with `\|δ\| ≤ unitRoundoffAt fmt = 2^(-precision)`, `\|η\| ≤ underflowErrorAt fmt = 2^(minSubnormalExponent - 1)`, and `δ * η = 0`, for every real `x`. For binary32 the constants are `2^(-24)` and `2^(-150)`. |
| `round_standardModel_of_nearest` | The same model holds for every nearest rounding function, including ties away from zero. |
| `round_standardModel`, `roundAt_down_standardModel`, `roundAt_up_standardModel`, `round_truncRound_standardModel` | Every valid rounding function, including the directed ones, satisfies the model with both constants doubled. |
| `toReal_mul_standardModel`, `toReal_div_standardModel`, `toReal_sqrt_standardModel`, `toReal_fma_standardModel`, `toReal_cast_standardModel` | An operation on IEEE descriptors with a finite result satisfies the standard model with gradual underflow. Division requires a finite divisor; square root requires a finite nonnegative input, including either signed zero. |
| `roundAt_add_eq_mul_one_add` | The rounded sum of two grid points is `(x + y) * (1 + δ)` with `\|δ\| ≤ unitRoundoffAt fmt` and no underflow term, because a sum below the normal range is exact. |
| `toReal_add_eq_mul_one_add`, `toReal_sub_eq_mul_one_add`, `abs_toReal_add_sub_le_unitRoundoffAt`, `abs_toReal_sub_sub_le_unitRoundoffAt` | For an IEEE descriptor, addition or subtraction with a finite result has relative error at most `unitRoundoffAt fmt`, including subnormal operands and results. |
| `abs_roundAt_sub_le_unitRoundoffAt` | Nearest-even rounding differs from its real input by at most `unitRoundoffAt fmt * \|x\| + underflowErrorAt fmt`. |
| `abs_le_underflowErrorAt_of_roundAt_eq_zero`, `roundAt_pos`, `roundAt_lt_zero` | A real that rounds to zero is at most `underflowErrorAt fmt` in magnitude, so a real above `underflowErrorAt fmt` rounds to a positive value and one below `-underflowErrorAt fmt` to a negative value. |
| `bpow_minSubnormalExponent_le_abs_toReal` | A finite nonzero value is at least the least subnormal `2^minSubnormalExponent` in magnitude. |
| `unitRoundoffAt_eq`, `underflowErrorAt_eq`, `two_mul_unitRoundoffAt`, `two_mul_underflowErrorAt`, `unitRoundoffAt_pos`, `underflowErrorAt_pos` | The standard-model constants are the positive powers of two `2^(-precision)` and `2^(minSubnormalExponent - 1)`; doubling them gives the relative normal spacing and the subnormal spacing. |
| `underflowErrorAt_le_zpow` | The underflow allowance is at most `2^e` for every `e ≥ minSubnormalExponent - 1`. |
| `ulpAt_eq_of_abs_lt_minNormalAt`, `ulpAt_le_of_minNormalAt_le` | Below the normal range one ULP is the subnormal spacing; in the normal range it is at most `2^(1 - precision) * \|x\|`. |
| `mulAccError_eq_site_residuals` | One mixed-precision multiply-accumulate error is exactly the sum of its two input-cast, product, accumulator-cast, and addition residuals. |
| `mulAcc_abs_error_le_budget` | A finite mixed-precision multiply-accumulate is bounded by the corresponding five local half-ULP budgets. |
| `sequentialAccumulator_error_eq_sum` | Sequential accumulation error telescopes exactly into the errors committed at its executed prefix states. |
| `dotSequential_eq_cast_sequentialAccumulator` | The executable sequential dot loop is its prefix accumulator followed by the output cast. |
| `dotSequential_abs_error_le_budget` | A finite executable mixed-precision dot is bounded by all per-step site budgets plus the final output-cast budget. |
| `matmul_refines` | A successful matrix product has the expected row and column shape, and every entry is the corresponding executable sequential dot. |
| `matmul_entry_abs_error_le_budget` | Any selected successful matrix entry inherits the sequential-dot budget without a separate matrix error model. |
| `toReal_sub_eq_of_sterbenz` | Two values with positive real values within a factor of two subtract exactly; their finiteness and result finiteness follow from those hypotheses. |

`roundAt`, `ulpAt`, and `minNormalAt` use the descriptor's declared exponent bias, including FNUZ
and custom encodings, on a grid with no upper exponent bound. `toReal_genericFormat_of_isFinite` and
`roundAt_toReal_eq` apply to every finite decoded word without an IEEE premise. To connect an
arithmetic operation to that grid, you still need its operation-specific refinement hypotheses.

You need the normal range for the relative-error theorem. Near zero, gradual underflow prevents a
uniform relative bound, so absolute error is the useful statement there.

### Mixed relative and absolute error

Import `FloatLib.Numerics.MixedError.Basic` and `FloatLib.Numerics.MixedError.Elementary` for the
format-independent lemmas, and `FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError` for
the binary operations. `MixedError x x₀ r a` states `|x - x₀| ≤ r * |x₀| + a` with
nonnegative `r` and `a`. We write `u = unitRoundoffAt fmt` and `η = underflowErrorAt fmt`.

| Theorem | Informal statement |
| --- | --- |
| `MixedError.trans`, `MixedError.trans_of_abs_sub_le` | A rounding with error `(r, a)` of a value that approximates the exact result with error `(r', a')` has relative error `(1 + r) * r' + r` and absolute error `(1 + r) * a' + a`. |
| `MixedError.of_standardModel`, `Model.mixedError_roundAt` | The standard model `x₀ * (1 + δ) + η` is a mixed error, so nearest-even rounding has error `(u, η)`. |
| `Model.mixedError_roundAt_of_minNormalAt_le`, `Model.mixedError_roundAt_natCast` | In the normal range nearest-even rounding has error `(u, 0)`, and so has the rounding of a natural number, which is zero or at least `minNormalAt fmt`. |
| `MixedError.add_of_mul_nonneg`, `MixedError.sub_of_mul_nonpos`, `MixedError.mul`, `MixedError.div` | Same-sign sums keep the larger relative error, products have relative error `rx + ry + rx * ry`, and a quotient by a value with pure relative error `ry < 1`, whose absolute part is zero, has relative error `(rx + ry) / (1 - ry)`. |
| `MixedError.div_of_le_abs` | A quotient by a value with error `(ry, ay)` whose exact magnitude is at least `m > 0` has the error of `MixedError.div` for the relative error `ry + ay / m`, when that is below one. |
| `MixedError.lower_le`, `MixedError.le_upper`, `MixedError.lower_le_center`, `MixedError.center_le_upper` | The approximation and the exact value both lie in the enclosure `[x₀ - (r * \|x₀\| + a), x₀ + (r * \|x₀\| + a)]`. |
| `MixedError.sqrt`, `MixedError.sqrt_of_le` | The square root of an approximation of a nonnegative exact value keeps the relative error, whatever the sign of the approximation. The absolute error becomes `√a`, or `a / √m` when the exact value is at least `m > 0`. |
| `abs_exp_sub_exp_le`, `MixedError.exp` | `\|exp x - exp x₀\| ≤ (exp \|x - x₀\| - 1) * exp x₀`, so an absolute input error becomes a relative output error. |
| `MixedError.log`, `MixedError.log_one_add`, `MixedError.exp_sub_one` | At a positive exact argument, the logarithm turns a pure relative error `r < 1`, with absolute part zero, into the absolute error `-log (1 - r)`. `log (1 + x)` when the computed and the exact argument are both nonnegative, and `exp x - 1` when both are nonpositive, keep a mixed error unchanged. |
| `abs_log_sub_log_le`, `MixedError.log_one_add_of_le` | The logarithm is `1 / m`-Lipschitz above `m > 0`, so where `1 + x` and `1 + x₀` are at least `m`, `log (1 + x)` of an argument of either sign has absolute error `(r * \|x₀\| + a) / m`. |
| `MixedError.exp_sub_one_of_abs_le` | On `\|x₀\| ≤ c`, `exp x - 1` has relative error `(1 + c) * exp (r * c + a) * r` and absolute error `exp (c + r * c + a) * a`, for arguments of either sign. |
| `MixedError.trans_exp`, `MixedError.trans_log`, `MixedError.trans_log_one_add`, `MixedError.trans_exp_sub_one`, `MixedError.trans_log_one_add_of_le`, `MixedError.trans_exp_sub_one_of_abs_le` | An implementation with mixed error `(u, η)` at its computed argument composes with the error of that argument, under the premises of the propagation lemma it uses: a positive exact argument with a pure relative error below one for `log`, nonnegative computed and exact arguments for `log (1 + x)`, nonpositive ones for `exp x - 1`, the margin `m` of `log_one_add_of_le`, and the bound `c` of `exp_sub_one_of_abs_le`. |
| `Model.mixedError_toReal_add`, `Model.mixedError_toReal_sub`, `Model.mixedError_toReal_add_of_mul_nonneg`, `Model.mixedError_toReal_sub_of_mul_nonpos` | Finite IEEE addition and subtraction add the relative error `u` and no underflow term. A sum of same-sign values keeps a relative bound. |
| `Model.mixedError_toReal_mul`, `Model.mixedError_toReal_div`, `Model.mixedError_toReal_fma`, `Model.mixedError_toReal_sqrt`, `Model.mixedError_toReal_cast` | The other IEEE operations with a finite result propagate their operand errors and add the rounding error `(u, η)` once. Division also needs a finite divisor whose error is purely relative, below one. Square root needs a finite input that is zero or has a clear sign bit, and a nonnegative exact value. A cast needs an IEEE destination and a finite result. |
| `Model.mixedError_toReal_sub_of_sterbenz`, `Model.mixedError_toReal_cast_of_gridExtension`, `Model.mixedError_toReal_cast_of_compatibleWidening`, `Model.mixedError_toReal_neg`, `Model.mixedError_toReal_maximum`, `Model.mixedError_toReal_minimum` | Sterbenz subtraction of finite values of the same sign within a factor of two, a cast with a finite result into a finer grid, a widening cast of a finite value, and negation, `maximum` and `minimum` of finite values do not round and carry only the operand errors. |
| `Model.mixedError_toReal_sub_self` | For a finite `x`, `x - x` is exactly zero, whatever the error of `x`. The other exact cases, such as `Model.toReal_add_of_isZero_left`, `Model.toReal_sub_self` and their decoded forms `Model.toRat?_sub_self` and `Model.toRat?_add_of_representable`, are listed with the finite real semantics. |
| `Model.isFinite_of_mem_scanl_add`, `Model.isFinite_of_mem_finRange_scanl_add` | The operands of a finite sum are finite (`isFinite_of_isFinite_add`), so every partial sum of a finite left-to-right sum is finite, whatever the signs of its terms. |
| `Model.mixedError_toReal_foldl_add`, `Model.mixedError_toReal_foldl_add_of_toReal_eq_zero`, `Model.mixedError_toReal_fin_foldl_add`, `Model.mixedError_toReal_fin_foldl_add_of_toReal_eq_zero` | A finite IEEE left-to-right sum of `n` terms, folded over a list or with `Fin.foldl`, whose seed and terms have nonnegative exact values, relative error `r` and absolute errors `d` and `err i`, has relative error `(1 + u)^n * (1 + r) - 1` and absolute error `(1 + u)^n * (d + Σ err i)`. From a seed of real value zero the first addition is exact, and `n - 1`, in natural subtraction, replaces `n`. |
| `Model.mixedError_toReal_foldl_add_weighted` and its zero-seed and `Fin.foldl` variants | When the seed has a nonnegative exact value and a pure absolute error `d`, and each term has a nonnegative exact value and its own error `(rel i, err i)`, the finite IEEE sum has relative error `(1 + u)^n - 1` and absolute error `(1 + u)^n * (d + Σ (rel i * term₀ i + err i))`, so each relative error is weighted by its own term. |
| `Model.mixedError_toReal_foldl_add_absolute` and its zero-seed and `Fin.foldl` variants | A finite IEEE sum of terms of either sign, from a seed with pure absolute error `d`, has the pure absolute bound `((1 + u)^n - 1) * (\|seed₀\| + Σ \|term₀ i\|) + (1 + u)^n * (d + Σ (rel i * \|term₀ i\| + err i))`. |
| `Model.toRat?_foldl_add_of_eq_zero`, `Model.toRat?_foldl_add_eq_single`, `Model.toRat?_fin_foldl_add_of_eq_zero`, `Model.toRat?_fin_foldl_add_eq_single` | Adding terms that decode to zero keeps the decoded value of the seed. A sum from zero over a list without repeated indices (`l.Nodup`) that contains `j`, whose terms all decode to zero except the one at `j`, decodes to that term whatever its length, so a one-hot sum is exact. `Fin.foldl` visits every index once. |

`ExecFloat.Binary.mixedError_toReal_add` and its siblings in
`FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedError` state the same bounds for `+`,
`-`, `*`, `/`, fused multiply-add, square root, negation, `max`, `min`, and left-to-right sums of
configured values, over a list or with `Fin.foldl`, together with the finiteness of their partial
sums and the exact results stated with `toRat?`. `ExecFloat.Binary.toReal_mul_nonneg` and
`toReal_mul_nonpos` give a configured product the weak sign of its exact product, and
`toReal_mul_lt_zero` gives a product of finite values the strict one when that product is in range
and below `-η`. `ExecFloat.Binary.mixedError_toReal_of_toModel_eq_cast` and its two exact variants
cover every finite configured value that decodes to `Model.cast` of a configured value.

### IEEE status flags

Import `FloatLib.Floats.Formats.BinaryInterchange.Status`.

With `(status := true)`, the operations `add`, `sub`, `mul`, `div`, `fma`, and `sqrt` return the
result together with its five IEEE flags and its ternary value, and so do `roundToIntegral`,
`scale`, `binaryExponent`, `remainder`, `nextUp`, `nextDown`, `minimum`, `maximum`, `minimumNumber`,
`maximumNumber`, `cast`, `sum`, and `ExecDType.intToFloat`. `dot` and `parse` return it inside their
`Except`. `value_add` and its siblings through `value_cast`, `Reduction.value_sum`, and
`Reduction.map_value_dot` (`simp` lemmas) state that the delivered value is the value of the same
operation without the option. Theorems such as `add_invalid`, `div_divideByZero`, and
`dyadicRoundingStatus_overflow` describe the other returned fields. In a conventional IEEE format,
`add_invalid_of_isIEEE`, `mul_invalid_of_isIEEE`, `fma_invalid_of_isIEEE`, and
`div_invalid_of_isIEEE` give the invalid flag from the classes and signs of the operands alone:
finite operands raise it only for zero over zero, because their rounded results are numbers in
every direction (`isNaN_add_eq_false_of_isFinite` and its siblings).

To decide overflow, we first round to the destination precision with an unbounded exponent range. So
a direction that increases magnitude overflows immediately above the largest finite value, while
toward-zero and a direction back into the finite range don't overflow until the rounded significand
enters the next binade. `dyadicRoundingStatus_overflow` and `rationalRoundingStatusScaled_overflow`
expose that classification for dyadic and signed-rational inputs, respectively.

`roundToIntegral_finite_exact` separates representability of the rounded integer from the input's
finiteness. For IEEE descriptors, the toward-zero results `abs_roundDyadicToInt_towardZero_le`,
`isFinite_roundToIntegral_towardZero`, `toReal_roundToIntegral_towardZero`, and
`roundToIntegral_towardZero_overflow_eq_false` establish truncation without an extra
precision-versus-exponent-range assumption.

`sqrt_inexact_iff` shows that on a finite input with a clear sign bit square root raises `inexact`
exactly when the delivered value is not the real square root, in every rounding direction and for
every descriptor. On every input the flag is the ternary value's difference from `.eq`
(`sqrt_inexact_eq_ternary_bne_eq`). So on a positive finite input the ternary value is `.eq` exactly
for an exact root, and `sqrt_inexact_of_underflow` gives the tiny-and-inexact rule.
`sqrt_status_of_toDyadic` and its siblings `sqrt_status_of_isNaN`, `sqrt_status_of_isZero`,
`sqrt_status_of_signBit`, and `sqrt_status_of_isInf` state the outcome on every class of input. When
`fmt.fracWidth + 1 < fmt.exponentBias`, `dyadicSqrtIsTinyAfterRounding_eq_false` shows that no
positive finite radicand has its root below an underflow boundary, which is why the executable skips
that comparison there.

`toReal_roundRatScaled_eq_roundAt` includes zero numerators in the exact-input nearest-even
bridge, and its finiteness hypothesis rules out a zero denominator. `le_toEReal_ofRat_up` gives the
corresponding upward bound in `EReal`, including zero, subnormal results, and overflow to positive
infinity.

`roundToIntegral x (mode := m)` is the flagless IEEE 754-2019 §5.9 `roundToIntegral{TiesToEven,
TiesToAway, TowardZero, TowardPositive, TowardNegative}` family, together with MPFR's rounding away
from zero. With `status := true` it is §5.9 `roundToIntegralExact` in the requested direction: it
first rounds the exact input to an integer, encodes it in the same direction, and also raises
`inexact` on fractional input (`roundToIntegral_inexact_iff`). `overflow` is raised only for a
custom descriptor whose finite range ends below the rounded integer.
`roundToIntegral_overflow_eq_false` shows this never happens when
`fmt.fracWidth ≤ fmt.maxNormalExponent`, which every IEEE interchange format satisfies.
`isFinite_roundToIntegral` with the `toReal_roundToIntegral` theorems for `down`, `up`,
`towardZero`, `nearest`, `nearestAway`, and `away` then give the result the real value `⌊x⌋`, `⌈x⌉`,
the truncation of `x`, the nearest-even integer, the nearest integer with ties away from zero, or
the integer away from zero. In the remaining custom cases a finite-only encoding saturates, so an
overflow result need not itself be an integer.

`remainder x y (status := true)` reports a clear status on finite operands with a nonzero divisor
because the exact remainder is always representable: `remainder_exact` proves the delivered value
is finite and denotes the exact dyadic remainder for every conventional IEEE descriptor. For the
same operands, `abs_toReal_remainder_le` bounds the result by half the divisor in magnitude, and
`exists_toReal_remainder_eq_sub` writes it as the dividend minus an integer multiple of the divisor.
When the result is nonzero and its sign differs from the dividend's, adding the divisor with the
dividend's sign, the correction that turns it into C's `fmod`, is finite and exact
(`remainder_add_copySign_exact`).

`minimum`, `maximum`, `minimumNumber` and `maximumNumber` are the IEEE 754-2019 §9.6 operations.
`minimum` and `maximum` return a quiet NaN for a NaN operand, and with `status := true` they report
the `invalid` that a signaling NaN owes (`minimum_invalid`, `maximum_invalid`). `minimumNumber`
skips a signaling NaN operand like a quiet one (`minimumNumber_of_isNaN_left`), and with
`status := true` it reports the owed `invalid` (`minimumNumber_invalid`). `minNum` and
`maxNum` are the IEEE 754-2008 operations, which IEEE 754-2019 replaced. They quiet-propagate a
signaling NaN and stay on the model for the TestFloat comparison. With `status := true`, `nextUp`
and `nextDown` likewise add the §5.3.1 `invalid` indicator (`nextUp_invalid`, `nextDown_invalid`).
On two zeros, in either order, `minimum` returns the zero whose sign is the disjunction of the
operands' signs and `maximum` the conjunction (`minimum_of_isZero`, `maximum_of_isZero`,
`minimum_zero_zero`, `maximum_zero_zero`).

`adjacencyRank_lt_adjacencyRank_iff` and `adjacencyRank_eq_adjacencyRank_iff` show that on non-NaN
words the adjacency rank orders the extended-real values, with the two zeros sharing one rank.
From a number, `nextUp` and `nextDown` step to a number (`isNaN_nextUp`, `isNaN_nextDown`), move
strictly away from their fixed points (`toEReal_lt_toEReal_nextUp`,
`toEReal_nextDown_lt_toEReal`), and leave no non-NaN value strictly in between
(`no_value_between_nextUp`, `no_value_between_nextDown`).

Underflow follows the documented after-rounding, tiny-and-inexact rule. Quiet NaN propagation and
generated invalid operations come from the executable operation semantics, and theorems in
`Status.Proof` characterize them.

### Ternary values

Import `FloatLib.Floats.Formats.BinaryInterchange.Status`.

Every `IEEEOutcome` also carries `ternary : Ordering`, MPFR's ternary value: the delivered value
compared with the exact result. Each producer computes it from the same exact witness as its status:
`dyadicTernary` for dyadic results, `rationalTernaryScaled` for division and decimal text,
`dyadicSqrtTernary` for square root, `exactInfinityTernary` when the exact result is an infinity,
and `DecimalInterchange.Conversion.binaryTernary` for the decimal-interchange `toBinary` conversion.
Integral rounding compares with its input, as `mpfr_rint` does. By convention, NaNs, exact
infinities, and the placeholders of `outcomeWithInvalid` have `.eq`. An overflow infinity, or the
NaN that replaces it in a format without one, takes the sign of the exact value, and an exact
infinity delivered as a saturated value or as that NaN has `.lt` for `+∞` and `.gt` for `-∞`.
Nothing in the structure ties inexactness to a nonzero ternary value: a saturating integral rounding
can deliver its own fractional input with `inexact` raised and `.eq`. Below are the theorems for the
comparison helpers and the conventions. Except for `sqrt_inexact_eq_ternary_bne_eq`, which shows
that the square-root `inexact` flag is the ternary value's difference from `.eq` on every input,
they are not contracts relating the ternary value of an operation to its flags.

| Theorem | Informal statement |
| --- | --- |
| `Model.outcomeWithInvalid_ternary` | The exceptional-result constructor carries the ternary convention `.eq`. |
| `Model.dyadicTernary_eq_compare` | For a finite delivery, the dyadic ternary value is the real comparison of the delivered value with the exact dyadic. |
| `Model.dyadicTernary_eq_lt_iff`, `dyadicTernary_eq_eq_iff`, `dyadicTernary_eq_gt_iff` | For a finite delivery, `.lt`, `.eq`, and `.gt` mean below, equal to, and above the exact value. |
| `Model.dyadicTernary_of_isFinite_eq_false` | A non-finite delivery takes the sign of the exact value, the overflow convention. |
| `Model.rationalTernaryScaled_eq_compare` | For a finite delivery and a nonzero denominator, the rational ternary value is the real comparison with the exact signed rational. |
| `Model.rationalTernaryScaled_eq_lt_iff`, `rationalTernaryScaled_eq_eq_iff`, `rationalTernaryScaled_eq_gt_iff` | For a finite delivery and a nonzero denominator, the three rational ternary values mean below, equal to, and above the exact rational. |
| `Model.rationalTernaryScaled_of_isFinite_eq_false` | A non-finite delivery takes the sign of the exact rational, the overflow convention. |
| `Model.rationalTernaryScaled_eq_dyadicTernary` | With denominator one the rational and dyadic ternary values agree. |
| `Model.dyadicSqrtTernary_eq_compare` | For a finite nonnegative delivery and a nonnegative radicand, the square-root ternary value, computed from the square of the delivery, is the comparison with the exact real square root. |
| `Model.dyadicSqrtTernary_of_isFinite`, `Model.dyadicSqrtTernary_of_isFinite_eq_false` | A finite delivery is compared with the radicand through the exact square of its decoding; a non-finite delivery has `.gt`. |
| `Model.sqrt_inexact_eq_ternary_bne_eq` | Square root raises `inexact` exactly when its ternary value is not `.eq`, on every input. |
| `Model.exactInfinityTernary_eq_eq_iff`, `Model.exactInfinityTernary_of_not_infinity` | For an exact infinity, the ternary value is `.eq` exactly when that infinity is delivered, and otherwise `.lt` for `+∞` and `.gt` for `-∞`. |
| `Model.compareDyadicScaled?_eq_compare` | The executable comparison of a signed scaled rational with any dyadic is their real-number order whenever the denominator is nonzero. |
| `Model.cmpDyadic_eq_compare` | The executable dyadic comparison is the real-number order of the two values. |
| `Model.toReal_eq_toReal_finiteDyadic` | A finite value denotes the real value of its decoded dyadic. |
| `Model.expField_le_maxFiniteExpField_of_isFinite`, `Model.abs_toReal_lt_bpow_of_toDyadic?_some` | Every finite word of every encoding has an exponent field at most `maxFiniteExpField` and a magnitude below `2^(maxNormalExponent + 1)`. |

### Configured explicit rounding and status

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof`. Configured
operations `ExecFloat.Binary.add`, `sub`, `mul`, `div`, `fma`, and `sqrt` take the model's options.
Operands come first, then an optional rounding direction `(mode := .up)` (nearest-even by default)
and `(status := true)`, which returns an `ExecFloat.Binary.IEEEOutcome` with the configured value,
its `Numerics.IEEEStatus`, and the ternary value. So no stored word appears in application code.

The configured theorems that need an IEEE descriptor take its proof `hformat : format.isIEEE = true`
as their last argument, with the default `ieee_format`. It uses a hypothesis in context or decides
the proof for a concrete IEEE-encoded format, so `toReal_add_eq_roundAt hout` needs no format
argument for binary32. A format with another encoding has no such proof, and a variable format
without a hypothesis passes `(hformat := h)`. The `Model` theorems take the descriptor proof as
an ordinary argument.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.IEEEOutcome.toModel_ofModel` | Repacking and decoding a model outcome preserves its delivered value, all five status flags, and its ternary value. |
| `ExecFloat.Binary.toModel_add`, `toModel_sub`, `toModel_mul`, `toModel_div`, `toModel_fma`, `toModel_sqrt` | Decoding a configured operation gives the descriptor-model operation `Model.add (mode := mode)` (and its five siblings) on the decoded operands. The nearest-even call runs the format's selected capability, so the theorem takes the instance argument `ExecFloat.Capability.HasSpec cap Configured.Spec.add`, that its reference operation is the model's; instance search proves it for every capability the library declares, also under `simp`. A custom capability whose reference is only propositionally the model operation needs an explicit `HasSpec` instance, and one with another reference operation does not satisfy the theorem. |
| `ExecFloat.Binary.toModel_hAdd`, `toModel_hSub`, `toModel_hMul`, `toModel_hDiv`, `toModel_neg`, `toModel_execFloat_sqrt` | Decoding `a + b`, `a - b`, `a * b`, `a / b`, `-a`, and the generic `ExecFloat.sqrt a` gives the nearest-even model operation on the decoded operands, so `simp` moves a goal about the notation to the model. The four operators and the square root take the same `HasSpec` instance argument as `toModel_add`; negation is computed through the codec and needs none. |
| `ExecFloat.Binary.toReal?_eq_none_iff`, `toReal?_eq_some_toReal` | `toReal?`, the exact real value of a configured value, is absent exactly when the value is not finite, and is otherwise the total `toReal`. |
| `ExecFloat.Binary.toReal_of_toRat?_eq_some`, `toRat?_eq_some_of_toReal_eq` | A value whose exact rational value is `q` has real value `q`, and a finite value whose real value is the rational `q` has exact rational value `q`. |
| `ExecFloat.Binary.toReal_add_eq_roundAt`, `toReal_sub_eq_roundAt`, `toReal_mul_eq_roundAt`, `toReal_div_eq_roundAt`, `toReal_fma_eq_roundAt`, `toReal_sqrt_eq_roundAt` (`Configured.Real`) | For an IEEE descriptor, a finite result of `a + b`, `a - b`, `a * b`, `a / b` (finite divisor), `fma a b c`, or `sqrt a` (finite `a`, zero or positive, always finite) is `Model.roundAt` of the exact real result. They take the same `HasSpec` instance argument as `toModel_hAdd`. |
| `ExecFloat.Binary.abs_toReal_add_sub_le` and its siblings through `abs_toReal_sqrt_sub_le` | Under the same hypotheses, the result differs from the exact real result by at most half an ulp, `Model.halfUlpAt format` at the exact result. |
| `ExecFloat.Binary.toReal_add_of_isZero_left` and its siblings through `toReal_sqrt_of_isZero` (`Configured.Real`) | The exact cases of the descriptor model hold for `+`, `-`, `*`, `/`, and `sqrt` on configured values, and `toReal_sub_self` gives `x - x = 0`. |
| `ExecFloat.Binary.toModel_ofRat`, `IEEEOutcome.toModel_ofRat`, `value_ofRat` | `ofRat q (mode := m)` decodes to `Model.ofRat format q (mode := m)`, its `status := true` outcome to the model outcome, and that outcome's value is the plain rounding. |
| `ExecFloat.Binary.IEEEOutcome.value_bind`, `status_bind`, `ternary_bind` | `outcome.bind next` delivers the value and ternary value of `next outcome.value` and the union of both statuses. |
| `ExecFloat.Binary.toInt?_eq_none_iff` (`Configured.Operations.Proof`) | `toInt? x (mode := m)`, the integer that rounds the exact value of `x` in `m`, is absent exactly when `x` is not finite. |
| `ExecFloat.Binary.IEEEOutcome.toModel_add`, `toModel_sub`, `toModel_mul`, `toModel_div`, `toModel_fma`, `toModel_sqrt` | Decoding a configured operation with `status := true` gives the descriptor-model outcome: value, all five flags, and ternary value. |
| `ExecFloat.Binary.value_add`, `value_sub`, `value_mul`, `value_div`, `value_fma`, `value_sqrt` | The value of a configured operation with `status := true` is the configured operation without it. They take the same `HasSpec` instance argument as `toModel_add` and its siblings, which instance search supplies for every capability the library declares, with the same restriction for custom capabilities. |
| `ExecFloat.Binary.IEEEOutcome.toModel_remainder`, `toModel_roundToIntegral`, `toModel_scale`, `toModel_binaryExponent`, `toModel_nextUp`, `toModel_nextDown`, `toModel_minimum`, `toModel_maximum`, `toModel_minimumNumber`, `toModel_maximumNumber` and `ExecFloat.Binary.value_remainder` through `value_maximumNumber` | The same decoding and projection statements for the configured standard operations (`Configured.Operations.Proof`). `min_eq_minimum` and `max_eq_maximum` state that `min` and `max` run the configured `minimum` and `maximum`. |

Apart from the nearest-even default, which runs the selected capability, the configured functions
just repackage the existing descriptor-model operations. Since the bridge theorems above are `simp`
lemmas, a goal about a configured operation reduces to the corresponding `Model` theorem in
`Status.Proof` or `DirectedSemantics`.

We accumulate sticky flags with `FloatLib.Numerics.IEEEStatus.union`. Binary and decimal operations
report the same record, `Numerics.IEEEStatus`, and selection, clearing, saving, testing, and
restoration share one implementation too. `Numerics.IEEEStatus.Proof` proves their laws for every
flag state and selected group, and the decimal namespace exports those results.

### Exact integer exponents

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Proof`. `binaryExponentInt`
returns the exact integer exponent of a finite nonzero input, and `binaryExponent`, the same-format
convenience operation, rounds that integer into the source format.

| Theorem | Informal statement |
| --- | --- |
| `Model.binaryExponentInt_of_finite_nonzero` | The integer result is the significand's integer binary logarithm plus its stored exponent, with clear status. |
| `Model.binaryExponentInt_bounds` | Its exponent brackets the exact magnitude between consecutive powers of two. |
| `Model.binaryExponentSentinel_outside_logBBound` | The exceptional sentinel lies beyond twice the IEEE exceptional-result bound. |
| `Model.binaryExponentInt_mem_exponentRange`, `Model.abs_binaryExponentInt_lt_binaryExponentSentinel` | A finite nonzero answer lies between the least subnormal and the largest normal exponent, so it never equals the sentinel or its negation. |
| `Model.binaryExponentInt_of_zero`, `binaryExponentInt_of_infinity`, `binaryExponentInt_of_nan` | Zero returns a negative sentinel; infinity and NaN return a positive sentinel; each raises invalid. |

### Quiet and signaling comparisons

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Comparison.Proof`.
`compareQuiet` and `compareSignaling` take the 22 IEEE comparison operations as a predicate
argument (`compareQuiet .lessEqual` is `compareQuietLessEqual`) and use `Numerics.IEEEComparison`'s
shared truth tables. Model and configured operations return the same Boolean-and-flags result type
used by decimal comparison.

| Theorem | Informal statement |
| --- | --- |
| `Model.compare_eq_of_toEReal?` | Non-NaN operands compare according to their exact extended-real values, including infinities. |
| `Model.compareQuiet_value_of_toEReal?`, `compareSignaling_value_of_toEReal?` | Every predicate applies its truth table to that exact numerical order. |
| `Model.compareQuiet_value_of_nan`, `compareSignaling_value_of_nan` | A NaN operand selects the predicate's unordered truth value. |
| `Model.compareQuiet_invalid_iff`, `compareSignaling_invalid_iff` | Quiet comparison raises invalid for signaling NaNs, and signaling comparison raises it for either kind of NaN. |
| `ExecFloat.Binary.compareQuiet_value_of_toEReal?`, `compareSignaling_value_of_toEReal?` | The same numerical contracts hold through every lawful configured storage codec. |

### Total ordering of representations

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Proof`. For finite values,
the executable comparison reuses the scalable dyadic comparator and is proved equal to an exact
lexicographic specification. Every descriptor policy, width, and bias uses this one implementation.
These operations preserve NaN metadata and raise no exceptions.

| Theorem | Informal statement |
| --- | --- |
| `Model.totalOrder_total`, `Model.totalOrder_trans`, `Model.totalOrder_antisymm` | Complete words form a total order for every binary descriptor. |
| `Model.totalOrder_of_compare_eq_lt`, `Model.totalOrder_of_toEReal_lt` | Strict numerical order implies representation order. |
| `Model.totalOrder_zero_iff`, `Model.totalOrder_nan_iff` | Zero signs and NaN signs, signaling classes, and payloads determine the exceptional order. |
| `Model.totalOrderMag_trans`, `Model.totalOrderMag_both_iff_exactValue_abs_eq` | Magnitude ordering is transitive and identifies equal sign-cleared complete data. |
| `Model.totalOrderMag_eq_totalOrder_abs_of_ieee` | IEEE magnitude order agrees with total order after encoded absolute value. |

### Classification

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Classification.Proof`.
These results apply to every binary descriptor with its declared encoding and bias.

| Theorem | Informal statement |
| --- | --- |
| `Model.classify_eq_match_exactValue` | All ten classes agree with the complete exact value, including zero signs and NaN signaling status. |
| `Model.isNormal_iff_le_abs_toReal` | Normal values are finite, with magnitude at least the descriptor's normal threshold. |
| `Model.isSubnormal_iff_abs_toReal` | Subnormal values have positive magnitude strictly below that threshold. |
| `Model.classify_eq_of_exactValue_eq` | Equal complete exact values have equal classes. |
| `ExecFloat.Binary.classify_eq_match_exactValue` | Configured classification satisfies the same semantic contract through every lawful codec. |

### External text

Import `FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Roundtrip`,
`FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.PrecisionProof` and
`FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.DecimalFormattingProof`. `format value`
writes a decimal that reads back as `value`: the exact value when it has at most `d` significant
digits (17 for binary64), and otherwise normally the shortest one. `toString` and `#eval` show the
same text. `format value (style := .exact)` and `(style := .hex)` give the exact external
representations, including NaN metadata.

| Theorem | Informal statement |
| --- | --- |
| `Model.toReal_convertDecimalText_nearest`, `Model.toReal_parse_decimal_nearest` | Successfully scanned decimal text is one nearest-even rounding of its exact decimal value, including inexact text and zero, when the IEEE output is finite. |
| `Model.convertDecimalText_eq_exact` | Clamping the written decimal exponent never changes the converted value, status, or ternary value. |
| `Model.rationalTernaryScaled_eq_of_high`, `Model.rationalTernaryScaled_eq_of_low` | Above the overflow saturation exponent and below the underflow one, the ternary value of a delivery does not depend on the exact rational. |
| `Model.parse_format_of_isFinite`, `Model.parse_toString_of_isFinite` | Every finite IEEE word round-trips through its decimal display with nearest-even input, including signed zero. |
| `Model.parse_format_hex_of_isFinite` | Every finite IEEE word round-trips through exact hexadecimal text in all input modes, including signed zero. |
| `Model.parse_format_exact_of_isFinite` | Every finite IEEE word round-trips through exact decimal text with nearest-even input. |
| `Model.significantDecimal_coefficient_bounds`, `Model.significantHex_coefficient_bounds` | Nonzero output has exactly the requested positive number of significant digits in every mode. |
| `Model.significantDecimal_nearest_error`, `Model.significantHex_nearest_error` | Nearest-even output stays within half the selected text-grid step. |
| `Model.le_significantDecimal_up`, `Model.le_significantHex_up` | Output toward positive infinity is at least the exact input. |
| `Model.significantDecimal_down_le`, `Model.significantHex_down_le` | Output toward negative infinity is at most the exact input. |
| `Model.significantDecimal_towardZero_abs_le`, `Model.significantHex_towardZero_abs_le` | Output toward zero cannot increase the exact input's magnitude. |
| `Model.formatDyadicText_decimal_inexact_iff`, `Model.formatDyadicText_hexadecimal_inexact_iff` | Output raises inexact exactly when its numerical value changes. |
| `Model.format_status` | Text output in any style raises at most inexact. |
| `Model.format_exact_status`, `Model.format_hex_status` | Exact decimal and hexadecimal output leave all five exception indicators clear. |
| `Model.format_fixed_error`, `Model.format_scientific_error` | Nearest-even fixed and scientific output stay within half a unit in the last requested place. |

This proof API does not cover universal NaN/infinity word recovery.

### Certified execution backends

Import `FloatLib.Floats.ExecFloat`. Whichever backend the planner selects, the public equations
`ExecFloat.Proof.*_eq_spec` hold for every configured binary type, because each backend enters
through a `Backend.Certified` candidate whose certificate is one of the theorems below. We prove the
kernels against the descriptor model, so one theorem serves every format a kernel is eligible for.

| Theorem | Informal statement |
| --- | --- |
| `Model.NativePair.addFinite_eq`, `subFinite_eq`, `fmaFinite_eq` | On two 64-bit words, for every IEEE layout of at most 128 bits whose fraction is wider than one word (`NativePair.Eligible`), the fast finite addition, subtraction, and fused multiply-add agree with the exact finite kernel whenever they accept. |
| `Model.NativePair.mulNormalLimb_refines`, `divNormal_refines`, `sqrtNormal_refines` | The two-word normal multiplication, division (Algorithm D candidate, independent certificate, proved restoring repair), and square root refine the reference specification under the same eligibility. |
| `Model.WideLimb.toModel_add`, `toModel_sub`, `toModel_mul`, `toModel_div`, `toModel_sqrt`, `toModel_fma` | On the 32-bit limb carrier of `ExecFloat.BinaryLimbs`, for every IEEE layout wider than 128 bits with an exponent field of at most 32 bits, all six operations decode to their complete `Model.Spec` results. Division uses a direct integer quotient for finite inputs; square root uses an integer root for positive normal inputs, with exact fallbacks elsewhere. |
| `Model.NativeSmallWordAdd.addFinite_refines` | The all-`UInt64` addition and subtraction kernel for IEEE layouts within one machine word refines the exact finite kernel whenever it accepts. |

## Lean's native float model

Import `FloatLib.Floats.Formats.IEEE754`, or the usual `FloatLib` root. Lean exposes enough of its
float model to connect its signed integer casts and integer constructors to our rounding
specifications. Arithmetic bridges also relate ordinary Lean expressions to FloatLib's
configured operations. `toFloat`, `ofFloat`, `toFloat32`, and `ofFloat32` convert every configured
format, rounding once in their `mode` option through `Model.cast` when the formats differ. The
theorems below are about `Binary64` and `Binary32`, whose values cross as interchange words.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.toFloat32_ofFloat32`, `toFloat_ofFloat` | Every native value survives importing into FloatLib and exporting again. |
| `ExecFloat.Binary.toModel_ofFloat32_nan`, `toModel_ofFloat_nan` | Lean's named NaN constants import as FloatLib's canonical NaN. Corresponding `inf` theorems identify positive infinity. |
| `Model.ofInt_conversion_spec` | Lean's integer constructor gives the word and status of FloatLib's reference default conversion `runWith` for any conventional IEEE descriptor. |
| `Model.toReal_ofModel_ofInt_eq_roundAt` | A finite result of Lean's integer constructor is the nearest-even rounding of the integer. |
| `Model.finiteStatus_ofInt_underflow_false` | Lean's integer constructor never signals underflow in a conventional IEEE descriptor. |
| `ExecFloat.Binary.toModel_ofFloat_ofNat`, `toModel_ofFloat32_ofNat` | Native natural constructors round the entire unbounded input with FloatLib's rational rounder. |
| `ExecFloat.Binary.toModel_ofFloat_intToFloat`, `toModel_ofFloat32_intToFloat32` | Unbounded `Int` casts agree with FloatLib's dyadic rounder, including negative values and overflow. |
| `ExecFloat.Binary.toModel_ofFloat32_int64ToFloat32`, `toModel_ofFloat_int64ToFloat` | Signed integer casts agree with FloatLib's nearest-even integer conversion. The other native signed widths have corresponding lemmas. |
| `ExecFloat.Binary.float32ToInt8_eq_floatToIntSaturating`, `floatToInt8_eq_floatToIntSaturating` | Native signed casts truncate toward zero and saturate; NaN maps to zero. The other signed widths have corresponding lemmas. |
| `ExecFloat.Binary.ofFloat32_add_of_isFinite`, `ofFloat_add_of_isFinite` | On finite operands, importing a native sum equals adding the imports, including signed zeros and overflow. Corresponding subtraction, multiplication, and division lemmas have the same scope. |
| `Model.canonicalizeModel_sqrt_eq_model` | For every conventional IEEE input, square root agrees with Lean's model after NaN canonicalization. |
| `ExecFloat.Binary.toFloat32_sqrt`, `toFloat_sqrt` | Configured square root commutes with native export on every input. |

Here the `Model` names belong to `Formats.BinaryInterchange.Model`. These are equalities with Lean's
logical definitions. Executing a native call also trusts the compiler, runtime, and hardware, while
our software operations keep their existing refinement certificates.

## Configured binary transcendentals

These functions come from the optional
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals` import (or the model barrel
`BinaryInterchange.Transcendentals`), which `import FloatLib` does not include. With it,
applications can call `ExecFloat.Binary.exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh`, and
`tanh` without unpacking the configured carrier, and can use `Model.pow` / `x ^ y` on a binary
model. That import also installs `MathFunctions` on `ExecFloat.Binary` and `Model fmt`, with the
approximation kernels. `open scoped FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath`
replaces both instances by the dictionaries `CorrectlyRounded.mathFunctions`, whose `exp` and
`log` are correctly rounded on IEEE descriptors. Certified `sqrt` and `abs` are available without
it.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.toModel_exp`, `toModel_log` | Configured exponential and logarithm are exactly their deterministic model kernels after decoding. |
| `ExecFloat.Binary.CorrectlyRounded.mathFunctions_exp_of_isIEEE`, `mathFunctions_log_of_isIEEE` | For an IEEE descriptor, the `exp` and `log` of the opt-in dictionary `ExecFloat.Binary.CorrectlyRounded.mathFunctions` are `CorrectlyRounded.exp` and `CorrectlyRounded.log`. The default instance keeps the approximation kernels. |
| `Model.Transcendentals.CorrectlyRounded.mathFunctions_exp_of_isIEEE`, `mathFunctions_log_of_isIEEE` | The same for `Model.Transcendentals.CorrectlyRounded.mathFunctions` on `Model fmt`. |
| `ExecFloat.Binary.toModel_sin`, `toModel_cos`, `toModel_sinCos` | Configured trigonometric calls preserve the corresponding model result; `sinCos` shares argument reduction. |
| `ExecFloat.Binary.toModel_sinh`, `toModel_cosh`, `toModel_tanh` | Configured hyperbolic calls preserve the corresponding model result. |

These theorems connect configured calls to their model results. We haven't proved general real-error
bounds or correct rounding for these value-only kernels, and the calls return no IEEE status flags.
For externally trusted real enclosures and explicit rounding modes, use the optional Arb adapter.

Sine and cosine reduce their arguments with the Payne-Hanek reduction of
`FloatLib.Numerics.Enclosure.ArgumentReduction` (import `FloatLib.Numerics.Enclosure`). It reduces
`x = m * 2 ^ e` from a window of the cached `2 / π` to a quadrant and a fraction `F` with
`x * 2/π = 4 j + quadrant + (F + η) / 2 ^ scale` and `0 ≤ η < 2 m`. Then the kernels widen the
window until `F` keeps the destination precision plus 32 bits, at most four times and only while it
stays within `2^21` bits of `2 / π`. We prove the error of the remainder, but not the Taylor
evaluation or the final rounding, so the kernels stay approximations. For a `k`-bit significand `m`,
the first window stays within the limit when `max e 0 + 2 k + fracWidth + 59 ≤ 2^21`. In a format
with at most 524,258 fraction bits, that holds for every finite argument below `2^(2^20)`. An
argument whose first window needs more bits, or whose permitted windows are all rejected, gives the
invalid result.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.Enclosure.ArgumentReduction.reduceWindow_spec`, `reduce_spec` | For `m > 0` and every window of at least two bits, the reduction of `m * 2 ^ e` meets `QuarterTurns.Reduces`: `x * 2/π = 4 j + quadrant + (fraction + η) / 2 ^ scale` for an integer `j` and some `0 ≤ η < 2 m`. |
| `Numerics.Enclosure.ArgumentReduction.abs_fraction_reduceWindow_le`, `abs_fraction_reduce_le` | The fraction is at most half a quarter turn. |
| `Numerics.Enclosure.ArgumentReduction.exists_reduce_eq_reduceWindow`, `error_reduce`, `accepts_reduce` | `reduce` returns the reduction of one of its attempts, with error `2 m`, and an accepted one when some attempt within its fuel is accepted. |
| `Numerics.Enclosure.ArgumentReduction.fuelWithin?_isGreatest`, `fuelWithin?_spec`, `fuelWithin?_eq_none_iff` | `fuelWithin?` gives the largest count within its fuel whose window reads a cache level of at most its limit, every earlier attempt reads at most that level too, and it gives none exactly when the first window needs a higher level. |
| `Numerics.Enclosure.ArgumentReduction.QuarterTurns.accepts_spec`, `QuarterTurns.Reduces.exists_remainder` | An accepted reduction is nonzero, has the sign of the exact remainder, and has relative error below `2 ^ -bits`. |
| `Numerics.Enclosure.ArgumentReduction.sin_cos_add_quarterTurns`, `QuarterTurns.Reduces.exists_sin_cos_eq_rotate` | The sine and cosine of `x` are those of the reduced argument `(fraction + η) / 2 ^ scale * π/2`, rotated by the quadrant. |
| `Numerics.Enclosure.ArgumentReduction.QuarterTurns.abs_argument_sub_le`, `QuarterTurns.Reduces.abs_sin_sub_rotate_le`, `QuarterTurns.Reduces.abs_cos_sub_rotate_le` | The argument computed with the cached `π / 2` at `M` bits is within `error / 2 ^ scale * π/2 + \|fraction\| / 2 ^ scale * 2 ^ (1 - M)` of the reduced argument, and the rotated sine and cosine of it are within the same distance of `sin x` and `cos x`. |
| `Numerics.Enclosure.ArgumentReduction.exists_accepting_window`, `exists_accepts_reduce` | Every window from some width on is accepted (for `m > 0` because `m * 2 ^ e * 2/π` is irrational, and trivially for `m = 0`), so enough doublings reach an accepted reduction. |

For an IEEE descriptor the constant `Model.pi` is correctly rounded. It rounds an enclosure from the
cache of proved constants in `FloatLib.Numerics.Enclosure.Constants` (import
`FloatLib.Numerics.Enclosure`), which also supplies the `2 / pi` and `pi / 2` of sine and cosine
reduction, the `log 2` of exponential reduction and of generated configurations, and the `log 2` of
the certified power. Each precision level of the cache is computed once, on first use, and these
readers share it from then on. The exact comparators and the certified logarithm still compute their
own `pi / 4` and `log 2`.

| Theorem | Informal statement |
| --- | --- |
| `Model.toReal_pi_eq_roundAt`, `Model.isFinite_pi` | For an IEEE descriptor, `Model.pi` is finite and is the nearest-even rounding of `Real.pi`. |
| `Numerics.Enclosure.Constants.piLevel_halfPi_spec`, `piLevel_twoOverPi_spec`, `ln2Fixed_spec` | At every precision, the computed integers are within two units below `π / 2`, `2 / π` and `log 2` times `2 ^ bits`. |
| `Numerics.Enclosure.Constants.halfPiLower_spec`, `twoOverPiLower_spec`, `ln2Lower_spec`, `abs_ln2Faithful_sub_lt_one`, `containsReal_ln2Grid` | Reads from the cache at any precision stay within two units below, the rounded read of `log 2` within one unit, and its grid read encloses it. |
| `Numerics.Enclosure.Constants.piLevelAt_eq`, `ln2FixedAt_eq` | A cached level is exactly the uncached value. |

`Model.Power.toReal_pow_of_eq_intCast` covers another case: for an IEEE descriptor, a finite base,
and a finite floating exponent whose real value is an integer, every finite `Model.pow` result
is one nearest-even rounding of the exact integer power. `Model.Power.pow_spec_of_certified` covers
every other finite exponent of a finite positive base. Whenever the certified enclosure search
`Model.Transcendentals.Certified.pow` settles, `Model.pow` returns its finite result, the
nearest-even rounding of the real power. When the search reports overflow, `Model.pow` returns the
format's overflow result. Most exact results on a rounding boundary, an exhausted search, and
non-IEEE descriptors fall back to the approximate composition `exp (y * log x)`.

For IEEE binary formats, the certified searches `ExecFloat.Binary.Certified.exp`, `log`, `pow`,
`expMinus1`, and `logPlus1` refine proved rational enclosures until both endpoints round to the same
finite encoding. Stable variants perform the subtraction or addition of one exactly before rounding.
They return `.ok result` on success, and otherwise `.error (failure : Certified.Failure)`: an
unsupported format, a nonfinite input, a domain or range failure, or an inconclusive search.
Certification never falls back to an approximation. The theorems below are partial correctness.
They describe every `.ok` result, but no theorem says which inputs succeed, and the only proved
success is the signed-zero passthrough `Model.Transcendentals.Certified.expMinus1_of_isZero` and
`logPlus1_of_isZero`. You set the starting degree and the number of enclosure attempts with the
`budget` option, a `Certified.Budget`, which bounds the attempts and not the total work. On the
model,
`Model.Transcendentals.Certified.pow` (finite floating inputs) and `powRat` (exact rationals) refine
enclosures of `exp (y * log x)` for a positive base in the same way.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.Certified.map_toModel_exp`, `map_toModel_log`, `map_toModel_pow`, `map_toModel_expMinus1`, `map_toModel_logPlus1` | Decoding preserves the certified model kernel's result or failure. |
| `ExecFloat.Binary.Certified.isFinite_of_exp_eq_ok`, `isFinite_of_log_eq_ok`, `isFinite_of_pow_eq_ok` | Every certified result is finite. |
| `ExecFloat.Binary.Certified.toReal_of_exp_eq_ok`, `toReal_of_log_eq_ok`, `toReal_of_pow_eq_ok` | A certified result equals nearest-even real rounding of the exact exponential, logarithm, or power. |
| `ExecFloat.Binary.Certified.toReal_of_expMinus1_eq_ok`, `toReal_of_logPlus1_eq_ok` | A certified result is one nearest-even rounding of `Real.exp x - 1` or `Real.log (1 + x)`, without first rounding the exponential or the sum. |
| `ExecFloat.Binary.toModel_pow` | The plain configured `pow` decodes to `Model.pow`. |
| `Model.Transcendentals.Certified.isFinite_of_powRat_eq_ok`, `toReal_of_powRat_eq_ok`, `base_pos_of_powRat_eq_ok` | A power of exact rationals accepted by `powRat` is finite and equals nearest-even rounding of the real power `base ^ exponent`; only positive bases are accepted. |
| `Model.Transcendentals.Certified.isFinite_of_pow_eq_ok`, `toReal_of_pow_eq_ok` | The same for finite floating inputs decoded exactly, including bases and results far outside binary64's exponent range. |
| `Model.Power.pow_spec_of_certified` | For a finite positive base and a finite exponent that is not an integer, `Model.pow` is finite and correctly rounded whenever `Certified.pow` settles within the budget `Model.Power.certifiedBudget`. |

The optional `FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded` import adds
total `ExecFloat.Binary.CorrectlyRounded.exp`, `log`, `expMinus1`, `logPlus1`, and `expMul`,
which rounds `exp x * w` once. Each returns the result of the enclosure search when it settles and
otherwise decides the rounding by exact comparisons, so the theorems have no premise on the
budget. The model functions and these theorems are in `Model.Transcendentals.CorrectlyRounded`.
Apart from the agreement with the certified search, the theorems need an IEEE descriptor and a
finite input in the domain.

| Theorem | Informal statement |
| --- | --- |
| `toReal_exp_eq_roundAt`, `toReal_log_eq_roundAt`, `toReal_expMinus1_eq_roundAt`, `toReal_logPlus1_eq_roundAt`, `toReal_expMul_eq_roundAt` | When the exact result, in absolute value for `log`, `logPlus1`, and `expMul`, lies below `Certified.overflowThreshold`, the result is its nearest-even rounding. |
| `toReal_exp_of_isFinite` and its siblings | Every finite result is the nearest-even rounding of the exact result. |
| `isFinite_exp_iff` and its siblings | The result is finite exactly when the exact result, in absolute value for `log`, `logPlus1`, and `expMul`, is below the overflow threshold. |
| `abs_toReal_exp_sub_le` and its siblings | Under the range premise of `toReal_exp_eq_roundAt` and its siblings, the result has relative error `unitRoundoffAt fmt` and absolute error `underflowErrorAt fmt`. |
| `exp_eq_nativeOverflow` and its siblings | When the exact result is at or above the overflow threshold in absolute value, the result is the infinity with its sign. |
| `toReal_pos_of_isFinite_log`, `neg_one_lt_toReal_of_isFinite_logPlus1` | A finite logarithm or `logPlus1` of a finite input comes from an input in the domain. |
| `toReal_exp_pos`, `toReal_expMinus1_lt_zero`, `toReal_expMinus1_pos`, `toReal_logPlus1_pos`, `isFinite_exp_of_nonpos`, `isFinite_expMinus1_of_nonpos`, `isFinite_logPlus1_of_nonneg` | The exponential is positive when its exact result exceeds `underflowErrorAt fmt` and is below the overflow threshold. `expMinus1` of a negative input is negative, and of a positive input is positive when its exact result is below the overflow threshold. The exponential and `expMinus1` of a nonpositive input are finite. `logPlus1` of a nonnegative input is finite, and of a positive input is positive. |
| `toReal_expMul_nonneg`, `toReal_expMul_nonpos`, `toReal_expMul_pos`, `toReal_expMul_lt_zero` | The weighted exponential is nonnegative for a nonnegative weight and nonpositive for a nonpositive one. It has the strict sign of its exact result when the magnitude of that result exceeds `underflowErrorAt fmt` and is below the overflow threshold. |
| `exp_eq_of_certified_exp_eq_ok`, `expMinus1_eq_of_certified_expMinus1_eq_ok`, `log_eq_of_certified_log_eq_ok`, `logPlus1_eq_of_certified_logPlus1_eq_ok` | Whenever the certified search returns a result, the total function returns the same encoding. |
| `ExecFloat.Binary.CorrectlyRounded.toModel_exp` and its siblings | The configured functions decode to the model functions, and they carry `isFinite_exp`, `toReal_exp_eq_roundAt`, `isFinite_exp_iff`, `abs_toReal_exp_sub_le`, the sign and domain theorems, and their siblings. `toModel_exp_eq_nativeOverflow` and its siblings state the overflow results. At a zero the exponential is exactly one and `expMinus1` and `logPlus1` return the zero, all finite: `toReal_exp_of_isZero`, `toReal_expMinus1_of_isZero`, `toReal_logPlus1_of_isZero` and their `isFinite` siblings. |

`ExactExpression` and `roundOnce` round once when the expression is exact in their chosen domain. A
rational domain cannot represent `log`, `sin`, or `tanh` in general, so composing the current
transcendental kernels approximates and rounds at each function boundary. Correctly rounding a whole
transcendental composition needs a certified real enclosure or another exact-real procedure.
Treating the expression as rational arithmetic can't give you that.

## Error bounds inferred from code

Import `FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff`. You write the
computation, and the analysis builds the reference, the same computation in exact arithmetic on the
decoded inputs, and the error budget from its code. At a call of a function whose real model the
analysis has no rule for, such as a real function the program takes, the reference applies that
model to the decoded computed argument, so the argument's rounding is not part of the bound. Here
is a quarter of a binary32 value:

```lean
import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff

open FloatLib.Floats

def quarter (x : Binary32) : Binary32 := x / 4

roundoff mixed theorem quarter_mixedError :=
  fun (x : Binary32) => ExecFloat.Binary.toReal (quarter x)
```

The command generates and proves `quarter_mixedError`, and `#check quarter_mixedError` prints its
statement. For a finite `x` whose exact quarter `|toReal x / 4|` is at most the largest finite
binary32 value, `quarter x` is finite and has the mixed error
`(unitRoundoffAt binary32, underflowErrorAt binary32)` against `toReal x / 4`. That is one
rounding of the exact quotient, because the literal `4` converts exactly. The range condition is
yours to prove. For `|toReal x| ≤ 1` it follows from `Model.one_le_toReal_posMaxFinite` and
`linarith`.

`roundoff theorem` states an absolute bound instead, naming its reference and budget. The tactic
`roundoff` proves an absolute or mixed error bound, finiteness, a decoded value or a sign of a
configured computation in place, and leaves any premise it can't prove as a goal. A loop over a
list, an array, a vector, a function on `Fin n` or a matrix is analyzed once for a symbolic
accumulator and lifted through the traversal, so the theorem holds at every length. Another
library registers its containers, and relations that a loop step preserves, by marking a
`Roundoff.Extension` with `@[roundoff_extension]`, and `[roundoff_rule]` registers further
numerical theorems. The table lists the lemmas the analysis builds its proofs from.

| Theorem | Informal statement |
| --- | --- |
| `List.fold_error` | A bound on one step of `List.foldl`, for an accumulator within its budget of its reference, lifts through the loop to the accumulated budget `List.foldError`, when the step's conditions hold at the visited states (`List.AllSteps`). |
| `List.fold_mixedError` | The same for mixed bounds, with the relative and absolute parts `List.foldRelative` and `List.foldAbsolute`, together with an invariant the steps preserve, such as finiteness. |
| `List.fold_relation` | A relation between the loop state, a shadow state and budgets that one step preserves under its condition lifts through the loop to the shadow fold and the accumulated budgets `List.foldBudget`, when the condition holds at the visited states. |
| `List.abs_sub_le_of_sumFold`, `List.abs_sub_le_of_sumFold_of_exact` | The generated mixed bound of a summation loop `s := s + t v` from zero, with relative error `u` per addition and term budgets `c v`, is at most `((1 + u)^n - 1) * ∑ |p v| + (1 + u)^n * ∑ c v`, and `((1 + u)^n - 1) * ∑ |p v|` for exact terms. |
| `List.AllSteps.invariant`, `List.AllSteps.of_map`, `List.AllSteps.of_forall`, `List.foldl_induction` | An invariant preserved at the visited steps holds at the end; conditions can be read on the original accumulator; conditions that hold everywhere hold at the visited steps. |
| `Numerics.add_error`, `Numerics.mul_error`, `Numerics.div_error`, `Numerics.exp_error` and their siblings | The absolute error of an exact real operation on approximate operands, plus the local error of the operation actually executed. |
| `Numerics.enclosure_error` | The distance to the farther endpoint of a rational enclosure bounds the error of any candidate. |
| `ExecFloat.Binary.add_rounding`, `sub_rounding`, `mul_rounding`, `div_rounding`, `sqrt_rounding` | For an IEEE descriptor, a finite configured result has the mixed error of one rounding against the exact operation on the computed operands: relative error `u`, with the underflow allowance as absolute part for products, quotients and square roots. A quotient needs a finite divisor and a square root a finite operand in its domain. |
| `Model.add_rounding`, `sub_rounding`, `mul_rounding`, `div_rounding`, `sqrt_rounding`, `fma_rounding`, `Model.isFinite_add_of_mixedError` and its siblings | The same for descriptor-model values. Importing `Analysis.MixedError.Rounding` registers them, so that `roundoff` can prove mixed bounds with a relative part for model computations. |
| `ExecFloat.Binary.isFinite_add_of_mixedError` and its siblings | For an IEEE descriptor, finite operands whose exact result has an enclosure at most the largest finite value have a finite result; a quotient also needs a divisor that is not an executable zero. |
| `ExecFloat.Binary.isFinite_sub_self`, `isFinite_add_of_isZero_left`, `isFinite_mul_of_abs_toReal_eq_one_left` and their siblings | Under the hypotheses of the exact operation, an IEEE descriptor and its zero, unit-magnitude or finiteness facts, the result is finite with no range condition. |
| `Model.toReal_ofRat_eq_roundAt`, `Model.isFinite_ofRat`, `Model.abs_toReal_ofRat_sub_le` | For an IEEE descriptor, a finite conversion of a rational is its rounding to nearest, within one rounding error; a rational of magnitude at most the largest finite value converts to a finite value. |
| `Model.cast_toRat_eq_toReal`, `Model.toReal_abs_of_isFinite`, `Model.abs_toReal_sub_le_of_containsReal` | A value's rational decoding, read as `0` for an exceptional value, is its total real value; clearing the sign of a finite value is exact in a format with signed zero; and a rational enclosure bounds a finite candidate's error. |

## Repeatedly rounded reductions

`FloatLib.Numerics.Reduction.Tree` describes nonempty binary evaluation schedules.
`FloatLib.Numerics.Reduction.Error` proves bounds from local error assumptions at the actual operand
pairs. Neither module depends on a format or tensor library.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.ReductionTree.abs_eval_sub_exact_le_errorBudget` | The total error is at most the sum of allowances at the internal nodes. |
| `Numerics.ReductionTree.abs_eval_sub_exact_le_nodeCount` | A uniform absolute allowance is paid once per addition. |
| `Numerics.ReductionTree.abs_eval_sub_exact_le_mixedBudget` | Relative and absolute local errors give a recursive bound using exact subtree sums. |
| `Numerics.ReductionTree.abs_eval_sub_exact_le_geometric` | Under local relative bounds, leaf count and absolute-input scale give a schedule-independent geometric enclosure. |
| `Numerics.ReductionTree.abs_eval_sub_eval_le_of_perm` | Two schedules over the same input occurrences differ by at most the sum of their errors against the exact sum. |
| `Model.ReductionTree.abs_toReal_eval_sub_sum_le` | Every finite IEEE reduction tree has a sum-of-half-ULPs bound, including subnormal intermediate results. |
| `Model.ReductionTree.abs_toReal_eval_sub_eval_le` | Two finite schedules over the same input occurrences differ by at most their combined budgets. |
| `Model.ReductionTree.allNodes_abs_toReal_add_sub_le` | Every finite addition in an IEEE tree meets the local relative premise with `u = unitRoundoffAt fmt` and no absolute allowance. |
| `Model.ReductionTree.abs_toReal_eval_sub_sum_le_mixedBudget` | Every finite IEEE reduction tree satisfies the mixed-budget bound with `u = unitRoundoffAt fmt` and zero absolute allowance, including subnormal intermediate results. |
| `Model.ReductionTree.abs_toReal_eval_sub_sum_le_geometric` | Every finite IEEE reduction tree with `n` additions has error at most `((1 + u)^n - 1) * Σ\|xᵢ\|`, with no normal-range hypothesis. |

Model results live in `BinaryInterchange.Reduction.Tree` and require finite leaves and finite
intermediate additions. They don't identify an arbitrary native CPU or GPU reduction with a
particular tree. That connection needs a downstream execution proof.

## Correctly rounded reductions

Import
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction` for configured values or
`FloatLib.Floats.Formats.BinaryInterchange.Reduction` for mixed source and destination
descriptors.

Our model reducer decodes every finite term into an exact dyadic, accumulates the full sum or
product sum, and invokes the ordinary descriptor rounder once. In the configured API, the carrier
changes before and after that model operation.

| Theorem | Informal statement |
| --- | --- |
| `Model.Reduction.Internal.array_foldl_pushValue_exact_toRat` | The executable sum accumulator denotes the exact rational sum of all finite inputs. |
| `Model.Reduction.Internal.dotState_exact_toRat` | The dot accumulator denotes the exact rational sum of exact products. |
| `Model.Reduction.sum_status_eq_round_of_finite_nonzero` | A nonzero finite sum performs one final dyadic rounding and returns exactly that rounding's status and ternary value. |
| `Model.Reduction.sum_status_value_toReal_eq_roundAt_of_finite`, `dot_status_value_toReal_eq_roundAt_of_finite` | Finite-input nearest-even sums and successful dots with finite outputs are one real rounding, including empty inputs and cancellation to zero. |
| `Model.Reduction.sum_status_eq_zero_of_finite` | An exact-zero finite sum follows the documented signed-zero rule and raises no status flag. |
| `Model.Reduction.dot_status_eq_round_of_finite_nonzero` | A nonzero finite dot performs one final dyadic rounding and returns exactly that rounding's status and ternary value. |
| `Model.Reduction.dot_status_eq_zero_of_finite` | An exact-zero finite dot follows the documented signed-zero rule and raises no status flag. |
| `Model.Reduction.sumAccumulator_toRat_eq_of_perm` | Permuting finite summands preserves the exact rational accumulator; NaN selection remains traversal-order dependent. |
| `Model.Reduction.dot_status_lengthMismatch` | Unequal lengths return both observed lengths without evaluating a truncated dot product. |
| `ExecFloat.Binary.IEEEOutcome.toModel_sum` | Decoding a configured sum preserves its complete model result, status, and ternary value. |
| `ExecFloat.Binary.dot_status_eq_model` | Configured dot execution is exactly the model result, including errors and status. |
| `Model.Reduction.value_sum`, `Model.Reduction.map_value_dot` | The value of a sum or dot product with `status := true` is the sum or dot product without it, with the same length check, so the theorems above also describe the value forms. |
| `ExecFloat.Binary.value_sum`, `ExecFloat.Binary.map_value_dot` | The same holds for the configured reductions. |

`Model.Reduction.Semantics.finiteDot_singleton` records the mathematical one-product case behind
FMA. An FMA chain rounds each prefix, so its result can differ from an exact dot product.
Signed-zero and exceptional-value choices can also differ. Both executions agree only when every
intermediate round is exact and those edge rules align.

Our external MPFR oracle covers binary16, bfloat16, binary32, binary64, binary128, and binary256,
all six rounding modes, and wider-source mixed-precision cases. Fixed encoding regressions cover NaN
choice, infinities, signed zero, overflow, underflow, `0 * ∞`, and explicit length errors.

## Decimal interchange

Import `FloatLib.Floats.Formats.DecimalInterchange.Basic`.

One descriptor in the `Encoding` API supports both BID and DPD, with decimal32, decimal64, and
decimal128 as named presets. A custom layout chooses a declet count, a positive exponent-field
width, and an arbitrary bias, and its precision is `3 * declets + 1`. These theorems preserve the
full datum: coefficient, quantum exponent, signed zero, and exceptional fields. In particular, equal
numerical values with different cohort exponents stay distinct.

| Theorem | Informal statement |
| --- | --- |
| `Encoding.decode_valid` | Every word decodes to a valid datum for its width. |
| `Encoding.decode_of_encode?_eq_some` | Successful checked encoding round-trips the complete datum. |
| `Encoding.decode_canonicalize` | Canonicalization changes no datum fields. |
| `Encoding.canonicalize_idempotent` | A canonical word is unchanged by further canonicalization. |
| `Encoding.canonicalize_eq_canonicalize_iff` | Two words have the same canonical word exactly when they decode to the same datum. |
| `decode_transcode` | Conversion between BID and DPD preserves the complete datum. |
| `transcode_transcode` | Conversion to the other encoding and back produces the canonical source word. |
| `Datum.toRat?_ofScientific`, `Datum.toRat?_ofNat` | A `Datum` literal, which keeps its written coefficient and quantum, has the value of the same literal in `ℚ`. |

Import `FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Basic` for core arithmetic and its
numerical guarantees. Operations consume and return complete `Datum` values, with all five rounding
modes and explicit exception flags.

Decimal operations report `FloatLib.Numerics.IEEEStatus`, the record binary arithmetic uses. Flag
selection, clearing, restoration, and their laws use that shared namespace.

| Theorem | Informal statement |
| --- | --- |
| `Arithmetic.add_valid`, `sub_valid`, `mul_valid`, `div_valid`, `fma_valid` | Each operation returns a valid destination datum. |
| `Arithmetic.add_error_le_half`, `mul_error_le_half`, `div_error_le_half`, `fma_error_le_half` | Under the stated finite nearest-rounding hypotheses, error is at most half the selected quantum. |
| `Arithmetic.sqrt_error_le_half` | Exact squared comparisons give the corresponding square-root rounding bound. |
| `projectMagnitude_exact`, `projectMagnitude_exact_status` | Representable rational values are preserved numerically and do not raise inexactness. |
| `le_project_up`, `project_down_le` | Without overflow, directed projection is finite and lies on the requested side of the exact input. |
| `le_project_up_of_toRat?_eq_some`, `project_down_le_of_toRat?_eq_some` | Every finite directed result lies on the requested side of the exact input, saturated overflow included. |
| `Arithmetic.add_inexact_iff`, `Arithmetic.fma_inexact_iff` | The inexact flag records a change in the exact numerical result. |
| `project_underflow_iff` | Underflow combines inexactness with decimal tininess before rounding. |
| `Arithmetic.add_zeros`, `Arithmetic.sqrt_zero` | Zero results follow the stated sign and preferred-exponent rules. |
| `projectMagnitude_quantum_closest`, `Arithmetic.sqrt_quantum_closest` | Exact nonzero results select a representable cohort exponent closest to the preferred exponent. |
| `projectMagnitude_inexact_quantum_minimal`, `Arithmetic.sqrt_inexact_quantum_minimal` | Inexact finite results use the least representable quantum exponent. |
| `Arithmetic.quantize_same_quantum`, `Arithmetic.quantize_inexact_iff` | Successful quantization uses the requested quantum, with inexactness exactly when the value changes. |
| `Arithmetic.quantize_error_le_half`, `Arithmetic.quantize_error_lt_one` | Quantization satisfies the nearest or directed error bound in units of the requested quantum. |
| `Arithmetic.roundToIntegralExact_integer`, `Arithmetic.roundToIntegralExact_inexact_iff` | Finite integral rounding produces an integer and reports whether rounding changed the value. |
| `Arithmetic.roundToIntegral_value`, `Arithmetic.roundToIntegral_inexact` | Quiet integral rounding preserves the same rounded value and suppresses the inexact flag. |
| `Datum.compare_sameCohort` | Numerical comparison is unchanged when operands are replaced by equal cohort members. |
| `Datum.compareQuiet_invalid_iff`, `Datum.compareSignaling_invalid_iff` | Quiet and signaling comparisons raise invalid on their specified NaN classes. |
| `Datum.totalOrder_trans`, `Datum.totalOrder_total`, `Datum.totalOrder_antisymm_iff` | Total ordering distinguishes complete datums, including cohort exponents and NaN data. |
| `Datum.sameCohort_isNormal`, `Datum.sameCohort_isSubnormal` | Normal and subnormal classification depends on the value, not its cohort exponent. |
| `Arithmetic.nextUp_adjacent`, `Arithmetic.nextDown_adjacent` | No valid finite datum lies strictly between an input and its delivered neighbor. |
| `Arithmetic.nextUp_quantum_minimal`, `Arithmetic.nextDown_quantum_minimal` | Finite nonzero neighbors use the finest representable quantum. |
| `Arithmetic.remainder_value`, `Arithmetic.remainder_error_le_half_divisor` | The exact nearest-even remainder is representable and has magnitude at most half the divisor. |
| `Arithmetic.remainder_even_at_midpoint` | A remainder at half the divisor uses an even integer quotient. |
| `Arithmetic.scale_exact_value`, `Arithmetic.scale_inexact_iff` | Scaling preserves representable exact values and reports numerical rounding precisely. |
| `Arithmetic.scale_quantum_closest` | Exact scaling chooses the cohort quantum closest to the shifted input quantum. |
| `Arithmetic.decimalExponent_bounds`, `Arithmetic.decimalExponent_eq_of_equal_magnitude` | The finite exponent query bounds the input by consecutive powers of ten and is unchanged by cohort or sign. |
| `Formatting.parse_formatExact`, `Formatting.parseWord_formatWord_exact` | Exact text preserves complete datums and canonical BID/DPD words. |
| `Formatting.significantDecimal_error_le_half`, `Formatting.significantDecimal_nearest_midpoint` | Requested-precision output satisfies the nearest error bound and resolves even ties. |
| `Formatting.parse_format_significant_value` | Output with at least the source precision round-trips numerically under any output/input rounding-mode pair. |
| `FloatLib.Numerics.IEEEStatus.testFlags_iff`, `FloatLib.Numerics.IEEEStatus.testSavedFlags_iff` | A group test succeeds precisely when a selected exception is raised. |
| `FloatLib.Numerics.IEEEStatus.isSet_lowerFlags`, `FloatLib.Numerics.IEEEStatus.isSet_restoreFlags` | Clearing and restoration affect exactly the selected exceptions. |
| `FloatLib.Numerics.IEEEStatus.union_assoc`, `Environment.accept_accept_flags` | Successive outcomes accumulate their flags associatively. |
| `Environment.run_isSet` | An exception remains raised if it was already set or the operation raises it. |
| `Environment.withRounding_rounding`, `Environment.withRounding_flags` | Scoped rounding restores the caller's direction and preserves the inner computation's final flags. |

These guarantees cover the six core operations, their preferred-cohort rules, quantization,
integral rounding, comparisons, classification, neighbors, remainder, exponent operations,
text conversion, and explicit exception state.
Import `FloatLib.Floats.Formats.DecimalInterchange` for the complete public decimal API.

For exact integer powers, reciprocal square root, hypotenuse, and integer roots, import
`FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Proof`. Each of these algebraic operations
accepts all five rounding modes and works with custom decimal layouts.

| Theorem | Informal statement |
| --- | --- |
| `Arithmetic.square_valid`, `powInt_valid`, `rsqrt_valid`, `hypot_valid`, `rootN_valid` | The delivered datum is valid for the destination format. |
| `Arithmetic.rootN_degree_zero` | Degree zero returns a canonical quiet NaN and raises invalid for every input, including NaNs. |
| `Arithmetic.square_error_le_half`, `powInt_error_le_half`, `rsqrt_error_le_half`, `hypot_error_le_half`, `rootN_error_le_half` | A finite nearest-rounded result is within half the selected decimal grid step of the exact real expression, under its domain hypotheses. |
| `Arithmetic.rootN_error_lt_one` | For a finite nonzero input and a nonzero degree in the real domain, every rounding mode has error strictly less than one selected grid step when no overflow occurs. |
| `Arithmetic.rootN_down_le`, `le_rootN_up` | Directed roots lie on their requested side of the exact root when no overflow occurs. |
| `Arithmetic.rootN_inexact_iff`, `rootN_underflow_iff` | Root status records numerical inexactness and tininess before rounding. |
| `Arithmetic.integerRoot_pow_natAbs` | The real root specification satisfies its defining power equation, using the reciprocal operand for a negative degree. |

Stable `expMinus1` and `logPlus1` and their correctness theorems come from the optional import
`FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof`. In its
`Transcendentals.Certified` namespace, `toReal_of_expMinus1_eq_some` and
`toReal_of_logPlus1_eq_some` identify a successful result with nearest-even rounding of
`Real.exp x - 1` and `Real.log (1 + x)`. A returned datum is valid and finite, and valid signed
zeros keep their quantum. An inconclusive enclosure or an invalid domain returns `none`. This is
partial correctness: no theorem says which inputs succeed, except that a valid signed zero passes
through (`expMinus1_of_isZero`, `logPlus1_of_isZero`).

Conversions reuse exact source decoding and one destination projection:

| Theorem | Informal statement |
| --- | --- |
| `Conversion.convertFormat_error_le_half` | Decimal-to-decimal nearest rounding has at most half a selected quantum of error when it does not overflow. |
| `Conversion.fromBinary_zero_clamped`, `Conversion.fromPosit_zero_clamped` | Zero conversion chooses a valid quantum for every descriptor, even when quantum zero is unavailable. |
| `Conversion.toPosit_eq_real` | A finite decimal converts to the standard posit rounding of its exact real value, including saturation and nonzero underflow. |
| `Conversion.Integer.convertToInteger_invalid_iff` | Integer conversion fails exactly for an exceptional source or a rounded integer outside the destination range. |
| `Conversion.Integer.convertToInteger_error_le_half` | Successful nearest integer conversion has at most half a unit of error. |
| `Conversion.Integer.convertFromInt_exact` | Every representable integer converts to its exact decimal value. |

For a binary destination, the adapter requires an IEEE descriptor. Its nearest-mode equalities
require a finite output, while directed modes provide extended-real bounds. NaN conversion preserves
fitting payloads, quiets signaling NaNs, and raises invalid for them. Convenience results that
deliver decimal quantum zero assume `[f.HasQuantumZero]`, but the general clamped results need no
bias bounds.

## Posits and quires

Import `FloatLib.Floats.Formats.Posit`.

`Model.toRat?` is the exact semantic view. It returns `none` exactly for the unique NaR word:

| Theorem | Informal statement |
| --- | --- |
| `Model.toRat?_eq_none_iff` | Exact rational decoding fails exactly for NaR. |
| `Model.toRat?_eq_toDyadic?_map` | Rational and dyadic views agree on every word. |
| `Model.compareLess_eq_true_iff` | Encoded strict comparison agrees with signed-word order. |
| `Model.nar_le`, `Model.nar_lt_iff_ne_nar` | NaR is the least posit in the standard order. |
| `Model.toProjectiveRat_eq_infty_iff` | The optional projective view reaches its added point exactly for NaR. |
| `Model.toRat?_widen` | Appending any number of zero bits preserves the complete optional exact value, including zero and NaR. |
| `Model.roundRat_widen` | Rounding an exactly decoded finite source into a wider posit produces its zero-extended word. |
| `ExecFloat.Posit.decode_ofModel_widen` | Every lawful configured codec preserves complete decoding under zero-extension, including zero and NaR. |
| `ExecFloat.Posit.Conversion.run_default_widen` | Default configured conversion to any wider posit returns the zero-extended word. |
| `ExecFloat.Posit.toModel_ofRat` | `ofRat q`, the rounding behind posit literals, decodes to `Model.roundRat format q`. |

Read the projective theorem as an interoperability result. It doesn't redefine NaR as a posit
infinity: the primary semantics keeps `ExceptionalValue.notAReal`.

For the elementary functions we prove real-valued rounding theorems, which say more than agreement
with an executable approximation:

| Theorem | Informal statement |
| --- | --- |
| `Model.exp_eq_real`, `Model.expMinus1_eq_real` | The result is the standard posit rounding of the exact real exponential, with subtraction performed before rounding for `expMinus1`. |
| `Model.log_eq_real`, `Model.logPlus1_eq_real` | Positive logarithm arguments are rounded from their exact real values; `logPlus1` adds one exactly first. |
| `Model.log2_eq_real`, `Model.log10_eq_real` | Base-two and base-ten logarithms satisfy the corresponding real rounding statements. |
| `Model.log2Plus1_eq_real`, `Model.log10Plus1_eq_real` | The shifted-input variants perform one rounding after exact addition and logarithm. |
| `Model.exp2_eq_roundPositive`, `Model.exp10_eq_roundPositive` | Rational-exponent comparison selects the rounding of the exact real power. |
| `Model.exp2Minus1_eq_round`, `Model.exp10Minus1_eq_round` | Base-two and base-ten exponential-minus-one operations round the exact combined expression. |
| `Model.sin_eq_real`, `Model.cos_eq_real`, `Model.tan_eq_real` | Radian trigonometric functions return the standard posit rounding of the exact real result. |
| `Model.arcSin_eq_real`, `Model.arcCos_eq_real`, `Model.arcTan_eq_real` | Inverse trigonometric functions satisfy real rounding on their principal domains. |
| `Model.sinPi_eq_real`, `Model.cosPi_eq_real`, `Model.tanPi_eq_real` | Pi-scaled functions include multiplication by pi in the exact expression before rounding. |
| `Model.arcSinPi_eq_real`, `Model.arcCosPi_eq_real`, `Model.arcTanPi_eq_real` | Inverse pi-scaled functions divide the exact principal angle by pi before rounding. |
| `Model.tanPi_eq_nar_of_pole` | Every half-integer tangent input is rejected exactly. |
| `Model.arcTan2_eq_real`, `Model.arcTan2Pi_eq_real` | The result rounds the principal argument of `x + i*y`, or that argument divided by pi, for finite nonzero coordinate pairs. |
| `Model.arcTan2_origin`, `Model.arcTan2Pi_origin` | The origin produces NaR. |
| `Model.sinH_eq_real`, `Model.cosH_eq_real`, `Model.tanH_eq_real` | Hyperbolic functions round the exact real value without intermediate posit rounding. |
| `Model.arcSinH_eq_real`, `Model.arcCosH_eq_real`, `Model.arcTanH_eq_real` | Inverse hyperbolic functions satisfy real rounding on their real domains. |
| `Model.parse_display`, `ExecFloat.Posit.parse_toString` | Exact decimal display round-trips every posit value, including NaR. |
| `Model.parse_eq_roundRat` | Successful finite decimal input uses one rounding of the parsed exact rational. |
| `Model.toRat?_floor`, `Model.toRat?_ceil` | Every finite result denotes the exact mathematical integer; NaR propagates. |
| `Model.toRat?_nearestInt`, `Model.nearestInt_spec` | The delivered posit is exactly a nearest integer, within half a unit, with even ties. |
| `Model.floor_of_int`, `Model.ceil_of_int`, `Model.nearestInt_of_int` | All three operations fix every integer-valued posit. |
| `Model.toInt_toFixedInt_of_inRange` | Conversion to a fixed-width integer implements nearest-even rounding when the result fits. |
| `Model.toFixedInt_eq_minCode_iff` | The signed sentinel word occurs for an out-of-range rounded result or a valid result equal to the signed minimum. |
| `Model.toNat_toUnsigned_of_inRange` | A successful unsigned conversion denotes the shared nearest-even rounded integer. |
| `Model.toUnsigned_eq_intMin_iff` | The unsigned sentinel word also represents an in-range value, so its bits alone do not identify failure. |

Invalid inputs have their own domain and NaR theorems, and the configured posit carriers export the
corresponding results through their model bridge. The natural exponential/logarithm search
terminates because it separates irrational targets from rational boundaries. Exact rational cases
are handled directly.

For exact accumulation, the important quire results are:

| Theorem | Informal statement |
| --- | --- |
| `Quire.Model.toRat?_pToQ` | Converting any posit to its quire preserves its optional exact rational meaning. |
| `Quire.Model.toRat?_qMulAdd_of_ordinary` | A quire fused product-add is exact while the coefficient remains in range. |
| `Quire.Model.qMulAdd_eq_nar_of_not_ordinary` | A quire fused product-add whose exact coefficient leaves the range produces quire NaR; together with the previous row this characterizes `qMulAdd` on ordinary inputs. |
| `Quire.Model.toRat?_qMulSub_of_ordinary` | A quire fused product-subtract is exact while the coefficient remains in range. |
| `Quire.Model.addDyadic_eq_nar_of_exponent_lt` | The shared accumulation kernel rejects an increment below the quire's least-significant bit instead of mis-scaling it. |
| `Quire.Model.qToP_eq_roundRat` | Converting a quire back to a posit performs rational rounding as defined by the Posit Standard (2022). |
| `Quire.Model.ordinaryCoefficient_sum_of_length_lt_productSumTermLimit` | Every product list below the standard term limit fits the ordinary quire coefficient range. |
| `Quire.Model.toRat?_foldMulAdd_zero` | Folding `qMulAdd` over fewer than `2^31` pairs of non-NaR posits from the zero quire is exact: the result is not NaR and denotes the exact sum of products. |
| `Quire.Model.toRat?_foldAddP_zero` | Folding `qAddP` over fewer than `2^(23 + 4n)` non-NaR posits from the zero quire is exact. |

On the configured user carrier, `ExecFloat.Posit.Quire.toRat?_pToQ`,
`ExecFloat.Posit.Quire.toRat?_foldl_qMulAdd_zero`, and
`ExecFloat.Posit.Quire.toRat?_foldl_qAddP_zero` are exported too, so ordinary programs don't need to
unwrap storage codes to use the conversion or capacity theorems. The hypothesis
`exactProducts? pairs = some products` (or `exactValues?`) states that no input is NaR and names the
exact rational terms.

## Exact fixed point and logarithmic formats

Import `FloatLib.Floats.Formats.FixedPoint` or
`FloatLib.Floats.Formats.Logarithmic`.

| Theorem | Informal statement |
| --- | --- |
| `FixedPoint.Code.toRat_add` | Decoding exact fixed-point addition gives rational addition. |
| `FixedPoint.Code.toRat_sub` | Decoding exact fixed-point subtraction gives rational subtraction. |
| `FixedPoint.Code.toRat_mul` | Multiplication composes the two scales and gives the exact rational product. |
| `FixedPoint.Bounded.toRat_wrapAdd` | Wrapping addition is coefficient addition reduced modulo the storage width. |
| `FixedPoint.Bounded.toRat_saturatingAdd` | Saturating addition is exact coefficient addition followed by clamping. |
| `ExecFloat.BoundedFixedPoint.toRat_of_add_eq_some` | Configured addition with the default `overflow := .reject` is exact: any returned value decodes to the rational sum (likewise `toRat_of_sub_eq_some`, `toRat_of_mul_eq_some`). |
| `ExecFloat.BoundedFixedPoint.add_eq_some` | Configured rejecting addition succeeds when the exact coefficient sum fits the width (likewise `sub_eq_some`, `mul_eq_some`). |
| `ExecFloat.BoundedFixedPoint.add_eq_none_iff` | Configured rejecting addition returns `none` exactly when the exact coefficient sum does not fit (likewise `sub_eq_none_iff`, `mul_eq_none_iff`). |
| `ExecFloat.BoundedFixedPoint.toRat_add_saturate` | Configured addition with `overflow := .saturate` decodes to the exact coefficient sum clamped to the signed range (likewise `toRat_sub_saturate`, `toRat_mul_saturate`; `toRat_add_wrap` and its siblings give the wrapping results). |
| `Logarithmic.Code.toReal_mul` | Multiplication of logarithmic codes is exact real multiplication. |
| `Logarithmic.Code.toRat_mul` | The same multiplication is exact in the rational decoder. |
| `ExecFloat.FixedPoint.coefficient_ofRat` | `ofRat q`, the rounding behind decimal literals, stores the ties-to-even rounding of `q` times the scale. |
| `ExecFloat.Logarithmic.cast_toRat`, `ExecFloat.Logarithmic.toRat_mul` | The configured exact reading `toRat` agrees with the real semantics and is exact under multiplication. |

Fixed-point results record the composed fractional scale in their type. Bounded wrapping and
saturating operations get their own theorems, because they reduce or clamp the coefficient when an
exact result leaves the representable range.

## Named codebook values

Import `FloatLib.Floats.Formats.Codebook`. Arbitrary codebooks cannot have a generic inverse
constructor because a table may be non-injective or contain exceptional entries. Named catalog
tables expose semantic constructors instead. The bipolar table provides
`ExecFloat.Codebook.Catalog.bipolar1.negativeOne` and `positiveOne`, and the ternary table provides
`zero`, `negativeOne`, `positiveOne`, and `reserved` in its own namespace.

Matching `decode_negativeOne`, `decode_positiveOne`, `decode_zero`, and `decode_reserved` theorems
state their complete `NumericalValue Int` meanings, so application code doesn't need to know any
catalog bit pattern.

`Codebook.nearestCode` is a deterministic nearest-codeword quantizer: `Codebook.nearestCode_spec`
states that its result is a finite codeword minimizing `|x - c|` over all finite codewords, and
`Codebook.nearestCode_toNat_le` that at a tie it picks the lowest word.

## Block-scaled and interval semantics

Import `FloatLib.Floats.Formats.Block` for shared-scale blocks. `Block.quantizesAt_quantizeAt`
states that each lane is rounded at the supplied common exponent, and
`Block.quantizeAt_refines` packages that pointwise statement as the contextual quantization
capability.

For the six concrete 32-element OCP MX profiles, import `FloatLib.Floats.Formats.OCP.MX`.
The following names are in `OCP.MX.Standard`:

| Theorem | Informal statement |
| --- | --- |
| `quantizeFinite_quantizes` | Each lane follows the selected shared scale and element overflow policy. |
| `quantizeFinite_error_le` | With SAT, each output lane minimizes absolute error among finite elements at the selected scale. |
| `dotExact_eq_scaled_sum` | Exact block accumulation equals the specification's shared-scale dot-product formula. |
| `dotGeneralExact_finite` | Multi-block accumulation equals the exact rational sum of all products. |
| `toReal_dotGeneral_eq_roundAt` | A finite result is one nearest-even binary32 rounding of the exact real sum. |
| `abs_toReal_dotGeneral_sub_le` | For finite inputs and a finite result, the error is at most half a binary32 ULP, including gradual underflow. |

Dot products accept different element profiles on their two sides. Exact accumulation is our choice
of the internal precision MX permits. The scale-selection theorem doesn't claim global optimality
over other shared scales.

`Numerics.Interval α` stores arbitrary endpoint representations. Its partial arithmetic uses
`Numerics.OutwardRounding α β`: a scalar decoder and a certified partial enclosure function. Generic
corner bounds apply over any ordered field. Successful finite operations preserve containment, and
unavailable enclosures, exceptional inputs, and zero-crossing division return `none`. Concrete
binary, decimal, and posit adapters use exact rational scalar arithmetic. `Interval.ContainsReal`
interprets those rational endpoints in the reals, and the `containsReal_add?`, `containsReal_sub?`,
`containsReal_mul?`, and `containsReal_div?` theorems cover arbitrary real members, not only
rational inputs. `contains_fma?` proves the ordered-field multiply-add enclosure, and
`containsReal_fma?` gives its real interpretation, with outward rounding applied only after the
product and addend are combined.

`Numerics.Interval.Expr` composes arithmetic, natural and real powers, and elementary functions. Its
`containsReal_eval?` theorem proves real containment for any backend satisfying
`Numerics.Interval.Backend.Sound`. `rational_sound`, `binaryGrid_sound`, and `ofRounding_sound`
establish this contract for exact rational endpoints, integer binary-grid endpoints, and custom
outward rounders, respectively. `Expr.check_sound` proves inequalities over a rational box,
including adaptive subdivision, and the `interval` tactic uses it to produce kernel-checked proofs
from local real bounds. Elementary containment theorems include `containsReal_tanBounds?`,
`containsReal_asinBounds?`, `containsReal_acosBounds?`, `containsReal_sinhBounds`,
`containsReal_coshBounds`, and `containsReal_tanhBounds`. Inverse sine and cosine check the
`[-1, 1]` domain, and tangent checks that its cosine enclosure excludes zero.
`containsReal_rpowBounds?` covers variable real exponents on positive base intervals.
`containsReal_logbBounds?` covers positive arguments and bases whose logarithm enclosure excludes
zero. `containsReal_asinhBounds?`, `containsReal_acoshBounds?`, and `containsReal_atanhBounds?` give
inverse hyperbolic containment. Inverse hyperbolic cosine requires inputs at least one, and inverse
hyperbolic tangent requires an interval strictly inside `(-1, 1)`. Inverse hyperbolic sine uses
monotonicity and odd symmetry for stable endpoint evaluation. All five contracts apply to every real
member of their accepted input intervals.

`ConstantBounds` bundles a constant's rational endpoints with the ordinary inequalities proving
containment. Its `toExtension_sound` theorem supplies the general contract automatically.
`Extension.Sound` connects a computable enclosure to a curried real function or constant.
`Backend.withExtensions_sound` preserves containment when extending any sound endpoint backend.
`@[interval_extension]` registers constant certificates or those proofs for use by the tactic.
`Expr.call` supports any number of arguments and is reevaluated on each subdivision.

Configured binary endpoints are available through
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval`.
`ExecFloat.Binary.Interval.toModel_ofModel` and `ofModel_toModel` preserve complete endpoint
encodings, and the `toModel_*` lemmas identify every configured operation with the existing model
operation. Its `add_sound`, `sub_sound`, `mul_sound`, and `div_sound` theorems transport the model's
real-enclosure guarantees, including their descriptor and validity hypotheses. We keep range-checked
finite-encoding results apart from IEEE extended-real results.

Import `FloatLib.Floats.Interval` for enclosure proofs:

| Theorem | Informal statement |
| --- | --- |
| `Interval.roundDown_le` | Directed downward rounding never exceeds the exact real input. |
| `Interval.le_roundUp` | Directed upward rounding never falls below the exact real input. |
| `Interval.genericFormat_roundDown`, `genericFormat_roundUp` | Both directed roundings land on the format's grid. |
| `RInterval.mem_add`, `mem_sub`, `mem_mul` | Outward-rounded interval arithmetic contains the corresponding real operation. |
| `RInterval.mem_exp` | Endpoint evaluation of `Real.exp` with outward rounding is sound, by monotonicity. |
| `RInterval.mem_tanh` | Endpoint evaluation of `Real.tanh` with outward rounding is sound, by monotonicity. |
| `RInterval.mem_sqrt` | Square-root propagation is sound; the enclosure is informative when the input interval is nonnegative. |
| `RInterval.mem_log` | Logarithm propagation is sound when the input interval is strictly positive. |
| `RInterval.mem_div` | Division is sound for every denominator interval: four-corner division when it excludes zero, and the whole extended-real line when it contains zero. |

For IEEE overflow and division through zero, use the `EInterval` theorems, whose endpoints live in
`EReal` and so can represent unbounded enclosures.

For bit-executable descriptor intervals, import
`FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics`:

| Theorem | Informal statement |
| --- | --- |
| `Model.Interval.{add,sub,mul,div,sqrt}_sound` | Directed endpoint execution encloses the corresponding exact real operation; square root carries its nonnegative-domain premise. |
| `Model.Interval.{add,sub,mul}_sound_of_encoding_finite` | For all-words-finite encodings, add/sub require both exact endpoint results in range and multiplication requires all four exact corner products in range. |
| `Model.Interval.{add,sub,mul,div}_validExtended` | Every IEEE arithmetic result has ordered non-NaN endpoints; indeterminate candidate bounds become the whole range. |
| `Model.Interval.{neg,relu,abs}_sound_extended` | Unary enclosures accept `ValidExtended` inputs and real members in `EReal`, so infinite endpoints from earlier operations are allowed. |
| `Model.Interval.{neg,relu,abs}_validExtended` | Negation, ReLU, and absolute value preserve ordered non-NaN endpoints in every descriptor. |
| `Model.Interval.sqrt_validExtended` | Finite valid nonnegative inputs produce ordered non-NaN square-root bounds. |

`ValidExtended.valid_of_isFinite` turns that overflow-aware invariant back into ordinary `Valid`
once both result endpoints are proved finite. `ofBounds` handles indeterminate candidates such as
`∞ + -∞`, `0 · ∞`, and `∞ / ∞` by returning the whole range. This keeps the operations closed and
the fallbacks conservative, but each soundness theorem still requires its stated input hypotheses.
For negation, ReLU, and absolute value, apply `*_sound_extended` right after an operation that may
overflow, with no need to prove the intermediate endpoints finite. For finite intervals, the
original `*_sound` theorems are convenient specializations.

## Flocq-style generic format theory

Import `FloatLib.Floats.Formats.Flocq`. These theorems are stated over `ℝ` for a radix `β` and
exponent function `fexp`. They form the proof layer behind the interval rounders and the binary
error analyses, and none of them is an executable operation.

| Theorem | Informal statement |
| --- | --- |
| `Flocq.round_toNearest_point` | Every `ValidRndToNearest` rule selects a representable value at minimal distance from the input. |
| `Flocq.add_round_error_generic` | For any nearest rounding rule, the error of a rounded sum of two representable values is itself representable (this fails for directed rounding). |
| `Flocq.add_round_exact_error` | Error-free transformation form of the previous theorem: `x + y = round (x + y) + e` with `e` representable. |
| `Flocq.sqrt_round_residual_FLX` | For precision above one, the residual `x - q^2` of a nearest-rounded square root is representable. |
| `Flocq.roundAtScale_nearestEven_after_odd_binary_extra` | Round-to-odd with two extra binary digits followed by nearest-even rounding equals direct nearest-even rounding, on a fixed grid only. |
| `Flocq.refineLocation_correct` | The executable bracket refinement used by the effective calculation layer is sound. |
| `Flocq.round_floor_of_scaledBracket`, `round_ceil_of_scaledBracket`, `round_trunc_of_scaledBracket`, `round_away_of_scaledBracket`, `round_nearestChoice_of_scaledBracket` | A unit bracket of the scaled mantissa and the input's location in it determine the rounded value for floor, ceiling, truncation, rounding away from zero, and nearest rounding with any tie choice. |
| `Flocq.nearestChoice_eq_of_fract_ne_half`, `nearestChoice_tieAway_eq_awayRound_of_fract_eq_half` | Off a midpoint every tie choice gives the same integer; at a midpoint, ties away from zero is rounding away from zero. |
| `Flocq.negRound_floorRound`, `negRound_ceilRound`, `negRound_truncRound`, `negRound_awayRound`, `negRound_nearestChoice_tieAway` | Conjugation by negation exchanges floor and ceiling and fixes truncation, rounding away from zero, and ties away from zero. |

`Flocq.roundingFunction` interprets the six directions of `IEEERoundingMode`, the five
IEEE 754-2019 rounding-direction attributes and rounding away from zero, GNU MPFR's `MPFR_RNDA`,
as integer-rounding rules. Each has a `ValidRnd` instance, so `Flocq.roundingSpec` and every
theorem about `round` that assumes only `ValidRnd` cover all six.
Results that assume `ValidRndToNearest`, such as `error_bound_ulp` and `round_toNearest_point`,
still apply only to nearest rounding.

`Flocq.RoundOddPoint` fixes parity at a grid exponent you supply. `Flocq.RoundOddCanonicalPoint`
uses the result's canonical exponent, matching Flocq's `Rnd_odd_pt`. `round_odd_canonical_point_FIX`
proves this contract for fixed-point grids, and `round_odd_canonical_point_of_cexp_eq` transports it
when rounding preserves the canonical exponent.

## P3109 representation, projection, and arithmetic

Import `FloatLib.Floats.Formats.P3109`. A P3109 descriptor supplies exact representation semantics
and the interim report's v4.0.3 round-then-saturate projection. Ordinary `convert`, `cast`, and
destination-driven mixed operations use `Rat` as the exact domain of a P3109 destination, which has
one zero. `ofDyadic`, `project`, `ofRat`, and `projectRat` are the focused projection APIs.
`ExecFloat.P3109` evaluates addition, subtraction, multiplication, division, and fused expressions
exactly before one projection into `(target := ...)` under the `mode` and `saturation` options, and
its `unary`, `binary`, and `ternary` accept operands of different descriptors. Square root,
reciprocal square root, and hypotenuse use integer comparisons with the exact real root, so their
implementation does not need an intermediate floating-point approximation. On top of that, the mixed
interface includes fused addition, scaled operations, and binary16, binary32, and BFloat16
destinations. Extrema and query operations use the descriptor's finite classes and exceptional
values.

`Formats.P3109.Block` adds nonempty blocks with independently typed scales and elements.
Conversions, exact sums, products, dots, and generic unary, binary, and ternary closed rational
operations normalize at the requested result scale before one destination projection. Block roots
use P3109 destinations and handle negative result scales through signed exact roots. Stochastic
policies carry one caller-supplied word per lane.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.P3109.decode_zero` | The named zero constructor denotes the unique finite zero. |
| `ExecFloat.P3109.decode_nan` | The named NaN constructor denotes P3109's sole NaN. |
| `Formats.P3109.Format.significand_eq_zero_iff_of_decode_eq_finite`, `decode_eq_exceptional_iff` | Only the all-zero code decodes to a zero, so there is no negative zero, and only the NaN code decodes to an exceptional value. |
| `ExecFloat.P3109.decode_positiveInfinity` | The named positive infinity has that meaning for every extended descriptor. |
| `ExecFloat.P3109.decode_negativeInfinity` | The named negative infinity has that meaning for every signed extended descriptor. |
| `ExecFloat.P3109.decode_of_ofFiniteFields?_eq_some` | A successful checked field construction has in-range fields and denotes the signed finite value they name. |
| `ExecFloat.P3109.toRat?_eq_some_iff`, `toRat?_eq_none_iff` | `toRat?` reads a value as `q` exactly when it decodes to a finite dyadic with value `q`, and gives `none` exactly for NaN and the infinities. |
| `Formats.P3109.Format.encode?_eq_some_iff` | Checked encoding returns a code exactly when that code decodes to the same datum as the input. |
| `ExecFloat.P3109.toNatBits_ofNatBits` | Low-level natural-word construction keeps exactly the low `K` bits. |
| `Formats.P3109.Format.decodePositiveFinite_strictMono` | Increasing a positive finite code strictly increases its exact rational value. |
| `Formats.P3109.Format.roundFiniteToPrecision_fitsPrecisionGrid` | Every rounding mode lands on the descriptor's finite precision grid. |
| `Formats.P3109.Format.roundFiniteToPrecision_report_spec` | The shift-based dyadic kernel follows the report's precision-rounding formula in every mode and for every supplied stochastic word. |
| `Formats.P3109.Format.roundFiniteToPrecision_toRat_eq_int_mul` | Every rounding mode returns an integer multiple of the selected quantum `2^Q`. |
| `Formats.P3109.Format.roundFiniteToPrecision_towardZero` | `towardZero` truncates: the result has no larger magnitude and lies within one quantum; `_maximal` gives the grid maximality. |
| `Formats.P3109.Format.roundFiniteToPrecision_up` | `up` is the least grid point at or above the input (with `_minimal`). |
| `Formats.P3109.Format.roundFiniteToPrecision_down` | `down` is the greatest grid point at or below the input (with `_maximal`). |
| `Formats.P3109.Format.roundFiniteToPrecision_nearestAway_abs_sub_le` | `nearestAway` is within half a quantum; `_tie` shows exact ties go to the larger magnitude. |
| `Formats.P3109.Format.roundFiniteToPrecision_nearest_abs_sub_le` | `nearest` is within half a quantum; `_tie` shows exact ties select the candidate whose P3109 code is even, and `_tie_even` gives even significands for `P > 1`. |
| `Formats.P3109.Format.roundFiniteToPrecision_toOdd_abs_sub_lt` | `toOdd` is within one quantum; `_odd` gives an odd significand for inexact rounding with `P > 1`. |
| `Formats.P3109.Format.sameDatum_decode_projectCode` | Decoding a projected code returns the datum produced by the executable round-then-saturate kernel (a representation theorem, not a rounding-direction theorem). |
| `Formats.P3109.Format.encode?_projectValue` | Checked encoding accepts every datum produced by projection. |
| `ExecFloat.P3109.decode_project` | The user-facing executable projection has the same exact datum theorem. |
| `ExecFloat.P3109.decode_projectRat` | Direct rational projection decodes to the exact round-then-saturate datum. |
| `Formats.P3109.Format.roundFiniteRatToPrecision_toRat` | Rational precision rounding equals the report's mathematical formula for every input and all nine modes, including each supplied stochastic word. |
| `Formats.P3109.Arithmetic.External.roundFinite_toRat` | External precision rounding follows that formula using the destination's declared precision and bias. |
| `ExecFloat.P3109.Conversion.implements_run` | Configured P3109 conversion implements its declared quantization relation. |
| `ExecFloat.P3109.Conversion.sameDatum_decode_run_value` | The delivered configured value decodes to the policy-selected projected datum. |
| `ExecFloat.P3109.Conversion.status_overflow_implies_outside` | A finite conversion's overflow flag implies that its exact input lies outside the destination's finite range. |
| `ExecFloat.P3109.decode_binary` | A binary operation decodes to the destination projection of its exact source values. |
| `ExecFloat.P3109.decode_ternary` | A fused ternary operation has one destination projection after its exact evaluation. |
| `ExecFloat.P3109.decode_fma_finite` | Finite fused multiply-add projects the exact rational product plus addend. |
| `Formats.P3109.Arithmetic.clamp_finite`, `ExecFloat.P3109.decode_clamp` | Ordered finite bounds give the rational interval clamp; encoding performs one report projection. |
| `Formats.P3109.Block.decode_project_lane`, `decode_convertFrom_lane` | Each lane decodes to its declared destination projection, with normalization when requested. |
| `Formats.P3109.Block.normalize_finite`, `normalize_zero`, `normalize_infinite_finite` | Ordinary division and the report's zero/infinite-scale normalization rules hold exactly. |
| `Formats.P3109.Block.sumExact_finite`, `productExact_finite`, `dotExact_finite` | Finite reductions equal exact rational sums, products, and independently scaled dot products. |
| `Formats.P3109.Block.decode_reduceAdd`, `decode_reduceMultiply`, `decode_dotProduct` | The complete exact reduction is projected only once. |
| `Formats.P3109.BlockRoot.normalize_finite_real`, `rounded_eq_real`, `decode_project` | Normalization gives the exact scaled real root, square comparisons implement its rounding, and encoding preserves the saturated datum. |
| `Formats.P3109.Arithmetic.roundSqrtRatToPrecision_eq_real` | Integer square-root comparisons select the same precision-grid value as the real square-root rounding rule. |
| `Formats.P3109.Arithmetic.sqrtRoundAway_stochasticA`, `sqrtRoundAway_stochasticB`, `sqrtRoundAway_stochasticC` | Each stochastic square-root threshold agrees with the report's floor or nearest-integer formula on the exact root fraction, for every supplied word. |
| `ExecFloat.P3109.decode_sqrt` | Executable square root decodes to the declared real-root projection, including exceptional inputs. |
| `ExecFloat.P3109.decode_rsqrt` | Reciprocal square root follows the same real-root projection after exact rational inversion. |
| `ExecFloat.P3109.decode_hypot` | Hypotenuse rounds the root of the exact sum of squares once. |
| `Formats.P3109.Arithmetic.Mixed.faa_eq_project_finite` | Fused addition projects the exact three-term sum once. |
| `Formats.P3109.Arithmetic.Mixed.scaledAdd_eq_project_finite`, `scaledMul_eq_project_finite` | Scaling and arithmetic are exact before destination projection. |
| `Formats.P3109.Arithmetic.External.project_refines` | External encoding preserves the projected finite datum, writes a zero as positive zero, and uses the specified infinity/NaN encodings. |
| `Formats.P3109.Arithmetic.External.mixed_decode_eq_decode` | A binary model operand of mixed report arithmetic decodes to the external decoder's observation, with its zero sign and NaN details erased. |
| `Formats.P3109.Format.no_decodePositiveFinite_between` | No positive finite datum lies between consecutive positive codes. |
| `ExecFloat.P3109.isNormal_or_isSubnormal` | Every finite nonzero value belongs to one of the two finite classes. |
| `ExecFloat.P3109.nextGreaterThan_of_isNaN`, `nextLessThan_of_isNaN` | Both neighbor operations propagate NaN. |

Dyadic direction theorems cover the deterministic modes. Rational and external precision rounding
have all-mode formula proofs, with direction and error bounds before saturation. For every supplied
stochastic word, the dyadic shift and square-root threshold implementations also have formula
bridges, which are deterministic statements about that word as an input.

With the raw-word constructor we can read file formats, implement wire protocols, and compare
conformance tables. Literals, conversions, and named constructors let ordinary programs write
numerical values without raw words.

## Real and executable affine quantization

`FloatLib.Numerics.Quantization.Affine.Real` provides `RealAffineQuantizer` and embeds the
executable rational `AffineQuantizer` into it with `AffineQuantizer.toReal`. The real API takes the
integer rounding function as an argument. Monotonicity, integer identity, and a local error bound
are hypotheses of their own, and only the theorem that needs one assumes it.

| Theorem | Informal statement |
| --- | --- |
| `RealAffineQuantizer.quantize_monotone` | A monotone rounder gives monotone quantization, including saturation. |
| `RealAffineQuantizer.quantize_dequantize` | Integer-preserving rounding returns every in-range reconstructed code. |
| `RealAffineQuantizer.dequantize_rawCode_error_le` | The grid scale multiplies the integer-rounding error. |
| `RealAffineQuantizer.dequantize_quantize_error_le_half` | Nearest rounding reconstructs within half a grid step when clipping is inactive. |
| `AffineQuantizer.toReal_quantize` | A real rounder agreeing with `roundRatEven` on rationals gives the executable saturated quantizer. |
| `Flocq.nearestEven_ratCast` | Real and executable rational nearest-even rounding choose the same integer, including ties. |
| `Flocq.affine_toReal_quantize` | The executable rational quantizer agrees with its real nearest-even specification. |
| `Flocq.affine_toReal_roundedValue` | Reconstruction also commutes with the rational-to-real embedding. |

You'll find the nearest-even connection in `FloatLib.Floats.Formats.Flocq.Theory.Rounding.Affine`.
If you only need executable rational quantization, you can still import
`Numerics.Quantization.Affine`.

## Theorem names and lookup

We use a few recurring names across the format families:

- `*_eq_spec` rewrites executable code to its reference definition;
- `*_refines`, `implements_*`, `spec_*`, and `preparedSpec_*` prove a relational capability;
- `toReal_*` and `toRat_*` state decoded mathematical behavior;
- `isFinite_*` establishes the side condition needed by a finite real theorem;
- `*_abs_error`, `*_relative_error`, and `*_mem_Icc` provide error or enclosure bounds;
- `*_eq_none_iff` characterizes exceptional values in optional exact views.

`#float_info YourType` lists the theorems for that type. For most configured types, such as
`Binary32`, `E4M3FN`, `Posit32`, or a fixed-point type, it lists the theorems about values of that
type first, such as `ExecFloat.Proof.add_notation_eq_spec` for `x + y`, and then the theorems about
each type those values reach, such as the proof model, the code, or the associated quire, with the
function that takes a value there. Other reports, such as those of P3109 types and Lean's native
floats, list their theorems under one heading, and each group's topic says what it is about.
Within a proof, Lean's `exact?`, `apply?`, and `rw?` can help you find a declaration that matches
the goal.
