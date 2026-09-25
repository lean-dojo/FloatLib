# Theorem index

We've collected FloatLib's major theorems here: agreement between executable arithmetic and
its specification, rounding and error bounds, exact conversions, and results for each format
family. Each table pairs the Lean names with a short statement of what we prove. The imports
appear beside their tables; proofs about individual algorithms live alongside their kernels.

For example, we can ask Lean for the full statement of the binary addition theorem with `#check`:

```lean
import FloatLib.Floats.Formats.BinaryInterchange.Semantics

#check FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt
```

We put the family and model in the namespace, leaving the theorem name to describe its
conclusion. Opening that namespace keeps applications short. The full Lean statements include
the finiteness, range, and encoding assumptions needed for each result.

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

These lemmas connect the arithmetic we write in a program to the reference operation we use
in a proof. For `+`, `-`, `*`, and `/`, they apply directly to ordinary notation, without a
`change` or unfolding step. Each format supplies its own reference operation. Its refinement
theorems then give that operation a numerical meaning, with real-valued results where the
format supports them.

For explicit cross-format computation, `ExecFloat.spec_cast` and
`ExecFloat.ConversionProof.preparedSpec_addAs`, `preparedSpec_subAs`, `preparedSpec_mulAs`, `preparedSpec_divAs`, and
`preparedSpec_fmaAs` state that exact decoding followed by one destination quantization satisfies the
destination's `Quantizer.spec` relation. Import `FloatLib.Floats.ExecFloat.Conversion.Proof` when
using these results directly.

The destination contract exposes the numerical meaning of the conversion alongside its complete
outcome. For a conventional IEEE binary descriptor, nearest-even conversion with native overflow
and gradual underflow selects a nearest finite value whenever the result is finite.
`ExecFloat.Binary.Conversion.nearestFinite_of_spec` extracts that property from a successful
configured conversion. The shared `ExecFloat.Binary.Conversion.specWith` also determines the
complete word and status for every context. Its independent nearest-value clause does not describe
other policies, tie selection, zero signs, or overflow to infinity; those use the corresponding
descriptor and policy theorems.

The numerical clauses differ with the destination:

| Destination | What its conversion contract exposes |
| --- | --- |
| IEEE binary | Distance to the input is no greater than that of any finite destination value, under the conditions above. |
| Posit | The decoded result equals real posit rounding, including minPos and maxPos behavior. |
| P3109 | The decoded datum equals the selected round-then-saturate projection; a separate word equality preserves payload details. |
| Fixed point | The nearest-even coefficient has at most half a unit of error and is even at a tie. |
| Bounded fixed point | The nearest-even coefficient is preserved or rejected when range-checked, reduced modulo `2^width` to its signed representative when wrapped, or clamped when saturated. |

Every family keeps the complete status and failure outcome. The `spec_iff_eq_run`
theorems, and binary's `specWith_iff_eq_runWith`, establish that the numerical clauses still
determine exactly one complete executable outcome.

For rewriting a concrete binary conversion,
`ExecFloat.Binary.Conversion.run_default_finite` reduces a default-context finite conversion to
`Model.roundRat`, and
`ExecFloat.Binary.Conversion.cast_eq_roundRat_of_decodeTo_eq_finite` does the same for a `cast`
whose source decodes to a finite value; `Model.Policy.roundRat_nearestEven_eq_execFloat` in
`Rounding/Policy/Proof.lean` identifies the policy rounder with `Model.roundRat`; and
`Model.toReal_roundRatScaled_eq_roundAt` in
`DirectedSemantics/Rational/RoundingSemantics/Executable.lean` together with the `cast_eq_roundAt`
family give `Model.roundRat` its real-number semantics. The other formats' sections develop
their rounding and projection theorems.

For NaN sources, `ExecFloat.Binary.Conversion.run_default_decode_of_isNaN` shows that the default
conversion returns the value and invalid flag of `Model.castWithStatus`. An IEEE destination keeps
the sign and any payload that fits; an oversized payload becomes zero. Maximum-NaN encodings keep
only the sign, while FNUZ has a single NaN. A signaling source raises invalid
(IEEE 754-2019 §6.2.3, §7.2).
That theorem needs a destination with a NaN encoding. For a fully finite destination,
`run_default_decode_of_isNaN_of_encoding_finite` shows that the conversion fails with the source NaN
as `.exceptional .source`, while `Model.castWithStatus` delivers positive zero and raises invalid
(`Model.castWithStatus_invalid_of_isNaN_of_encoding_finite`; the carrier-generic form is
`runWith_default_nan_of_encoding_finite`). Both paths treat the conversion as
invalid; `ExecFloat` refuses to invent a value. `ExecFloat.Binary.Conversion.decode_of_isNaN` gives
the NaN observation that a configured NaN decodes to.

The policy engine and directed engine agree on the complete packed result:
`Model.Policy.roundDyadicGeneral_toRoundingMode_eq_roundDyadicWithRounding` in
`Rounding/Policy/Agreement.lean` covers every `FloatFormat`, all four `IEEERoundingMode` values,
both signs, and every exact dyadic input. We keep this proof outside
`Rounding/Policy/Proof.lean` so programs that need only the policy rounder avoid compiling
the additional argument connecting the two engines.

The exact domain of every binary destination is `Numerics.SignedRat`, a rational with an IEEE sign
bit. A cast or mixed-format operation carries that sign to the destination's encoding policy:
`ExecFloat.Binary.Conversion.run_default_negZero_value?` states that converting an exact `-0` into a
binary destination delivers its `zero true`. A destination with only unsigned zero maps this to
positive zero. The `SignedRat` arithmetic lemmas
`SignedRat.value_add`, `value_sub`, `value_mul`, `value_div`, and `value_neg` say that the
rational part is ordinary rational arithmetic, while `negative_mul`, `negative_div`,
`negative_add_of_eq_zero`, and `negative_add_of_ne_zero` state the IEEE sign rules; an exact zero
sum is negative only when both operands are negative, the round-to-nearest rule. Sources whose exact
domain is `Rat` enter through `ExactMap.run_ratToSignedRat`, and binary sources decode through
`SignedRat.ofDyadic`, which keeps the dyadic sign (`SignedRat.negative_ofDyadic`).

For a longer finite algebraic calculation, `ExecFloat.ConversionProof.preparedSpec_roundOnce` states
that successful exact evaluation is followed by precisely one destination quantization.
`preparedSpec_roundOnceWith` gives the explicit-context version. `ExactExpression.div_zero` and
`div_of_not_is_zero` expose the checked-division boundary. The `ExactZero` capability gives each
exact domain one decidable zero predicate that includes canonical `0`. The `SignedRat` bridge
theorems identify that predicate with `value = 0`, so both signed zeros are recognized. The three
`ExactExpression.operand_eq_*` theorems state how finite, infinite, and exceptional operands enter
the expression.

The shared exact rational-to-integer rounder lives in
`FloatLib.Numerics.Quantization.Deterministic.Rational`. Posit integer functions and conversions
reuse it instead of maintaining separate tie rules.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.roundRatEven_nearest` | The rounded integer is at least as close as every other integer. |
| `Numerics.roundRatEven_error_le_half` | Its absolute error is at most one half. |
| `Numerics.roundRatEven_eq_of_error_lt_half` | A candidate strictly within half a unit is the unique rounded result. |
| `Numerics.roundRatEven_half_step` | Every half-integer, positive or negative, rounds to its even neighbor. |
| `Numerics.roundRatEven_eq_floor_ceil` | Quotient-based execution equals the floor/ceiling distance-and-parity decision for every rational. |

## Binary interchange formats

Import `FloatLib.Floats.Formats.BinaryInterchange.Semantics`. The names below are in
`FloatLib.Floats.Formats.BinaryInterchange.Model`.

### Finite real semantics

| Theorem | Informal statement |
| --- | --- |
| `toReal_add_eq_roundAt` | Finite IEEE addition whose executable sum is finite is the exact real sum rounded once to the format. |
| `toReal_sub_eq_roundAt` | Finite IEEE subtraction whose executable difference is finite is the exact real difference rounded once. |
| `toReal_mul_eq_roundAt` | Finite IEEE multiplication whose executable product is finite is the exact real product rounded once. |
| `toReal_div_eq_roundAt` | Division by a finite nonzero value, when the executable quotient is finite, is the exact real quotient rounded once. |
| `toReal_fma_eq_roundAt` | Finite fused multiply-add whose executable result is finite forms the exact product-plus-addend and rounds once. |
| `toReal_sqrt_eq_roundAt` | A finite nonnegative square root, including both signed zeros, is the exact real square root rounded once; no result-finiteness premise is needed. |
| `isFinite_sqrt_of_isFinite` | The square root of a finite nonnegative IEEE value never overflows. |

Each theorem explicitly assumes a conventional IEEE descriptor and the finiteness conditions
needed by a real-valued interpretation. For addition, subtraction, multiplication, division, and
fused multiply-add the finiteness of the executable result is an explicit hypothesis (`hfin` or
`hout`); it excludes overflow, which has no value in `ℝ`, and is decidable on the result. The
`*_of_abs_*_le_posMaxFinite` variants replace it by a symbolic bound on the operands. Square root
is the exception: `isFinite_sqrt_of_isFinite` shows it cannot overflow. The executable
specification also describes NaNs, infinities, invalid operations, and the signs of zeros.
Equality over `ℝ` alone cannot express those distinctions.

The corresponding `isFinite_*_of_abs_*_le_posMaxFinite` lemmas turn a symbolic magnitude bound
into the result-finiteness premise. This is usually easier than evaluating the output first.

### Powers, roots, and hypotenuse

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Algebraic.Proof`.
The `Model` theorems below have matching versions in `ExecFloat.Binary`, which apply directly
to configured values. Their real statements require a conventional IEEE descriptor, finite
operands in the function's domain, and a finite output.

| Theorem | Informal statement |
| --- | --- |
| `Model.toReal_rsqrt_eq_roundAt` | For a positive finite input, reciprocal square root rounds the exact real reciprocal root once. |
| `Model.toReal_hypot_eq_roundAt` | Hypotenuse rounds the root of the exact sum of squares, with no intermediate product rounding. |
| `Model.toReal_powInt_eq_roundAt` | A finite nonzero base raised to an integer exponent is rounded once, including negative exponents. |
| `Model.toReal_rootN_eq_roundAt` | A nonzero finite input and a nonzero integer degree give the rounded signed real root; negative inputs require an odd degree. |
| `ExecFloat.Binary.toModel_rootN`, `toModel_powInt`, `toModel_hypot`, `toModel_rsqrt` | Every storage codec preserves the complete model result, including exceptional encodings. |

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Square` for
`ExecFloat.Binary.square_eq_spec` and `square_eq_mul`: the unary square kernel produces the
same complete result as the certified multiplication specification and selected multiplication
backend. P3109 and posit squaring have corresponding `square_eq_mul` theorems.

### Casting and exact widening

Import `FloatLib.Floats.Formats.BinaryInterchange.Conversion`.

| Theorem | Informal statement |
| --- | --- |
| `cast_self_of_finite` | Casting a finite value to its own format preserves its exact encoding, including signed zero. |
| `cast_eq_roundAt` | A finite IEEE cast is one nearest-even rounding in the destination format. |
| `cast_exact_of_gridExtension` | A finite cast is exact when the destination contains the source's dyadic grid. |
| `cast_exact_of_compatibleWidening` | Increasing only fraction width while preserving exponent semantics and encoding is exact. |
| `castWithRounding_eq_widenExact_of_compatibleWidening` | Every rounding mode gives the same widened encoding for a finite value with compatible exponent fields and encoding. |
| `cast_of_isNaN`, `propagatedNaN_eq_quietNaN` | An IEEE destination quiets the NaN, keeps its sign, and keeps its payload when it fits, otherwise using payload zero (IEEE 754-2019 §6.2.3). Other encodings follow their own NaN rule; a cast to its own format is `quietNaN`. |
| `toReal_widenExact` | The direct widening constructor preserves the decoded real value, including zeros and subnormals. |

`cast_exact_of_gridExtension` is the general theorem behind standard widenings such as binary32
to binary64. It permits a larger exponent range; equal exponent widths are not required.

### Accuracy and exact subtraction

Import `FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error`,
`FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel`, or
`FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz` for scalar bounds. Import
`FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof` for the mixed-precision dot and
matrix theorems.

| Theorem | Informal statement |
| --- | --- |
| `abs_roundAt_sub_le` | Nearest-even rounding differs from its real input by at most half an ULP. |
| `relativeError_roundAt_le_of_normal` | A nonzero normal-range input satisfies the standard relative-error bound. |
| `abs_toReal_add_sub_le`, `abs_toReal_sub_sub_le`, `abs_toReal_mul_sub_le`, `abs_toReal_div_sub_le`, `abs_toReal_sqrt_sub_le`, `abs_toReal_fma_sub_le` | An IEEE operation with finite operands and result inherits the half-ULP bound under its domain hypotheses. |
| `add_exact_mem_Icc`, `sub_exact_mem_Icc`, `mul_exact_mem_Icc`, `div_exact_mem_Icc`, `sqrt_exact_mem_Icc`, `fma_exact_mem_Icc` | Under the same IEEE, domain, and finiteness hypotheses, the exact operation result lies in the computed value's half-ULP enclosure. |
| `abs_toReal_cast_sub_le` | A cast between IEEE descriptors with finite input and result inherits the destination half-ULP bound. |
| `roundAt_standardModel` | Nearest-even rounding satisfies the standard model with gradual underflow, `roundAt x = x * (1 + δ) + η` with `\|δ\| ≤ unitRoundoffAt fmt = 2^(-precision)`, `\|η\| ≤ underflowErrorAt fmt = 2^(minSubnormalExponent - 1)`, and `δ * η = 0`, for every real `x`. For binary32 the constants are `2^(-24)` and `2^(-150)`. |
| `round_standardModel_of_nearest` | The same model holds for every nearest rounding function, including ties away from zero. |
| `round_standardModel`, `roundAtDown_standardModel`, `roundAtUp_standardModel`, `round_truncRound_standardModel` | Every valid rounding function, including the directed ones, satisfies the model with both constants doubled. |
| `toReal_mul_standardModel`, `toReal_div_standardModel`, `toReal_sqrt_standardModel`, `toReal_fma_standardModel`, `toReal_cast_standardModel` | An operation on IEEE descriptors with finite operands and result satisfies the standard model with gradual underflow. Division requires a nonzero divisor; square root requires a nonnegative input, including either signed zero. |
| `roundAt_add_eq_mul_one_add` | The rounded sum of two grid points is `(x + y) * (1 + δ)` with `\|δ\| ≤ unitRoundoffAt fmt` and no underflow term, because a sum below the normal range is exact. |
| `toReal_add_eq_mul_one_add`, `toReal_sub_eq_mul_one_add`, `abs_toReal_add_sub_le_unitRoundoffAt`, `abs_toReal_sub_sub_le_unitRoundoffAt` | For an IEEE descriptor, addition or subtraction with finite operands and result has relative error at most `unitRoundoffAt fmt`, including subnormal operands and results. |
| `unitRoundoffAt_eq`, `underflowErrorAt_eq`, `two_mul_unitRoundoffAt`, `two_mul_underflowErrorAt` | The standard-model constants are the powers of two `2^(-precision)` and `2^(minSubnormalExponent - 1)`; doubling them gives the relative normal spacing and the subnormal spacing. |
| `ulpAt_eq_of_abs_lt_minNormalAt`, `ulpAt_le_of_minNormalAt_le` | Below the normal range one ULP is the subnormal spacing; in the normal range it is at most `2^(1 - precision) * \|x\|`. |
| `mulAccError_eq_site_residuals` | One mixed-precision multiply-accumulate error is exactly the sum of its two input-cast, product, accumulator-cast, and addition residuals. |
| `mulAcc_abs_error_le_budget` | A finite mixed-precision multiply-accumulate is bounded by the corresponding five local half-ULP budgets. |
| `sequentialAccumulator_error_eq_sum` | Sequential accumulation error telescopes exactly into the errors committed at its executed prefix states. |
| `dotSequential_eq_cast_sequentialAccumulator` | The executable sequential dot loop is its prefix accumulator followed by the output cast. |
| `dotSequential_abs_error_le_budget` | A finite executable mixed-precision dot is bounded by all per-step site budgets plus the final output-cast budget. |
| `matmul_refines` | A successful matrix product has the expected row and column shape, and every entry is the corresponding executable sequential dot. |
| `matmul_entry_abs_error_le_budget` | Any selected successful matrix entry inherits the sequential-dot budget without a separate matrix error model. |
| `toReal_sub_eq_of_sterbenz` | Two positive finite values within a factor of two subtract exactly; result finiteness follows from those hypotheses. |

`roundAt`, `ulpAt`, and `minNormalAt` use the descriptor's declared exponent bias, including FNUZ
and custom encodings. The grid has no upper exponent bound. `toReal_genericFormat_of_isFinite`
and `roundAt_toReal_eq` apply to every finite decoded word without an IEEE premise; connecting an
arithmetic operation to that grid still requires its operation-specific refinement hypotheses.

The relative-error theorem requires the normal range. Near zero, absolute error is
the useful statement because gradual underflow prevents a uniform relative bound.

### IEEE status flags

Import `FloatLib.Floats.Formats.BinaryInterchange.Status`.

The executable operations `addWithStatus`, `subWithStatus`, `mulWithStatus`, `divWithStatus`,
`fmaWithStatus`, and `sqrtWithStatus` return the result together with its five IEEE flags.
Theorems such as `addWithStatus_value`, `addWithStatus_invalid`,
`divWithStatus_divideByZero`, and `dyadicRoundingStatus_overflow` describe those returned fields
directly.

Overflow is determined by first rounding to the destination precision with an unbounded exponent
range. Thus a direction that increases magnitude overflows immediately above the largest finite
value, while toward-zero and a direction back into the finite range do not overflow until the
rounded significand enters the next binade. `dyadicRoundingStatus_overflow` and
`rationalRoundingStatusScaled_overflow` expose that classification for dyadic and signed-rational
inputs, respectively.

The value-only `roundToIntegral` is the flagless IEEE 754-2019 §5.9 `roundToIntegral{TiesToEven,
TowardZero, TowardPositive, TowardNegative}` family. `roundToIntegralExactWithStatus` is §5.9
`roundToIntegralExact` under an explicit direction: it first rounds the exact input to an integer,
encodes it in the same direction, and additionally raises `inexact` on fractional input
(`roundToIntegralExactWithStatus_inexact_iff`). `overflow` is raised only for a custom descriptor
whose finite range ends below the rounded integer; `roundToIntegralExactWithStatus_overflow_eq_false`
shows this never happens when `fmt.fracWidth ≤ fmt.maxNormalExponent`, which every IEEE interchange
format satisfies, and `isFinite_roundToIntegral` with `toReal_roundToIntegral_{towardNegativeInfinity,
towardPositiveInfinity, towardZero, nearestEven}` then give the result the real value `⌊x⌋`, `⌈x⌉`,
the truncation of `x`, or the nearest-even integer. A finite-only encoding saturates in the remaining
custom cases, so an overflow result need not itself be an integer.

`remainderWithStatus` reports a clear status on finite operands with a nonzero divisor because the exact remainder is
always representable: `remainderWithStatus_exact` proves the delivered value is finite and denotes
the exact dyadic remainder for every conventional IEEE descriptor.

`minimumNumber` and `maximumNumber` are the IEEE 754-2019 §9.6 operations: a signaling NaN operand
is skipped like a quiet one (`minimumNumber_of_isNaN_left`), and `minimumNumberWithStatus`
reports the owed `invalid` (`minimumNumberWithStatus_invalid`). `minNum` and `maxNum` remain as
the deprecated 754-2008 operations, which quiet-propagate a signaling NaN instead. `nextUpWithStatus`
and `nextDownWithStatus` likewise add the §5.3.1 `invalid` indicator to the quiet `nextUp` and
`nextDown`.

Underflow uses the documented after-rounding, tiny-and-inexact rule. Quiet NaN propagation and
generated invalid operations are handled by the executable operation semantics, then
characterized by theorems in `Status.Proof`.

### Configured explicit rounding and status

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof`. The value-only configured
operations are `ExecFloat.Binary.addWithRounding`, `subWithRounding`, `mulWithRounding`,
`divWithRounding`, `fmaWithRounding`, and `sqrtWithRounding`. Operands come first,
followed by a required rounding argument, supplied positionally or by name as
`(rounding := .towardPositiveInfinity)`. Their
`*WithStatus` counterparts
return the configured value and `Model.IEEEStatus` as a pair, so no stored word appears in
application code.

After `open scoped FloatLib.IEEERounding`, the two directed-infinity modes may also be written
`(rounding := +∞)` and `(rounding := -∞)`. The notation is scoped so it cannot silently replace
extended-real infinity notation in importing files.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.IEEEOutcome.toModel_ofModel` | Repacking and decoding a model outcome preserves both its delivered value and all five status flags. |
| `ExecFloat.Binary.toModel_addWithRounding`, `toModel_subWithRounding`, `toModel_mulWithRounding`, `toModel_divWithRounding`, `toModel_fmaWithRounding`, `toModel_sqrtWithRounding` | Decoding a configured directed operation gives the descriptor-model operation `Model.addWithRounding rounding` (and its five siblings) on the decoded operands. |
| `ExecFloat.Binary.IEEEOutcome.toModel_addWithStatus`, `toModel_subWithStatus`, `toModel_mulWithStatus`, `toModel_divWithStatus`, `toModel_fmaWithStatus`, `toModel_sqrtWithStatus` | Decoding a configured status-bearing operation gives the descriptor-model outcome, value and all five flags. |

The configured functions are direct repackings of the existing descriptor-model operations, and
the bridge theorems above are `simp` lemmas, so a goal about a configured directed operation
reduces to the corresponding `Model` theorem in `Status.Proof` or `DirectedSemantics`.

We accumulate sticky flags with `FloatLib.Numerics.IEEEStatus.union`.
Binary and decimal statuses share `Numerics.IEEEStatus`; the format-specific names are
abbreviations of the same record. Selection, clearing, saving, testing, and restoration also
share one implementation. `Numerics.IEEEStatus.Proof` proves their laws for every flag state
and selected group; the decimal namespace exports those results.

### Quiet and signaling comparisons

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Comparison.Proof`.
All 22 named predicates use `Numerics.IEEEComparison`'s shared truth tables. Model and
configured operations return the same Boolean-and-flags result type used by decimal comparison.

| Theorem | Informal statement |
| --- | --- |
| `Model.compare_eq_of_toEReal?` | Non-NaN operands compare according to their exact extended-real values, including infinities. |
| `Model.Comparison.quiet_value_of_toEReal?`, `signaling_value_of_toEReal?` | Every predicate applies its truth table to that exact numerical order. |
| `Model.Comparison.quiet_value_of_nan`, `signaling_value_of_nan` | A NaN operand selects the predicate's unordered truth value. |
| `Model.Comparison.quiet_invalid_iff`, `signaling_invalid_iff` | Quiet comparison raises invalid for signaling NaNs; signaling comparison raises it for either kind of NaN. |
| `ExecFloat.Binary.compareQuiet_value_of_toEReal?`, `compareSignaling_value_of_toEReal?` | The same numerical contracts hold through every lawful configured storage codec. |

### Total ordering of representations

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Proof`.
The executable finite comparison reuses the scalable dyadic comparator and is proved equal
to an exact lexicographic specification. All descriptor policies, widths, and biases use this
same implementation. These operations preserve NaN metadata and raise no exceptions.

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

Import `FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Roundtrip` and
`FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.PrecisionProof`.
`formatDecimal` and `formatHex` are explicit external representations; ordinary `format`
keeps its compact diagnostic display.

| Theorem | Informal statement |
| --- | --- |
| `Model.parse_formatHex_of_isFinite` | Every finite IEEE word round-trips through exact hexadecimal text in all input modes, including signed zero. |
| `Model.parse_formatDecimal_of_isFinite` | Every finite IEEE word round-trips through exact decimal text with nearest-even input. |
| `Model.significantDecimal_coefficient_bounds`, `Model.significantHex_coefficient_bounds` | Nonzero output has exactly the requested positive number of significant digits in every mode. |
| `Model.significantDecimal_nearestEven_error`, `Model.significantHex_nearestEven_error` | Nearest-even output stays within half the selected text-grid step. |
| `Model.formatDyadicText_decimal_inexact_iff`, `Model.formatDyadicText_hexadecimal_inexact_iff` | Output raises inexact exactly when its numerical value changes. |
| `Model.formatWithStatus_exact_status` | Exact output leaves all five exception indicators clear. |

The finite exact-output theorems do not establish the minimum decimal digit count (`Pmin`)
needed for a round trip. Universal NaN/infinity word recovery and the three directed output
inequalities also remain outside this proof API.

### Certified execution backends

Import `FloatLib.Floats.ExecFloat`. The public equations `ExecFloat.Proof.*_eq_spec` hold for
every configured binary type regardless of which backend the planner selects, because each
backend enters through a `Backend.Certified` candidate whose certificate is one of the theorems
below. The kernels are proved against the descriptor model, so the same theorem serves every
format the kernel is eligible for.

| Theorem | Informal statement |
| --- | --- |
| `Model.NativePair.addFinite_eq`, `subFinite_eq`, `fmaFinite_eq` | On two 64-bit words, for every IEEE layout of at most 128 bits whose fraction is wider than one word (`NativePair.Eligible`), the fast finite addition, subtraction, and fused multiply-add agree with the exact finite kernel whenever they accept. |
| `Model.NativePair.mulNormalLimb_refines`, `divNormal_refines`, `sqrtNormal_refines` | The two-word normal multiplication, division (Algorithm D candidate, independent certificate, proved restoring repair), and square root refine the reference specification under the same eligibility. |
| `Model.WideLimb.toModel_add`, `toModel_sub`, `toModel_mul`, `toModel_div`, `toModel_sqrt`, `toModel_fma` | On the 32-bit limb carrier of `ExecFloat.BinaryLimbs`, for every IEEE layout wider than 128 bits with an exponent field of at most 32 bits, all six operations decode to their complete `Model.Spec` results. Division uses a direct integer quotient for finite inputs; square root uses an integer root for positive normal inputs, with exact fallbacks elsewhere. |
| `Model.NativeSmallWordAdd.addFinite_refines` | The all-`UInt64` addition and subtraction kernel for IEEE layouts within one machine word refines the exact finite kernel whenever it accepts. |

## Lean's native float model

Import `FloatLib.Floats.Formats.IEEE754`, or the usual `FloatLib` root. We're glad Lean 4.34
exposes more of its float model: we can now connect its signed integer casts and integer
constructors to our rounding specifications. The arithmetic bridges also relate ordinary
Lean expressions to FloatLib's configured operations.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.toFloat32_ofFloat32`, `toFloat_ofFloat` | Every native value survives importing into FloatLib and exporting again. |
| `ExecFloat.Binary.toModel_ofFloat32_nan`, `toModel_ofFloat_nan` | Lean's named NaN constants import as FloatLib's canonical NaN. Corresponding `inf` theorems identify positive infinity. |
| `Model.ofInt_conversion_spec` | Lean's integer constructor satisfies FloatLib's complete default conversion specification for any conventional IEEE descriptor. |
| `ExecFloat.Binary.toModel_ofFloat_ofNat`, `toModel_ofFloat32_ofNat` | Native natural constructors round the entire unbounded input with FloatLib's rational rounder. |
| `ExecFloat.Binary.toModel_ofFloat_intToFloat`, `toModel_ofFloat32_intToFloat32` | Unbounded `Int` casts agree with FloatLib's dyadic rounder, including negative values and overflow. |
| `ExecFloat.Binary.toModel_ofFloat32_int64ToFloat32`, `toModel_ofFloat_int64ToFloat` | Signed integer casts agree with FloatLib's nearest-even integer conversion. The other native signed widths have corresponding lemmas. |
| `ExecFloat.Binary.float32ToInt8_eq_floatToIntSaturating`, `floatToInt8_eq_floatToIntSaturating` | Native signed casts truncate toward zero and saturate; NaN maps to zero. The other signed widths have corresponding lemmas. |
| `ExecFloat.Binary.ofFloat32_add_of_isFinite`, `ofFloat_add_of_isFinite` | On finite operands, importing a native sum equals adding the imports, including signed zeros and overflow. Corresponding subtraction lemmas have the same scope. |
| `Model.canonicalizeModel_sqrt_eq_model` | For every conventional IEEE input, square root agrees with Lean's model after NaN canonicalization. |
| `ExecFloat.Binary.toFloat32_sqrt`, `toFloat_sqrt` | Configured square root commutes with native export on every input. |

The `Model` names here belong to `Formats.BinaryInterchange.Model`. These are equalities with
Lean's logical definitions; execution of native calls also trusts the compiler, runtime,
and hardware. Our software operations retain their existing refinement certificates.

## Configured binary transcendentals

We provide these functions through the optional
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals` import (or the model barrel
`BinaryInterchange.Transcendentals`), separately from `import FloatLib`.
Applications can then call `ExecFloat.Binary.exp`, `log`,
`sin`, `cos`, `sinCos`, `sinh`, `cosh`, and `tanh` without unpacking the configured carrier, and
can use `Model.pow` / `x ^ y` on a binary model. The same import installs `MathFunctions` on
`ExecFloat.Binary` and `Model fmt`; certified `sqrt` and `abs` remain available without it.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.toModel_exp`, `toModel_log` | Configured exponential and logarithm are exactly their deterministic model kernels after decoding. |
| `ExecFloat.Binary.toModel_sin`, `toModel_cos`, `toModel_sinCos` | Configured trigonometric calls preserve the corresponding model result; `sinCos` shares argument reduction. |
| `ExecFloat.Binary.toModel_sinh`, `toModel_cosh`, `toModel_tanh` | Configured hyperbolic calls preserve the corresponding model result. |

These theorems connect configured calls to their model results. General real-error bounds and
correct-rounding proofs for these value-only kernels remain open, and the calls return no IEEE
status flags. The optional Arb adapter supplies externally trusted real enclosures and explicit
rounding modes.

`Model.Power.toReal_pow_of_eq_intCast` covers a separate case: for an IEEE descriptor, a finite
nonzero base, and a finite floating exponent whose real value is an integer, every finite
`Model.pow` result is one nearest-even rounding of the exact integer power.

For IEEE binary formats, `ExecFloat.Binary.Certified.exp`, `log`, `expMinus1`, and `logPlus1`
refine proved rational enclosures until both endpoints round to the same finite encoding.
The stable variants perform the subtraction or addition of one exactly before rounding.
They return `some result` on success and `none` for rejected inputs or exhausted refinement.
The theorems below are partial correctness: they describe every `some` result, but no theorem
says which inputs succeed. The only proved success is the signed-zero passthrough
`Model.Transcendentals.Certified.expMinus1_of_isZero` and `logPlus1_of_isZero`. The focused
`Configured.Transcendentals.Certified` import exposes this API without installing the approximation
functions. Its options control the starting degree and number of direct enclosure attempts.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.Certified.toModel_exp`, `ExecFloat.Binary.Certified.toModel_log` | Decoding preserves the certified model kernel's optional result. |
| `ExecFloat.Binary.Certified.isFinite_of_exp_eq_some`, `ExecFloat.Binary.Certified.isFinite_of_log_eq_some` | Every accepted result is finite. |
| `ExecFloat.Binary.Certified.toReal_of_exp_eq_some`, `ExecFloat.Binary.Certified.toReal_of_log_eq_some` | An accepted result equals nearest-even real rounding of the exact exponential or logarithm. |
| `ExecFloat.Binary.Certified.toReal_of_expMinus1_eq_some`, `ExecFloat.Binary.Certified.toReal_of_logPlus1_eq_some` | An accepted result is one nearest-even rounding of `Real.exp x - 1` or `Real.log (1 + x)`, without first rounding the exponential or the sum. |

`ExactExpression` and `roundOnceWith` round once when the expression is exact in their chosen
domain. A rational domain cannot represent `log`, `sin`, or `tanh` in general, so composing the
current transcendental kernels approximates and rounds at each function boundary. Correctly
rounding a whole transcendental composition requires a certified real enclosure or another
exact-real procedure; it cannot be obtained by treating the expression as rational arithmetic.

## Repeatedly rounded reductions

`FloatLib.Numerics.Reduction.Tree` describes nonempty binary evaluation schedules.
`FloatLib.Numerics.Reduction.Error` proves bounds from local error assumptions at the actual
operand pairs. These modules are independent of any format or tensor library.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.ReductionTree.abs_eval_sub_exact_le_errorBudget` | The total error is at most the sum of allowances at the internal nodes. |
| `Numerics.ReductionTree.abs_eval_sub_exact_le_nodeCount` | A uniform absolute allowance is paid once per addition. |
| `Numerics.ReductionTree.abs_eval_sub_exact_le_mixedBudget` | Relative and absolute local errors give a recursive bound using exact subtree sums. |
| `Numerics.ReductionTree.abs_eval_sub_exact_le_geometric` | Under local relative bounds, leaf count and absolute-input scale give a schedule-independent geometric enclosure. |
| `Model.ReductionTree.abs_toReal_eval_sub_sum_le` | Every finite IEEE reduction tree has a sum-of-half-ULPs bound, including subnormal intermediate results. |
| `Model.ReductionTree.abs_toReal_eval_sub_eval_le` | Two finite schedules over the same input occurrences differ by at most their combined budgets. |
| `Model.ReductionTree.allNodes_abs_toReal_add_sub_le` | Every finite addition in an IEEE tree meets the local relative premise with `u = unitRoundoffAt fmt` and no absolute allowance. |
| `Model.ReductionTree.abs_toReal_eval_sub_sum_le_mixedBudget` | Every finite IEEE reduction tree satisfies the mixed-budget bound with `u = unitRoundoffAt fmt` and zero absolute allowance, including subnormal intermediate results. |
| `Model.ReductionTree.abs_toReal_eval_sub_sum_le_geometric` | Every finite IEEE reduction tree with `n` additions has error at most `((1 + u)^n - 1) * Σ\|xᵢ\|`, with no normal-range hypothesis. |

The model results live in `BinaryInterchange.Reduction.Tree`. They require finite leaves and
finite intermediate additions. They do not identify arbitrary native CPU or GPU reductions
with a particular tree; a downstream execution proof must establish that connection.

## Correctly rounded reductions

Import
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction` for configured values or
`FloatLib.Floats.Formats.BinaryInterchange.Reduction` for mixed source and destination
descriptors.

The model reducer decodes every finite term into an exact dyadic, accumulates the full sum or
product sum, and invokes the ordinary descriptor rounder once. The configured API changes the
carrier before and after that model operation.

| Theorem | Informal statement |
| --- | --- |
| `Model.Reduction.Internal.array_foldl_pushValue_exact_toRat` | The executable sum accumulator denotes the exact rational sum of all finite inputs. |
| `Model.Reduction.Internal.dotState_exact_toRat` | The dot accumulator denotes the exact rational sum of exact products. |
| `Model.Reduction.sumWithStatus_eq_round_of_finite_nonzero` | A nonzero finite sum performs one final dyadic rounding and returns exactly that rounding's status. |
| `Model.Reduction.sumWithStatus_eq_zero_of_finite` | An exact-zero finite sum follows the documented signed-zero rule and raises no status flag. |
| `Model.Reduction.dotWithStatus_eq_round_of_finite_nonzero` | A nonzero finite dot performs one final dyadic rounding and returns exactly that rounding's status. |
| `Model.Reduction.dotWithStatus_eq_zero_of_finite` | An exact-zero finite dot follows the documented signed-zero rule and raises no status flag. |
| `Model.Reduction.sumAccumulator_toRat_eq_of_perm` | Permuting finite summands preserves the exact rational accumulator; NaN selection remains traversal-order dependent. |
| `Model.Reduction.dotWithStatus_lengthMismatch` | Unequal lengths return both observed lengths without evaluating a truncated dot product. |
| `ExecFloat.Binary.IEEEOutcome.toModel_sumWithStatus` | Decoding a configured sum preserves its complete model result and status. |
| `ExecFloat.Binary.dotWithStatus_eq_model` | Configured dot execution is exactly the model result, including errors and status. |

`Model.Reduction.Semantics.finiteDot_singleton` records the mathematical one-product case behind
FMA. An FMA chain rounds each prefix, so its result can differ from an exact dot product.
Signed-zero and exceptional-value choices can also differ. The executions agree
only when every intermediate round is exact and those edge rules align.

The external MPFR oracle covers binary16, bfloat16, binary32, binary64, binary128, and binary256,
all four rounding modes, and wider-source mixed-precision cases. Fixed encoding regressions
separately exercise NaN choice, infinities, signed zero, overflow, underflow, `0 * ∞`, and explicit
length errors.

## Decimal interchange

Import `FloatLib.Floats.Formats.DecimalInterchange.Basic`.

The `Encoding` API supports BID and DPD through one descriptor, with decimal32, decimal64, and
decimal128 as named presets. A custom layout chooses a declet count, a positive exponent-field
width, and an arbitrary bias; its precision is `3 * declets + 1`. These
theorems preserve the full datum: coefficient, quantum exponent, signed zero, and exceptional
fields. In particular, equal numerical values with different cohort exponents remain distinct.

| Theorem | Informal statement |
| --- | --- |
| `Encoding.decode_valid` | Every word decodes to a valid datum for its width. |
| `Encoding.decode_of_encode?_eq_some` | Successful checked encoding round-trips the complete datum. |
| `Encoding.decode_canonicalize` | Canonicalization changes no datum fields. |
| `Encoding.canonicalize_idempotent` | A canonical word is unchanged by further canonicalization. |
| `decode_transcode` | Conversion between BID and DPD preserves the complete datum. |
| `transcode_transcode` | Conversion to the other encoding and back produces the canonical source word. |

Import `FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Basic` for core arithmetic and
its numerical guarantees. The operations consume and return complete `Datum` values, with all
five rounding modes and explicit exception flags.

Decimal `Status` is an alias of `FloatLib.Numerics.IEEEStatus`. Flag selection, clearing,
restoration, and their laws use that shared namespace.

| Theorem | Informal statement |
| --- | --- |
| `Arithmetic.add_valid`, `sub_valid`, `mul_valid`, `div_valid`, `fma_valid` | Each operation returns a valid destination datum. |
| `Arithmetic.add_error_le_half`, `mul_error_le_half`, `div_error_le_half`, `fma_error_le_half` | Under the stated finite nearest-rounding hypotheses, error is at most half the selected quantum. |
| `Arithmetic.sqrt_error_le_half` | Exact squared comparisons give the corresponding square-root rounding bound. |
| `projectMagnitude_exact`, `projectMagnitude_exact_status` | Representable rational values are preserved numerically and do not raise inexactness. |
| `le_project_towardPositive`, `project_towardNegative_le` | Directed projection lies on the requested side of the exact input when the result is finite. |
| `Arithmetic.add_inexact_iff`, `Arithmetic.fma_inexact_iff` | The inexact flag records a change in the exact numerical result. |
| `project_underflow_iff` | Underflow combines inexactness with decimal tininess before rounding. |
| `Arithmetic.add_zeros`, `Arithmetic.sqrt_zero` | Zero results follow the stated sign and preferred-exponent rules. |
| `projectMagnitude_quantum_closest`, `Arithmetic.sqrt_quantum_closest` | Exact nonzero results select a representable cohort exponent closest to the preferred exponent. |
| `projectMagnitude_inexact_quantum_minimal`, `Arithmetic.sqrt_inexact_quantum_minimal` | Inexact finite results use the least representable quantum exponent. |
| `Arithmetic.quantize_same_quantum`, `Arithmetic.quantize_inexact_iff` | Successful quantization uses the requested quantum, with inexactness exactly when the value changes. |
| `Arithmetic.quantize_error_le_half`, `Arithmetic.quantize_error_lt_one` | Quantization satisfies the nearest or directed error bound in units of the requested quantum. |
| `Arithmetic.roundToIntegralExact_integer`, `Arithmetic.roundToIntegralExact_inexact_iff` | Finite integral rounding produces an integer and reports whether rounding changed the value. |
| `Arithmetic.roundToIntegral_value`, `Arithmetic.roundToIntegral_inexact` | Quiet integral rounding preserves the same rounded value and suppresses the inexact flag. |
| `Comparison.relation_sameCohort` | Numerical comparison is unchanged when operands are replaced by equal cohort members. |
| `Comparison.quiet_invalid_iff`, `Comparison.signaling_invalid_iff` | Quiet and signaling comparisons raise invalid on their specified NaN classes. |
| `Datum.totalOrder_trans`, `Datum.totalOrder_total`, `Datum.totalOrder_antisymm_iff` | Total ordering distinguishes complete datums, including cohort exponents and NaN data. |
| `Datum.sameCohort_isNormal`, `Datum.sameCohort_isSubnormal` | Normal and subnormal classification depends on the value, not its cohort exponent. |
| `Arithmetic.nextUp_adjacent`, `Arithmetic.nextDown_adjacent` | No valid finite datum lies strictly between an input and its delivered neighbor. |
| `Arithmetic.nextUp_quantum_minimal`, `Arithmetic.nextDown_quantum_minimal` | Finite nonzero neighbors use the finest representable quantum. |
| `Arithmetic.remainder_value`, `Arithmetic.remainder_error_le_half_divisor` | The exact nearest-even remainder is representable and has magnitude at most half the divisor. |
| `Arithmetic.remainder_even_at_midpoint` | A remainder at half the divisor uses an even integer quotient. |
| `Arithmetic.scale_exact_value`, `Arithmetic.scale_inexact_iff` | Scaling preserves representable exact values and reports numerical rounding precisely. |
| `Arithmetic.scale_quantum_closest_of_representable` | Exact scaling chooses the cohort quantum closest to the shifted input quantum. |
| `Arithmetic.decimalExponent_bounds`, `Arithmetic.decimalExponent_eq_of_equal_magnitude` | The finite exponent query bounds the input by consecutive powers of ten and is unchanged by cohort or sign. |
| `Formatting.parse_formatExact`, `Formatting.parseWord_formatWord_exact` | Exact text preserves complete datums and canonical BID/DPD words. |
| `Formatting.significantDecimal_error_le_half`, `Formatting.significantDecimal_nearestEven_midpoint` | Requested-precision output satisfies the nearest error bound and resolves even ties. |
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

The algebraic operations add exact integer powers, reciprocal square root, hypotenuse, and
integer roots. Import `FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Proof`; each
operation accepts all five rounding modes and works with custom decimal layouts.

| Theorem | Informal statement |
| --- | --- |
| `Arithmetic.square_valid`, `powInt_valid`, `rsqrt_valid`, `hypot_valid`, `rootN_valid` | The delivered datum is valid for the destination format. |
| `Arithmetic.square_error_le_half`, `powInt_error_le_half`, `rsqrt_error_le_half`, `hypot_error_le_half`, `rootN_error_le_half` | A finite nearest-rounded result is within half the selected decimal grid step of the exact real expression, under its domain hypotheses. |
| `Arithmetic.rootN_error_lt_one` | For a finite nonzero input and a nonzero degree in the real domain, every rounding mode has error strictly less than one selected grid step when no overflow occurs. |
| `Arithmetic.rootN_towardNegative_le`, `le_rootN_towardPositive` | Directed roots lie on their requested side of the exact root when no overflow occurs. |
| `Arithmetic.rootN_inexact_iff`, `rootN_underflow_iff` | Root status records numerical inexactness and tininess before rounding. |
| `Arithmetic.integerRoot_pow_natAbs` | The real root specification satisfies its defining power equation, using the reciprocal operand for a negative degree. |

The optional import
`FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof` supplies stable
`expMinus1` and `logPlus1` and their correctness theorems. In its `Transcendentals.Certified`
namespace, `toReal_of_expMinus1_eq_some` and `toReal_of_logPlus1_eq_some` identify a successful
result with nearest-even rounding of `Real.exp x - 1` and `Real.log (1 + x)`. The returned datum
is valid and finite; valid signed zeros keep their quantum. An inconclusive enclosure or an
invalid domain returns `none`. This is partial correctness: no theorem says which inputs
succeed, except that a valid signed zero passes through (`expMinus1_of_isZero`,
`logPlus1_of_isZero`).

Conversions reuse exact source decoding and one destination projection:

| Theorem | Informal statement |
| --- | --- |
| `Conversion.convertFormat_error_le_half` | Decimal-to-decimal nearest rounding has at most half a selected quantum of error when it does not overflow. |
| `Conversion.fromBinary_zero_clamped`, `Conversion.fromPosit_zero_clamped` | Zero conversion chooses a valid quantum for every descriptor, even when quantum zero is unavailable. |
| `Conversion.toPosit_eq_real` | A finite decimal converts to the standard posit rounding of its exact real value, including saturation and nonzero underflow. |
| `Conversion.Integer.convertToInteger_invalid_iff` | Integer conversion fails exactly for an exceptional source or a rounded integer outside the destination range. |
| `Conversion.Integer.convertToInteger_error_le_half` | Successful nearest integer conversion has at most half a unit of error. |
| `Conversion.Integer.convertFromInt_exact` | Every representable integer converts to its exact decimal value. |

The binary destination adapter requires an IEEE descriptor. Its nearest-mode equalities require
a finite output; directed modes provide extended-real bounds. NaN conversion preserves fitting
payloads, quiets signaling NaNs, and raises invalid for them. The convenience results that deliver
decimal quantum zero state `[f.HasQuantumZero]`; the general clamped results need no bias bounds.

## Posits and quires

Import `FloatLib.Floats.Formats.Posit`.

The exact semantic view is `Model.toRat?`. It returns `none` exactly for the unique NaR word:

| Theorem | Informal statement |
| --- | --- |
| `Model.toRat?_eq_none_iff` | Exact rational decoding fails exactly for NaR. |
| `Model.toRat?_eq_toDyadic?_map` | Rational and dyadic views agree on every word. |
| `Model.compareLess_eq_true_iff` | Encoded strict comparison agrees with signed-word order. |
| `Model.toProjectiveRat_eq_infty_iff` | The optional projective view reaches its added point exactly for NaR. |
| `Model.toRat?_widen` | Appending any number of zero bits preserves the complete optional exact value, including zero and NaR. |
| `Model.roundRat_widen` | Rounding an exactly decoded finite source into a wider posit produces its zero-extended word. |
| `ExecFloat.Posit.decode_ofModel_widen` | Every lawful configured codec preserves complete decoding under zero-extension, including zero and NaR. |
| `ExecFloat.Posit.Conversion.run_default_widen` | Default configured conversion to any wider posit returns the zero-extended word. |

The projective theorem is an interoperability result. It does not redefine NaR as a posit
infinity; the primary semantics retains `ExceptionalValue.notAReal`.

The elementary functions have real-valued rounding theorems, rather than only agreement with
an executable approximation:

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

Separate domain and NaR theorems specify invalid inputs. The configured posit carriers export
the corresponding results through their model bridge. The natural exponential/logarithm search
terminates by separating irrational targets from rational boundaries; exact rational cases
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

The configured user carrier also exports `ExecFloat.Posit.Quire.toRat?_pToQ`,
`ExecFloat.Posit.Quire.toRat?_foldl_qMulAdd_zero`, and `ExecFloat.Posit.Quire.toRat?_foldl_qAddP_zero`,
so ordinary programs do not need to unwrap storage codes to use the conversion or capacity
theorems. The hypothesis `exactProducts? pairs = some products` (or `exactValues?`) states that no
input is NaR and names the exact rational terms.

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
| `ExecFloat.BoundedFixedPoint.toRat_of_checkedAdd_eq_some` | Configured checked addition is exact: any returned value decodes to the rational sum (likewise `toRat_of_checkedSub_eq_some`, `toRat_of_checkedMul_eq_some`). |
| `ExecFloat.BoundedFixedPoint.checkedAdd_eq_some` | Configured checked addition succeeds when the exact coefficient sum fits the width (likewise `checkedSub_eq_some`, `checkedMul_eq_some`). |
| `ExecFloat.BoundedFixedPoint.toRat_saturatingAdd` | Configured saturating addition decodes to the exact coefficient sum clamped to the signed range (likewise `toRat_saturatingSub`, `toRat_saturatingMul`). |
| `Logarithmic.Code.toReal_mul` | Multiplication of logarithmic codes is exact real multiplication. |
| `Logarithmic.Code.toRat_mul` | The same multiplication is exact in the rational decoder. |

The fixed-point result type records the composed fractional scale. We state separate theorems
for bounded wrapping and saturating operations because they reduce or clamp the coefficient
when an exact result leaves the representable range.

## Named codebook values

Import `FloatLib.Floats.Formats.Codebook`. Arbitrary codebooks cannot have a generic inverse
constructor because a table may be non-injective or contain exceptional entries. Named catalog
tables instead expose semantic constructors. The bipolar table provides
`ExecFloat.Codebook.Catalog.bipolar1.negativeOne` and `positiveOne`; the ternary table provides
`zero`, `negativeOne`, `positiveOne`, and `reserved` in its own namespace.

The corresponding `decode_negativeOne`, `decode_positiveOne`, `decode_zero`, and
`decode_reserved` theorems state their complete `NumericalValue Int` meanings. Application code
therefore does not need to know any catalog bit pattern.

`Codebook.nearestCode` is a deterministic nearest-codeword quantizer: `Codebook.nearestCode_spec`
states that its result is a finite codeword minimizing `|x - c|` over all finite codewords.
The runtime resolves ties to the lower word; this theorem establishes distance minimality.

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

The dot products accept different element profiles on their two sides. Exact accumulation is
FloatLib's choice of the internal precision permitted by MX; the scale-selection theorem does
not claim global optimality over other shared scales.

`Numerics.Interval α` stores arbitrary endpoint representations. Its partial arithmetic uses
`Numerics.OutwardRounding α β`: a scalar decoder and a certified partial enclosure function.
The generic corner bounds apply over any ordered field. Successful finite operations preserve
containment; unavailable enclosures, exceptional inputs, and zero-crossing division return
`none`. Concrete binary, decimal, and posit adapters use exact rational scalar arithmetic.
`Interval.ContainsReal` interprets those rational endpoints in the reals; the
`containsReal_add?`, `containsReal_sub?`, `containsReal_mul?`, and `containsReal_div?` theorems
cover arbitrary real members, not only rational inputs. `contains_fma?` proves the
ordered-field multiply-add enclosure; `containsReal_fma?` gives its real interpretation,
with outward rounding applied only after the product and addend are combined.

`Numerics.Interval.Expr` composes arithmetic, natural powers, and elementary functions.
Its `containsReal_eval?` theorem proves real containment for any backend satisfying
`Numerics.Interval.Backend.Sound`. The `rational_sound`, `binaryGrid_sound`, and
`ofRounding_sound` theorems establish this contract for exact rational endpoints,
integer binary-grid endpoints, and custom outward rounders, respectively.
`Expr.check_sound` proves inequalities over a rational box, including adaptive subdivision;
the `interval` tactic uses it to produce kernel-checked proofs from local real bounds.
The elementary containment theorems include `containsReal_tanBounds?`,
`containsReal_asinBounds?`, `containsReal_acosBounds?`, `containsReal_sinhBounds`,
`containsReal_coshBounds`, and `containsReal_tanhBounds`. Inverse sine and cosine check
the `[-1, 1]` domain; tangent checks that its cosine enclosure excludes zero.

Configured binary endpoints are available through
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval`. The
`ExecFloat.Binary.Interval.toModel_ofModel` and `ofModel_toModel` theorems preserve complete
endpoint encodings. The `toModel_*` lemmas identify every configured operation with the existing
model operation. Its `add_sound`, `sub_sound`, `mul_sound`, and `div_sound` theorems transport
the model's real-enclosure guarantees, including their descriptor and validity hypotheses.
Range-checked finite-encoding results remain separate from IEEE extended-real results.

Import `FloatLib.Floats.Interval` for enclosure proofs:

| Theorem | Informal statement |
| --- | --- |
| `Interval.roundDown_le` | Directed downward rounding never exceeds the exact real input. |
| `Interval.le_roundUp` | Directed upward rounding never falls below the exact real input. |
| `RInterval.mem_add`, `mem_sub`, `mem_mul` | Outward-rounded interval arithmetic contains the corresponding real operation. |
| `RInterval.mem_exp` | Endpoint evaluation of `Real.exp` with outward rounding is sound, by monotonicity. |
| `RInterval.mem_tanh` | Endpoint evaluation of `Real.tanh` with outward rounding is sound, by monotonicity. |
| `RInterval.mem_sqrt` | Square-root propagation is sound; the enclosure is informative when the input interval is nonnegative. |
| `RInterval.mem_log` | Logarithm propagation is sound when the input interval is strictly positive. |
| `RInterval.mem_div_of_nozero` | Four-corner division is sound when the denominator interval excludes zero. |
| `RInterval.mem_div` | Division is sound for every denominator interval; one containing zero yields the whole extended-real line. |

For IEEE overflow and division through zero, use the `EInterval` theorems, whose endpoints live
in `EReal` and can therefore represent unbounded enclosures.

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
`∞ + -∞`, `0 · ∞`, and `∞ / ∞` by returning the whole range. This ensures closure and conservative
fallbacks; the individual soundness theorems still require their stated input hypotheses.
For negation, ReLU, and absolute value, use `*_sound_extended` directly after an operation that
may overflow; there is no need to prove the intermediate endpoints finite. The original
`*_sound` theorems remain convenient specializations for finite intervals.

## Flocq-style generic format theory

Import `FloatLib.Floats.Formats.Flocq`. These theorems are stated over `ℝ` for a radix `β` and
exponent function `fexp`; they are the proof layer behind the interval rounders and the binary
error analyses rather than executable operations.

| Theorem | Informal statement |
| --- | --- |
| `Flocq.round_toNearest_point` | Every `ValidRndToNearest` rule selects a representable value at minimal distance from the input. |
| `Flocq.add_round_error_generic` | For any nearest rounding rule, the error of a rounded sum of two representable values is itself representable (this fails for directed rounding). |
| `Flocq.add_round_exact_error` | Error-free transformation form of the previous theorem: `x + y = round (x + y) + e` with `e` representable. |
| `Flocq.sqrt_round_residual_FLX` | For precision above one, the residual `x - q^2` of a nearest-rounded square root is representable. |
| `Flocq.roundAtScale_nearestEven_after_odd_binary_extra` | Round-to-odd with two extra binary digits followed by nearest-even rounding equals direct nearest-even rounding, on a fixed grid only. |
| `Flocq.refineLocation_correct` | The executable bracket refinement used by the effective calculation layer is sound. |

## P3109 representation, projection, and arithmetic

Import `FloatLib.Floats.Formats.P3109`. The descriptor supplies exact representation semantics
and the interim report's v4.0.3 round-then-saturate projection. Ordinary `convert`, `convertWith`, `cast`, and
destination-driven mixed operations use `Rat` as the exact domain of a P3109 destination, which has
one zero. `ofDyadic`, `project`, `ofRat`, and `projectRat` are the focused projection APIs.
`ExecFloat.P3109` evaluates addition, subtraction, multiplication, division, and fused
expressions exactly before one destination projection. Its source descriptors can differ.
Square root, reciprocal square root, and hypotenuse use integer comparisons with the exact real
root, so their implementation does not need an intermediate floating-point approximation.
The mixed interface also includes fused addition, scaled operations, and binary16, binary32,
and BFloat16 destinations. Extrema and query operations use the descriptor's finite classes and
exceptional values.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.P3109.decode_zero` | The named zero constructor denotes the unique finite zero. |
| `ExecFloat.P3109.decode_nan` | The named NaN constructor denotes P3109's sole NaN. |
| `ExecFloat.P3109.decode_positiveInfinity` | The named positive infinity has that meaning for every extended descriptor. |
| `ExecFloat.P3109.decode_negativeInfinity` | The named negative infinity has that meaning for every signed extended descriptor. |
| `ExecFloat.P3109.exists_decode_finite_of_ofFiniteFields?_eq_some` | Every successful checked field construction denotes an ordinary finite dyadic value. |
| `ExecFloat.P3109.toNatBits_ofNatBits` | Low-level natural-word construction keeps exactly the low `K` bits. |
| `Formats.P3109.Format.decodePositiveFinite_strictMono` | Increasing a positive finite code strictly increases its exact rational value. |
| `Formats.P3109.Format.roundFiniteToPrecision_fitsPrecisionGrid` | Every rounding mode lands on the descriptor's finite precision grid. |
| `Formats.P3109.Format.roundFiniteToPrecision_report_spec` | The shift-based dyadic kernel follows the report's precision-rounding formula in every mode and for every supplied stochastic word. |
| `Formats.P3109.Format.roundFiniteToPrecision_toRat_eq_int_mul` | Every rounding mode returns an integer multiple of the selected quantum `2^Q`. |
| `Formats.P3109.Format.roundFiniteToPrecision_towardZero` | `towardZero` truncates: the result has no larger magnitude and lies within one quantum; `_maximal` gives the grid maximality. |
| `Formats.P3109.Format.roundFiniteToPrecision_towardPositive` | `towardPositive` is the least grid point at or above the input (with `_minimal`). |
| `Formats.P3109.Format.roundFiniteToPrecision_towardNegative` | `towardNegative` is the greatest grid point at or below the input (with `_maximal`). |
| `Formats.P3109.Format.roundFiniteToPrecision_nearestTiesToAway_abs_sub_le` | `nearestTiesToAway` is within half a quantum; `_tie` shows exact ties go to the larger magnitude. |
| `Formats.P3109.Format.roundFiniteToPrecision_nearestTiesToEven_abs_sub_le` | `nearestTiesToEven` is within half a quantum; `_tie` shows exact ties select the candidate whose P3109 code is even, and `_tie_even` gives even significands for `P > 1`. |
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
| `ExecFloat.P3109.decode_binaryTo` | A binary operation decodes to the destination projection of its exact source values. |
| `ExecFloat.P3109.decode_ternaryTo` | A fused ternary operation has one destination projection after its exact evaluation. |
| `ExecFloat.P3109.decode_fmaTo_finite` | Finite fused multiply-add projects the exact rational product plus addend. |
| `Formats.P3109.Arithmetic.roundSqrtRatToPrecision_eq_real` | Integer square-root comparisons select the same precision-grid value as the real square-root rounding rule. |
| `Formats.P3109.Arithmetic.sqrtRoundAway_stochasticA`, `sqrtRoundAway_stochasticB`, `sqrtRoundAway_stochasticC` | Each stochastic square-root threshold agrees with the report's floor or nearest-integer formula on the exact root fraction, for every supplied word. |
| `ExecFloat.P3109.decode_sqrtTo` | Executable square root decodes to the declared real-root projection, including exceptional inputs. |
| `ExecFloat.P3109.decode_rsqrtTo` | Reciprocal square root follows the same real-root projection after exact rational inversion. |
| `ExecFloat.P3109.decode_hypotTo` | Hypotenuse rounds the root of the exact sum of squares once. |
| `Formats.P3109.Arithmetic.Mixed.faa_eq_project_finite` | Fused addition projects the exact three-term sum once. |
| `Formats.P3109.Arithmetic.Mixed.scaledAdd_eq_project_finite`, `scaledMul_eq_project_finite` | Scaling and arithmetic are exact before destination projection. |
| `Formats.P3109.Arithmetic.External.project_refines` | External encoding preserves the projected finite datum and the specified infinity/NaN encodings. |
| `Formats.P3109.Format.no_decodePositiveFinite_between` | No positive finite datum lies between consecutive positive codes. |
| `ExecFloat.P3109.isNormal_or_isSubnormal` | Every finite nonzero value belongs to one of the two finite classes. |
| `ExecFloat.P3109.nextGreaterThan_of_isNaN`, `nextLessThan_of_isNaN` | Both neighbor operations propagate NaN. |

The dyadic direction theorems cover the deterministic modes. Rational and external precision
rounding have all-mode formula proofs, with direction and error bounds before saturation.
The dyadic shift and square-root threshold implementations also have formula bridges for every
supplied stochastic word. These are deterministic statements about that word as an input.

The raw-word constructor lets us read file formats, implement wire protocols, and compare
conformance tables. Literals, conversions, and named constructors give ordinary programs
a more direct way to express numerical values.

## Real and executable affine quantization

`FloatLib.Numerics.Quantization.Affine.Real` provides `RealAffineQuantizer` and embeds the
executable rational `AffineQuantizer` into it with `AffineQuantizer.toReal`. The real API accepts
an integer rounding function explicitly. Monotonicity, integer identity, and a local error bound
are separate hypotheses, needed only by the corresponding theorem.

| Theorem | Informal statement |
| --- | --- |
| `RealAffineQuantizer.quantize_monotone` | A monotone rounder gives monotone quantization, including saturation. |
| `RealAffineQuantizer.quantize_dequantize` | Integer-preserving rounding returns every in-range reconstructed code. |
| `RealAffineQuantizer.dequantize_rawCode_error_le` | The grid scale multiplies the integer-rounding error. |
| `RealAffineQuantizer.dequantize_quantize_error_le_half` | Nearest rounding reconstructs within half a grid step when clipping is inactive. |
| `AffineQuantizer.toReal_quantize` | Agreement of rational and real integer rounding lifts to the complete saturated operation. |
| `Flocq.nearestEven_ratCast` | Real and executable rational nearest-even rounding choose the same integer, including ties. |
| `Flocq.affine_toReal_quantize` | The executable rational quantizer agrees with its real nearest-even specification. |
| `Flocq.affine_toReal_roundedValue` | Reconstruction also commutes with the rational-to-real embedding. |

The nearest-even connection is in `FloatLib.Floats.Formats.Flocq.Theory.Rounding.Affine`.
Clients needing only executable rational quantization can still import `Numerics.Quantization.Affine`.

## Theorem names and lookup

We use a few recurring names across the format families:

- `*_eq_spec` rewrites executable code to its reference definition;
- `*_refines`, `implements_*`, `spec_*`, and `preparedSpec_*` prove a relational capability;
- `toReal_*` and `toRat_*` state decoded mathematical behavior;
- `isFinite_*` establishes the side condition needed by a finite real theorem;
- `*_abs_error`, `*_relative_error`, and `*_mem_Icc` provide error or enclosure bounds;
- `*_eq_none_iff` characterizes exceptional values in optional exact views.

`#float_info YourType` lists the theorem families available for a configured type. Within a
proof, Lean's `exact?`, `apply?`, and `rw?` can help us find a declaration that matches the goal.
