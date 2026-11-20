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
import `FloatLib.Numerics.Executable.Conversion.Proof`.

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
binary's `specWith_iff_eq_runWith`) show that the numerical clauses determine exactly one complete
executable outcome.

To rewrite a particular binary conversion, `ExecFloat.Binary.Conversion.run_default_finite` reduces
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
`FloatLib.Numerics.Quantization.Deterministic.Rational`, so they don't keep tie rules of their own.

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
but its odd significand has about `8.9 * 10^11` bits, which is more than a hundred gigabytes just
to write down. Capped exponentiation decides equality with a boundary at a cost polynomial in the
bit lengths of the base, the exponent and the boundary, and not in the exponent's magnitude. Logarithm enclosures of increasing degree separate every other boundary, and the search
ends because the logarithm difference is then nonzero.

## Packed rows for kernel certificates

Import `FloatLib.Numerics.Packed.Sos`, and `FloatLib.Tactic.PackedRow` for `packed_row`.
A biased row `u` keeps `n` integers in lanes of `w` bits of one natural number, and the kernel
programs check it with a few big-number operations. Each theorem says what a passing check means
for the integer list the row stands for.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.Packed.eval_entries` | A biased row below `2 ^ (w * n)` stands for the value of its signed entries in base `2 ^ w`. |
| `Numerics.Packed.entries_ofInt_eval`, `Numerics.Packed.entry_ofInt_eval` | A list whose entries fit comes back out of the biased row of its value, padded with zeros. |
| `Numerics.Packed.guard_sound` | One range check bounds every signed entry by `2 ^ g` and rules out lanes beyond the row. |
| `Numerics.Packed.eval_conv` | Kronecker substitution: the value of the Cauchy product is the product of the values. |
| `Numerics.Packed.entries_mul`, `Numerics.Packed.entries_autocorr` | Two range checks and `n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ (w - 1)` make the product row hold the Cauchy product; the same for a row times its reverse. |
| `Numerics.Packed.absSum_eval`, `Numerics.Packed.sum_eval`, `Numerics.Packed.posSum_eval` | Masked remainders modulo `2 ^ w - 1` compute the `l1` norm, the sum and the positive part of a row whose `l1` norm is below `2 ^ (w - 1)`. |
| `Numerics.Packed.absSum_toInt`, `Numerics.Packed.sum_toInt` | The same on a guarded row with entries in `[-2 ^ g, 2 ^ g)`, when `n * 2 ^ g < 2 ^ (w - 1)`. |
| `Numerics.Packed.entries_rev`, `Numerics.Packed.lanes_rev`, `Numerics.Packed.pack_eq_ofInt` | Reversal reverses the entries and the lanes, and packing a list gives the biased row of its value. |
| `Numerics.Packed.eval_lanes`, `Numerics.Packed.lanes_lt_of_guard`, `Numerics.Packed.laneSum_eq` | Rows of natural numbers: a row is the value of its lanes, the unsigned range check bounds every lane by `2 ^ g`, and one remainder computes the lane sum. |
| `Numerics.Packed.lanes_mul`, `Numerics.Packed.lanes_pack` | Two unsigned range checks and `n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ w` make `u * v` hold the Cauchy product of the lanes; unsigned packing keeps the entries. |
| `Numerics.Packed.dot_eq`, `Numerics.Packed.lanes_packRev`, `Numerics.Packed.lanes_packFwd`, `Numerics.Packed.conv_getD` | A dot product by one multiplication: for lists of `n > 0` and `m ≥ n` naturals below `2 ^ w`, one packed with its first member in the highest lane and one with its first member in lane zero, the lane `n - 1` of the product is `∑ i < n, xs[i] * ws[i]`, when the two rows pass the unsigned range checks with `n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ w`. The lanes of the two rows are the reversed list and the list, and entry `m` of a Cauchy product is `∑ i ≤ m, X[i] * Y[m - i]`. |
| `Numerics.Packed.restrict_eq`, `Numerics.Packed.signs_eq` | One shift and one mask read a window of lanes; `signs` multiplies lane `k` of a two-sided row by the sign of `k - (n - 1)`. |
| `Numerics.Packed.eval_shiftDown_add_low`, `Numerics.Packed.laneSum_low`, `Numerics.Packed.shiftDown_eval` | Rounding every entry down to a multiple of `2 ^ s` in place: the row is `2 ^ s` times the rounding plus the remainders, and one remainder reads their sum, the `l1` error. |
| `Numerics.Packed.entries_ofInt_unfold`, `Numerics.Packed.signRow_mirror`, `Numerics.Packed.signRow_mirror_odd` | A guarded half row unfolds to its cosine or sine row; on these rows the signs are a relabelling. |
| `Numerics.Packed.entries_ramp` | The derivative weights: entry `k` times `k`, read back under `n * 2 ^ g ≤ 2 ^ (w - 1)`. |
| `Numerics.Packed.sosCheck_sound` | A passing sum-of-squares check gives `l1 e₁ + l1 e₂ ≤ 2 e₁[n - 1]` for the rows `e₁ - i e₂` of `kT (T - i S) + kc - kH |P + i Q|²`, with the constant `kc` in entry `n - 1`. |
| `Numerics.Packed.sqRe_eq`, `Numerics.Packed.sqIm_eq`, `Numerics.Packed.l1_normSq_le` | Four Kronecker products and two reversals give the two rows of `|P + i Q|²` centred at `n - 1`, and their `l1` norms are at most `((|P| + |Q|) 2 ^ g)²`. |
| `Numerics.Packed.horner_eq`, `Numerics.Packed.entries_ofInt_horner` | Horner's rule on a packed row is the value of the composed row `∑ cₖ bᵏ a ^ (n - 1 - k)`, which reads back under `n 2 ^ g K ^ (n - 1) < 2 ^ (w - 1)` for rows `a` and `b` of any length. |
| `Numerics.Packed.linked_sound` | A passing `linked w d u k xs` says that lane `k + i` of `u` holds `xs[i] * d`, as `num * d = entry * den`. |
| `Numerics.Packed.length_eq_of_matMulCheck`, `Numerics.Packed.entries_matMul` | A matrix product by one multiplication per column: when `matMulCheck w gA gB n p cols rows prod` passes, `A` has as many columns as `B` has rows, and the row `prod` of `n * p` lanes holds `A * B` listed column by column, with entry `i + n * j` equal to `∑ k, A[i][k] * B[k][j]` (the zero row when there is no column); the check also bounds the input entries. An input with unequal inner dimensions is rejected. |
| `Numerics.Packed.F2.isInverse_sound`, `Numerics.Packed.F2.isInverse_square`, `Numerics.Packed.F2.lane_mul`, `Numerics.Packed.F2.fits_iff`, `Numerics.Packed.F2.square_iff` | Matrices over the field of two elements with one row per bit mask: a passing `isInverse w n B M` says that `M` has exactly `n` rows, each below `2 ^ n`, that `n ≤ w`, and that every row `i < n` of `B`, multiplied by the matrix with rows `M`, is the unit row `2 ^ i`. All rows are multiplied at once on lanes of `w` bits; bits of a lane of `B` from position `n` on are not read. The statement is about the library's `rowMul`; it is not transferred to Mathlib's `Matrix` over `ZMod 2`. |
| `Numerics.Packed.lanesLe_sound` | Many comparisons by one subtraction: a passing `lanesLe w n u v` gives `lane w k u ≤ lane w k v` for every `k < n`, for rows whose lanes leave their top bit clear. |

## Exact arithmetic in the kernel

Import `FloatLib.Numerics.Kernel.FracProof`, `BallProof`, `QProof`, `ModProof`, `RootProof`,
`CBall/Exponential`, `CFixProof`, `MultiplicativeProof`, `SeqProof` or `Bisection` for the theorems.
The definitions are in the modules of the same names without `Proof` (`Z`, `Signed`, `Frac`,
`Dyad`, `Ball`, `Q`, `Mod`, `Root`, `Bits`, `CBall`, `CFix`, `Multiplicative`, `Seq`, `Strict`),
which import no mathematics from Mathlib. Each function uses the natural-number operations that
Lean's kernel computes natively.
`FloatLib.Floats.ExecFloat.Backends.Kernel.Exact` and `Plumbing` register the existing equations
in reverse with `@[kernel_optimize ←]`, adding four bridge equations for arrays.
`kernel_twin` (`FloatLib.Tactic.KernelTwin`) applies these rules throughout a program's scoped
definition closure and proves every transformed definition equal to its source.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.Kernel.Z.add_eq`, `sub_eq`, `mul_eq`, `neg_eq`, `pow_eq`, `natAbs_eq`, `toNat_eq`, `min_eq`, `max_eq`, `shiftLeft_eq`, `shiftRight_eq`, `ediv_eq`, `emod_eq`, `fdiv_eq`, `tdivNat_eq` | The kernel functions on `Int` are core's operations: `Z.add x y = x + y` and so on, for all integers. |
| `Numerics.Kernel.Z.floorDiv_eq`, `ceilDiv_eq`, `ceilShift_eq`, `mod_eq`, `ble'_iff`, `blt'_iff`, `beq'_iff` | Division by a natural number rounded down and up, the remainder in `[0, d)`, and core's Boolean comparisons `Int.ble'`, `Int.blt'`, `Int.beq'` decide `≤`, `<` and `=`. |
| `Numerics.Kernel.Signed.toInt_add`, `toInt_sub`, `toInt_mul`, `toInt_neg`, `toInt_pow`, `le_iff`, `lt_iff`, `beq_iff`, `toInt_floorDiv`, `toInt_ceilDiv` | Integers as pairs `plus - minus` of naturals: every operation is the integer operation on `toInt`, with no condition on the pair. |
| `Numerics.Kernel.Frac.toRat_add`, `toRat_sub`, `toRat_mul`, `toRat_inv`, `toRat_div`, `toRat_pow`, `toRat_normalize`, `toRat_ofRat`, `toRat_ofScientific` | Unnormalized fractions `(plus - minus) / den` with a positive denominator in the type: every operation is the rational operation on `toRat`, and nothing computes a gcd except `normalize`. |
| `Numerics.Kernel.Frac.le_iff`, `lt_iff`, `beq_iff`, `le_cast`, `lt_cast`, `toInt_floor`, `toInt_ceil` | Comparison by cross-multiplication decides the order of the rationals, and of their casts into any ordered field; `floor` and `ceil` are `⌊x⌋` and `⌈x⌉`. |
| `Numerics.Kernel.Q.add_eq`, `sub_eq`, `mul_eq`, `neg_eq`, `inv_eq`, `div_eq`, `pow_eq`, `abs_eq`, `min_eq`, `max_eq`, `floor_eq`, `ceil_eq`, `mulPow2_eq`, `divPow2_eq`, `mk_eq`, `le_iff`, `lt_iff`, `beq_iff` | The kernel functions on core's `Rat` return the same normalized value as core's operations: `Q.add a b = a + b` and so on, and `Q.mk num den = mkRat num den`. |
| `Numerics.Kernel.Dyad.toRat_add`, `toRat_sub`, `toRat_mul`, `toRat_neg`, `toRat_mulPow2`, `toRat_divPow2`, `toRat_ofScaled`, `le_iff`, `lt_iff`, `beq_iff` | Dyadic numbers `(plus - minus) / 2 ^ scale`: sums align by shifts, and every operation is the rational operation on `toRat`. |
| `Numerics.Kernel.Dyad.dropDown_le`, `sub_dropDown_le`, `le_dropUp`, `dropUp_sub_le`, `roundDown_le`, `lt_roundDown_add`, `le_roundUp`, `roundUp_lt_add`, `trimDown_le`, `le_trimUp` | Rounding a dyadic number: removing `k` low bits moves it by at most `(2 ^ k - 1) / 2 ^ scale` in the stated direction, rounding to multiples of `2 ^ (-p)` by less than `2 ^ (-p)`, and cutting to a number of bits rounds in the stated direction. |
| `Numerics.Kernel.Ball.contains_add`, `contains_sub`, `contains_neg`, `contains_mul`, `contains_drop`, `contains_round`, `contains_trim`, `contains_ofFrac`, `contains_ofBounds`, `contains_iff` | Balls with a dyadic midpoint: the result of each operation contains the result of the operation on any members, in every ordered field, and rounding the midpoint keeps every member. |
| `Numerics.Kernel.Ball.contains_inv`, `contains_div`, `apart_iff` | For a ball that `apart` accepts, which holds exactly when zero is not a member, `inv x p` contains the reciprocal of every member and `div x y p` every quotient, with the two ends rounded outward to multiples of `2 ^ (-p)`. |
| `Numerics.Kernel.Ball.le_sound`, `lt_sound` | A passed comparison of two balls holds for all their members. |
| `Numerics.Kernel.powMod_eq`, `powModWindow_eq`, `invMod_spec`, `isInvMod_iff` | `powMod a e n = a ^ e % n` for every window and modulus; `a * invMod a n % n = 1 % n` for coprime `a` and `n`. |
| `Numerics.Kernel.isRoot_iff`, `isqrt_eq`, `Numerics.IntegerRoot.newton_eq_nthRoot` | `isRoot k r n` decides `r = Nat.nthRoot k n` for `k ≠ 0`; `isqrt n = Nat.sqrt n`; the checked Newton root is the floor root for every degree. |
| `Numerics.Kernel.size_eq`, `bitLength_eq`, `windowLength_eq`, `testBit_eq`, `lowBits_eq`, `ceilShift_eq`, `ceilDiv_eq`, `factorial_eq`, `log2_eq_size_sub_one` | Bits: `size n = Nat.size n` for every natural number, `bitLength B n` and `windowLength W k n 0` are the bit length under their bounds `n < 2 ^ B` and `n < 2 ^ (W * 2 ^ k)`, `testBit` is `Nat.testBit`, `Nat.log2 n = size n - 1`. |
| `Numerics.Kernel.popCount_eq`, `pairLevels_mod`, `digits_two_sum_le_size` | `popCount n` is the sum of the binary digits of `n`, for every natural number. It adds neighbouring lanes of 1, 2, 4, … bits and takes one remainder: for `n < 2 ^ (2 ^ k * K)` with fewer than `2 ^ 2 ^ k - 1` set bits, `k` levels and the remainder modulo `2 ^ 2 ^ k - 1` give the count. |
| `Numerics.Kernel.CBall.contains_add`, `contains_sub`, `contains_neg`, `contains_conj`, `contains_mul`, `contains_smul`, `contains_mulI`, `contains_round`, `contains_ofReal`, `contains_ofNat` and `mem_add`, …, `mem_mulIPow` | Complex balls, one ball for the real part and one for the imaginary part: the result of each operation (sum, difference, negation, conjugate, product, product with a real ball, product with `i` and with `i ^ k`, rounding to `2 ^ (-p)`) contains the result of the operation on any members, as pairs in every ordered field (`contains_…`) and as complex numbers (`mem_…`). |
| `Numerics.Kernel.CBall.mem_expI`, `mem_expISmall`, `mem_expIStep`, `contains_halfPi` | `expI x h j n p` contains `exp (i t)` for every real `t` in the ball `x`, when `h` contains `π / 2`, for all `j`, `n` and every precision `p`: quarter turns are removed with `h`, and the rest is the Taylor polynomial of degree below `n` with the bound of `Complex.exp_bound` when the rest is within `2 ^ (-j)` and `n ≥ 1`, the square `[-1, 1]²` otherwise. `expIStep` removes multiples of a step containing `s`, using a table whose entries must enclose `exp (i k s)`. `halfPi` contains `π / 2` to 66 binary digits. |
| `Numerics.Kernel.CFix.contains_mul`, `contains_conj`, `contains_one`, `contains_zero`, `contains_ofCBall`, `mem_mul`, `mem_pow2`, `Numerics.Kernel.CSum.contains_push`, `contains_add`, `contains_scale` | Complex enclosures stored as two naturals with the offset `2 * 2 ^ s`, one radius and a flag: a product is four products of naturals with no sign and no case distinction, and it contains the product of any members; a value whose flag is false claims nothing. `CSum` adds values up without reducing them, and `CSum.scale s z S` contains the product of a member of `z` with the sum that `S` contains. |
| `Numerics.Kernel.Split.total_contains_Icc`, `Split.cover_Icc`, `Cover.total_contains`, `Cover.find_spec` | For `fr`, `fi` on the naturals that multiply like the parts of a complex number and are `(1, 0)` at one, and values `zp p` that contain `(fr p, fi p)`: the total over a split that passes `Split.splitOk plan rough c₁ ν` contains `∑ n ∈ [1, ν], fr n` and `∑ n ∈ [1, ν], fi n`. A `Cover` carries the proof of the check, and `cover% ν y` writes one out for any bound. Nothing is assumed about primes. |
| `Numerics.Kernel.bisect_spec`, `bisect_eq`, `bisect_succ` | `bisect below bits lo` returns the largest number from `lo` to `lo + 2 ^ bits - 1` at which a downward-closed predicate that holds at `lo` holds, in `bits` steps; it is the reference bisection `Numerics.bisect` on that interval. |
| `Numerics.Kernel.strict_eq` | `strict n f = f n`: the application with the argument reduced to a literal first, so that the kernel reduces `f` once for each number. |
| `Numerics.Kernel.Seq.len_eq`, `Seq.nth?_eq`, `Seq.getD_eq`, `Seq.snoc_eq`, `Seq.tabulate_eq`, `Seq.map_eq`, `Seq.mapIdx_eq`, `Seq.zipWith_eq`, `Seq.all_eq`, `Seq.reverse_eq`, `Seq.sum_eq`, `Opt.bind_eq`, `Opt.map_eq`, `Opt.join_eq` | The list and option functions by recursors are core's: `Seq.len l = l.length`, `Seq.nth? l i = l[i]?`, `Seq.getD l i d = l.getD i d`, `Seq.snoc l x = l ++ [x]`, `Seq.tabulate n f = List.ofFn f`, `Seq.map f l = l.map f`, `Seq.mapIdx f l = l.mapIdx f`, `Seq.zipWith f la lb = List.zipWith f la lb`, `Seq.all p l = l.all p`, `Seq.reverse l = l.reverse`, `Seq.sum l = l.sum` for naturals, and `Opt.bind`, `Opt.map`, `Opt.join` are `Option.bind`, `Option.map`, `Option.join`. `Backends.Kernel.Plumbing` tags the rules for `List.length`, `Array.size`, `l[i]?`, `a[i]?`, `List.getD`, `Array.push`, `Array.ofFn`, `List.map`, `List.mapIdx`, `List.zipWith`, `List.all`, `List.reverse`, `List.sum` on naturals, the three option functions and `Nat.sqrt`. |
| `Numerics.Kernel.Seq.all₃_iff` | `Seq.all₃ p la lb lc = true` exactly when the three lists have the same length and `p` holds for the entries at every position. |
| `N.f.twin_eq` (generated by `kernel_twin f within M…`) | For every definition `g` that `f` depends on in the given modules and whose body the tagged rules change: `g = N.g`, where `N.g` has the rewritten body. One theorem per definition, proved by the rules that fired. |
| `Numerics.Interval.BinaryGrid.mul_def`, `add_def`, `div?_def`, `pow_def`, `Numerics.Enclosure.expTaylor_def`, `sinTaylor_def`, `expRadius_def`, `exp_def`, `log_def`, `atan_def`, `logScale_def`, `Numerics.Interval.sqrtPointBounds_def`, `tanBounds?_def`, `tanhBounds_def`, `Internal.reducedTrigBounds_def`, `Expr.eval?_binary`, `Expr.checkBox_def`, `Expr.check_def`, `Box.bisect?_def` and their siblings named `…_def` | FloatLib's fixed-point intervals and elementary enclosures are defined with the kernel functions; each `…_def` states the definition in ordinary notation (the sum of the series, the `if`, the operators, and for the expression evaluator its equations by pattern matching), so every earlier theorem about them still holds as stated. |

## Coefficient bounds on the circle and on intervals

Import `FloatLib.Numerics.Coeff.Trig`. An integer row with centre lane `c` stands for the Laurent
polynomial `∑ k, xs[k] z ^ (k - c)`, `Numerics.Coeff.laurent`, whose polynomial part is Mathlib's
`Polynomial.ofCoeffList xs`, and on `z = exp (u i)` for a trigonometric polynomial.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.Coeff.ofCoeffList_conv`, `Numerics.Coeff.laurent_conv`, `Numerics.Coeff.laurent_entries_mul` | The polynomial or the Laurent polynomial of a Cauchy product, or of a guarded Kronecker product, is the product. |
| `Numerics.Coeff.norm_laurent_le`, `Numerics.Coeff.norm_laurent_le_absSum` | On the unit circle a row is bounded by its `l1` norm, which one `absSum` computes. |
| `Numerics.Coeff.laurent_reverse`, `Numerics.Coeff.conj_laurent`, `Numerics.Coeff.laurent_autocorr` | Reversal substitutes `z⁻¹`, which is conjugation on the circle, so `h ⋆ reverse h` is `|h|²`. |
| `Numerics.Coeff.laurent_normSq` | The two rows of `Packed.normSq n P Q`, read as `t - i s`, are `|P + i Q|²` on the circle. |
| `Numerics.Coeff.re_laurent_nonneg`, `Numerics.Coeff.laurent_sosCheck` | A centre entry that dominates all other entries of a pair of rows gives a nonnegative real part; a passing `sosCheck` gives `kH |p + i q|² ≤ kT Re (t - i s) + kc`. |
| `Numerics.Coeff.trig_sosCheck`, `Numerics.Coeff.power_sosCheck`, `Numerics.Coeff.normSq_sosCheck` | One check bounds from one side a trigonometric polynomial with cosine and sine terms, a polynomial at `x = (M + R cos u) / D` through Horner's rule, or the norm square of a Gaussian-integer polynomial on the circle. |
| `Numerics.Coeff.laurent_compose` | The row of Horner's rule is the composed polynomial on the circle. |
| `Numerics.Coeff.laurent_exp`, `Numerics.Coeff.re_laurent_exp`, `Numerics.Coeff.im_laurent_exp` | At `z = exp (u i)` a row is a trigonometric sum, whose real and imaginary parts are the cosine and sine sums of its lanes. |
| `Numerics.Coeff.laurent_mirror`, `Numerics.Coeff.laurent_mirror_odd`, `Numerics.Coeff.abs_cos_sum_le`, `Numerics.Coeff.abs_sin_sum_le` | Mirrored rows are twice the cosine polynomial and `2 i` times the sine polynomial, each bounded by the `l1` norm of its half row. |
| `Numerics.Coeff.hasDerivAt_cos_sum`, `Numerics.Coeff.hasDerivAt_sin_sum`, `Numerics.Coeff.hasDerivAt_cos_ramp` | Derivatives of cosine and sine polynomials, with the derivative row of a packed row computed by `ramp`. |
| `Numerics.Coeff.hilbert_mirror`, `Numerics.Coeff.hilbert_mirror_odd` | The Hilbert transform, the multiplier `-i sgn m`, takes `cos (k u)` to `sin (k u)` and `sin (k u)` to `-cos (k u)`. |
| `Numerics.Coeff.chebyshev_cos`, `Numerics.Coeff.forall_Icc_chebyshev`, `Numerics.Coeff.forall_Icc_of_cos` | A Chebyshev series at `cos u` is a cosine polynomial, so a bound for all `u` holds for the Chebyshev series on `[-1, 1]`, and in `(lo + hi) / 2 + (hi - lo) / 2 * cos u` on any interval `[lo, hi]`. |

## Bounds on series with rational coefficients

Import `FloatLib.Tactic.Interval` for `interval`, whose coefficient route applies
these theorems to a bound over a whole domain. `Numerics.Coeff.series f xs` is
`∑ k < xs.length, xs[k] * f k`, and `Numerics.Coeff.rowCheck w g n d A xs` checks in the kernel that
the packed row `A` holds the rationals `xs` at the common denominator `d`.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.Coeff.series_add`, `Numerics.Coeff.series_smul`, `Numerics.Coeff.series_single`, `Numerics.Coeff.sum_eq_series` | `series` is linear in the list, a single coefficient is a monomial, and a block `∑ k ∈ range n, a k * f k` is the `series` of its coefficients. |
| `Numerics.Coeff.trig_sos` | One check gives `0 ≤ kT (2 d (∑ aₖ cos (k u) + ∑ bₖ sin (k u))) + kc` at every `u`. |
| `Numerics.Coeff.norm_sos` | One check gives `0 ≤ kT (d² ‖∑ aₖ zᵏ + i ∑ bₖ zᵏ‖²) + kc` at every `z` with `‖z‖ = 1`. |
| `Numerics.Coeff.power_sos` | One check on the row of Horner's rule gives `0 ≤ kT (d (2 D) ^ (n - 1) ∑ aₖ xᵏ) + kc` at every `x` of `[lo, hi]`. |
| `Numerics.Coeff.bound_le_of_sos`, `Numerics.Coeff.bound_lt_of_sos`, `Numerics.Coeff.le_bound_of_sos`, `Numerics.Coeff.lt_bound_of_sos` | `0 ≤ kT (K F) + kc` with `kT K b + kc ≤ 0` (or `< 0`) gives `b ≤ F` or `b < F` for `kT > 0`, and `F ≤ b` or `F < b` for `kT < 0`. |

## Constraint sets on rational boxes

Import `FloatLib.Tactic.Interval.Constraints` for the route of `interval` that proves
that a set of real constraints has no point, or `FloatLib.Numerics.Enclosure.Expression.ConstraintProof`
for the theorems alone. A `Numerics.Interval.Constraint` combines by `and` and `or` the atoms
`fails relation e` (`0 ≤ e` or `0 < e` for an interval expression `e`) and `form strict f` (a
quadratic form is nonpositive, or negative); `Constraint.Holds c values functions` is its real
meaning. A `Refutation` is a tree of cuts of a box whose leaves name the part of the constraint that
fails there, and `Constraint.refutes B r c box` checks one. All statements hold for every sound
backend, every constraint and every dimension.

`FloatLib.Numerics.Enclosure.Expression.RangeProof` has the intervals whose ends may be infinite. A
`Numerics.Interval.Range` is one, `Expr.range` evaluates an expression on a box of them, and
`Constraint.failsOn` says whether a constraint has no point there. So a variable with a bound on one
side only, or with none, still gives its expression a range.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.Interval.Constraint.refutes_sound` | If `c.refutes B r box = true` for a backend with `B.Sound functions`, then `c` holds at no real assignment of the box: `box.ContainsReal values → ¬ c.Holds values functions`. |
| `Numerics.Interval.Box.containsReal_cut`, `Box.containsReal_halve` | Every real assignment of a box belongs to one of the two parts of a cut at any point of a coordinate, and of the cut at its midpoint. |
| `Numerics.Interval.Constraint.holds_conjunct` | A constraint that holds has every conjunct on a path through its conjunctions. |
| `Numerics.Interval.Form.definite_sound` | An interval matrix that `Form.definite` accepts contains only symmetric matrices whose form is nonnegative at every vector, and with the strict check only matrices whose form vanishes at the zero vector alone. |
| `Numerics.Interval.Form.quad_reduceReal`, `Form.quad_of_reduceReal` | The form of a Schur complement is the form of the remaining rows minus the square of the border's sum over the pivot, so with a positive pivot `a` a form is `a * (d + L / a) ^ 2` plus the form of the complement. |
| `Numerics.Interval.Form.reduce_sound` | The interval Schur complement, computed with the operations of the backend, encloses the real one. |
| `Numerics.Interval.Form.nonneg_of_definiteOn` | A form that `Form.definiteOn` accepts on a box is nonnegative at every real assignment of the box. |
| `Numerics.Interval.Form.vanishes_of_definiteOn` | With the strict check, the form is nonpositive at a real assignment of the box only where every coordinate vanishes, which is nowhere when the constant one is a coordinate. |
| `Numerics.Interval.Constraint.not_holds_of_excluded` | A nonpositive form with an accepted matrix and a coordinate that cannot vanish on the box holds at no real assignment of the box. |
| `Numerics.Interval.Constraint.abs_lt_of_form`, `Constraint.abs_le_of_form` | If `a ≤ b` and the form of `a - b + λ * (e ^ 2 - x ^ 2)` is positive definite with a coordinate that cannot vanish (or positive semidefinite) on a box, then `-e < x ∧ x < e` (or `-e ≤ x ∧ x ≤ e`): the bound of a variable on a sublevel set. |
| `Numerics.Interval.Expr.contains_range` | The range of an expression contains its value at every real assignment in the ranges of the variables, for a sound backend with rational endpoints that decodes each endpoint to itself and a table of function names that `Range.NamesSound` accepts. |
| `Numerics.Interval.Constraint.not_holds_of_failsOn` | A constraint that `Constraint.failsOn` rejects on a box of ranges holds at no real assignment of the box. |
| `Numerics.Interval.le_of_deriv_nonneg`, `lt_of_deriv_pos`, `le_of_deriv_nonpos`, `lt_of_deriv_neg` | A function whose derivative is nonnegative between `l` and `x` is at `x` at least what it is at `l`, and more when the derivative is positive. With a nonpositive derivative between `x` and `u` it is at `x` at least what it is at `u`. This is the step of `interval` for two sides that meet at an end of the range. |
| `Numerics.Interval.exists_eq_sub_cube` | An odd function `f` with `u - u ^ 3 / d ≤ f u ≤ u` for `0 ≤ u`, where `0 < d`, satisfies `f u = u - u ^ 3 * r` with `0 ≤ r ≤ 1 / d`, for every real `u`. |
| `Numerics.Interval.exists_sin_eq_sub`, `exists_tanh_eq_sub`, `exists_arctan_eq_sub`, `exists_cos_eq_sub` | `sin u = u - u ^ 3 * r` with `0 ≤ r ≤ 1 / 6`, the same for `tanh u` and `arctan u` with `0 ≤ r ≤ 1 / 3`, and `cos u = 1 - u ^ 2 * c` with `0 ≤ c ≤ 1 / 2`, for every real `u`. |
| `Numerics.Interval.hasDerivAt_tanh`, `tanh_le_self`, `sub_cube_le_tanh`, `sub_cube_le_arctan` | The derivative of `Real.tanh` at `x` is `1 - Real.tanh x ^ 2`; for `0 ≤ u`, `Real.tanh u ≤ u`, `u - u ^ 3 / 3 ≤ Real.tanh u` and `u - u ^ 3 / 3 ≤ Real.arctan u`. |

## The Wiener algebra and a posteriori defects

Import `FloatLib.Numerics.Coeff.Defect`. `Numerics.Coeff.Wiener` is `ℓ¹(ℤ)` with convolution, a
complete normed commutative `ℂ`-algebra with `‖1‖ = 1`; `Wiener.eval u` evaluates an element at
the point `u` of the circle, and `Wiener.ofRow xs c` is the element of an integer row.

| Theorem | Informal statement |
| --- | --- |
| `Numerics.Coeff.Wiener.norm_eval_le`, `Numerics.Coeff.Wiener.continuous_eval_apply` | On the circle an element is bounded by its norm, and it is a continuous function. |
| `Numerics.Coeff.Wiener.eval_ofRow`, `Numerics.Coeff.Wiener.ofRow_conv`, `Numerics.Coeff.Wiener.norm_ofRow_le` | A row is its Laurent polynomial on the circle, Cauchy products of rows are products, and the norm of a row is at most its `l1` norm. |
| `Numerics.Coeff.inv_of_defect` | In a complete normed commutative ring with `‖1‖ = 1`, `‖1 - v f‖ ≤ δ < 1` makes `f` a unit with `‖f⁻¹ - v‖ ≤ ‖v‖ δ / (1 - δ)`. |
| `Numerics.Coeff.invSqrtOneSub_sq_mul`, `Numerics.Coeff.norm_invSqrtOneSub_sub_one_le` | The binomial series `(1 - d) ^ (-1/2)` squares to `(1 - d)⁻¹`, and `‖(1 - d) ^ (-1/2) - 1‖ ≤ δ / (2 (1 - δ))` for `‖d‖ ≤ δ < 1`. |
| `Numerics.Coeff.invSqrt_of_defect` | `‖1 - x g²‖ ≤ δ < 1` gives `r` with `r² x = 1` and `‖r - g‖ ≤ ‖g‖ δ / (2 (1 - δ))`. |
| `Numerics.Coeff.Wiener.eval_invSqrt_of_defect` | If `x` and `g` are real on the circle and `g (0) > 0`, that `r` is `1 / √(x u)`, and `x` is positive. |
| `Numerics.Coeff.Wiener.norm_one_sub_ofRow_mul_le` | One Kronecker product and one `absSum` bound the defect `‖1 - u v / 2 ^ K‖` of two packed rows. |

## Packed rows of format values

Import `FloatLib.Floats.ExecFloat.Packed`. `ExecFloat.ExactLanes` gives the exact rational lanes of a
value of any format with an exact decoder, one for a scalar and one per element for a block, and
`packed_values` brings a list of them in as one row at a common denominator.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Packed.link_sound` | A passing `link w d vs u` says that every lane of `vs` is finite and is entry `k` of `u` divided by `d`. |

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
are the rational versions. In our policy regression suite we compare the rational rounder with
the general engine, and the rational tie test with `dyadicIsGridTie` at denominator one.
`Model.dyadicNearestAwayOverflows` and `Model.rationalNearestAwayOverflowsScaled` classify overflow
at the top finite midpoint, which overflows under nearest-away whatever the parity of the largest
finite significand. Tininess for nearest-away uses the nearest-even boundary `underflowMidpoint`,
because both nearest rules round that midpoint up to the smallest normal value.

### The nearest-away and away-from-zero directions

`IEEERoundingMode` has six constructors: the five rounding-direction attributes of IEEE 754-2019,
with `nearestAway` (roundTiesToAway) after `nearest`, and `away` (MPFR's `MPFR_RNDA`, which IEEE
doesn't define as an attribute) last. `Numerics.RoundingMode` has `away` as well, and `Policy.ieeeRoundingMode?` maps
`nearestAway` and `away`, so `Policy.roundDyadic` and the conversion status `finiteStatus` treat
them as directions. Every operation that takes a rounding direction accepts them: arithmetic,
square root, casts, reductions, integral rounding, integer conversion, and text input and output.
Nearest-away square root uses the nearest-even square root, because the square root of a value of
a format is never a tie of its grid, as `Model.Internal.Directed.sqrt` explains. We haven't stated
that fact as a theorem.

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
| `Model.toReal_rSqrt_eq_roundAt` | For a finite input and a finite result, reciprocal square root rounds the exact real reciprocal root once; a finite result already rules out zero and negative inputs. |
| `Model.toReal_hypot_eq_roundAt`, `Model.isFinite_of_isFinite_hypot` | Hypotenuse rounds the root of the exact sum of squares, with no intermediate product rounding; a finite result forces finite operands. |
| `Model.toReal_pown_eq_roundAt` | A finite base raised to an integer exponent is rounded once, including negative exponents and a zero base. |
| `Model.toReal_rootn_eq_roundAt` | A finite input with a finite root gives the rounded signed real root; the finite result rules out degree zero and even roots of negative values. |
| `ExecFloat.Binary.toModel_rootn`, `toModel_pown`, `toModel_hypot`, `toModel_rSqrt` | Every storage codec preserves the complete model result, including exceptional encodings. |

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
| `cast_policy` | For finite input and output, any descriptor's nearest-even cast is its real grid rounding, followed by clipping to the finite interval only when its encoding is fully finite. Widths and exponent biases are arbitrary. |
| `cast_eq_roundAt`, `isFinite_of_isFinite_cast` | A finite cast to an IEEE destination is one nearest-even rounding, from any source descriptor including FP8; a finite result forces a finite source. |
| `cast_exact_of_gridExtension_policy` | A finite-input, finite-output cast is exact when the destination contains the source's dyadic grid and, for a saturating destination, the input lies in its finite interval. |
| `cast_exact_of_gridExtension` | A finite cast is exact when the IEEE destination contains the source's dyadic grid, for any source encoding. |
| `cast_exact_of_compatibleWidening` | Increasing only fraction width while preserving exponent semantics and encoding is exact. |
| `cast_eq_widenExact_of_compatibleWidening` | Every rounding mode gives the same widened encoding for a finite value with compatible exponent fields and encoding. |
| `isFinite_quietNaN`, `isFinite_canonicalNaN` | Quieting does not change finiteness, and the canonical NaN of an IEEE encoding is not finite. |
| `cast_of_isNaN`, `propagatedNaN_eq_quietNaN` | An IEEE destination quiets the NaN, keeps its sign, and keeps its payload when it fits, otherwise using payload zero (IEEE 754-2019 §6.2.3). Other encodings follow their own NaN rule; a cast to its own format is `quietNaN`. |
| `toReal_widenExact` | The direct widening constructor preserves the decoded real value, including zeros and subnormals. |

`cast_exact_of_gridExtension_policy` proves grid-extension exactness once for every encoding;
`cast_exact_of_gridExtension` is its IEEE corollary. It covers standard widenings such as binary32
to binary64 and permits a larger exponent range, so the exponent widths need not be equal.
`Model.toReal_roundDyadic_policy` supplies the shared executable packing argument;
`Model.toReal_roundDyadic_eq_roundAt` is its IEEE corollary.

Import `FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedPrecision` for exact products
and power-of-two scaling. The product and scaling families are descriptor-parametric; the
executable conclusions below use an IEEE arithmetic destination.

| Theorem | Informal statement |
| --- | --- |
| `genericFormat_mul_of_precision` | Two grid values have an exact product on the destination grid if their precisions sum to at most its precision and its subnormal floor is at most the sum of their canonical exponents. |
| `genericFormat_mul_of_normal` | The same precision condition suffices when the product is zero or in the destination's normal range. |
| `toReal_mul_cast_exact` | Exact widenings followed by a finite product introduce no product error under the precision, lower-grid and zero-or-normal product premises. A finite product forces finite widened operands. The two source descriptors can differ and need not be IEEE. |
| `ExecFloat.Binary.toReal_mul_cast_exact` | The exact-product theorem transports through arbitrary configured storage plans, codecs and a multiplication capability that satisfies its specification. |
| `genericFormat_mul_bpow` | A power-of-two shift preserves the grid if the shift is nonnegative, the input is zero, or the result is normal. |
| `isFinite_of_isFinite_scale`, `toReal_scale_eq_roundAt`, `toReal_scale_exact` | A finite `Model.scale x e` has a finite operand, in every encoding and direction. For an IEEE descriptor a finite result rounds the exact real product by `2^e` once, and the grid-preserving range condition makes it exact. |
| `toReal_mul_pow_two_exact` | Multiplication by a stored operand whose real value is `2^e` is exact under the same range condition when the product is finite. |

Precision alone does not ensure exact products: the square of the smallest bfloat16 subnormal
rounds to zero in binary32. Finiteness alone does not exclude saturation: casting binary32 1000
to E2M1 gives the finite value 6. The general cast bound retains this clipping loss.

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
arithmetic operation to that grid, you also need its operation-specific refinement hypotheses.

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

### Half-ulps and the rounded difference of two rounded reals

Import `FloatLib.Floats.Formats.BinaryInterchange.Analysis.HalfUlp` and
`FloatLib.Floats.Formats.BinaryInterchange.Analysis.RoundedDifference`. Every theorem holds for
every `FloatFormat` and nearest-even rounding onto its grid with gradual underflow, for all real
arguments. `h x = halfUlpAt fmt x`, `u = unitRoundoffAt fmt` and `η = underflowErrorAt fmt`.

| Theorem | Informal statement |
| --- | --- |
| `Model.halfUlpAt_le`, `halfUlpAt_le_of_minNormalAt_le`, `halfUlpAt_eq_of_abs_lt_minNormalAt` | `h x ≤ u |x| + η`: `u |x|` alone in the normal range, and exactly `η` below it. |
| `Model.halfUlpAt_mono`, `two_mul_halfUlpAt_le_of_lt`, `exists_ulpAt_eq_bpow` | `h` is monotone in `|x|`. An ulp is a power of two at or above the subnormal spacing, so a smaller half-ulp is at most half a larger one. |
| `Model.halfUlpAt_le_halfUlpAt_roundAt` | Rounding does not decrease the half-ulp: `h x ≤ h (round x)`. |
| `Model.genericFormat_sub_of_halfUlpAt_le`, `roundAt_sub_eq_of_halfUlpAt_le` | A difference of two grid points whose half-ulp is at most that of each operand is a grid point, so rounding it is exact. |
| `Model.abs_roundAt_sub_le_abs_sub`, `exists_genericFormat_between` | The rounded value is at least as close to `x` as any grid point, and between two nonnegative reals with different half-ulps there is a grid point. |
| `Model.one_add_mul_abs_roundAt_sub_le`, `one_add_mul_abs_roundAt_sub_le_add` | The relative error of one rounding is at most `u / (1 + u)` in the normal range: `(1 + u) |round x - x| ≤ u |x|`, and `≤ u |x| + (1 + u) η` for every real. |
| `Model.abs_roundAt_add_sub_le_of_genericFormat`, `abs_roundAt_sub_sub_le_of_genericFormat` | A sum or difference of two grid points rounds with relative error `u` and no underflow term. |
| `Model.NoUnderflowAt`, `abs_roundAt_sub_le_of_noUnderflowAt`, `exists_roundAt_eq_mul`, `exists_roundAt_add_eq_mul` | A real that is zero or in the normal range, and a sum of two grid points, round to themselves times a factor in `[1 - u, 1 + u]`. |
| `Model.roundedSubError_le` | For all reals `p` and `q`, `round (round p - round q)` is within `(2u + u²)(|p| + |q|) + (2 + 2u) η` of `p - q`. |
| `Model.roundedSubError_le_of_mul_nonpos`, `abs_roundAt_add_sub_le_of_nonneg` | When `p` and `q` have opposite signs nothing cancels and the bound is `2u (|p| + |q|) + 4 η`, with no `u²` term. |
| `Model.roundedSubError_cases`, `roundedSubError_cases_of_le` | When `p` and `q` have the same sign, with `m` the larger and `n` the smaller magnitude, the error is at most `u (2m - n) + 2u² (m + n) + (2 + 4u) η`, or `7/4 (u m + η)`, or `u (m + n) + 2 η`, by the half-ulps of `p`, `q` and the computed difference. |
| `Model.abs_roundAt_add_roundAt_sub_le` | The fused form: `round (p + round q)` is within `u |p + q| + u |q| + 3 η` of `p + q`. |

### Error bounds of whole complex operations

Import `FloatLib.Floats.Formats.BinaryInterchange.Complex.ErrorBounds`, also exported by
`FloatLib`. `Complex.Semantics` states the roundings of each operation of `ExecComplex fmt`
(`toComplex_mul_eq_roundedMul` and its peers). The theorems here bound the whole operation
against the exact operation in `ℂ`. A `rounded…` theorem holds for every `FloatFormat` and all
complex arguments, and a `toComplex` theorem for every IEEE descriptor under the finiteness
premise of the semantic theorem. `x = a + b i`, `y = c + d i`.

| Theorem | Informal statement |
| --- | --- |
| `ExecComplex.abs_toComplex_add_sub_le`, `norm_toComplex_add_sub_le`, `abs_toComplex_sub_sub_le`, `norm_toComplex_sub_sub_le` | Each component of a finite sum or difference is within `u` times the exact component, with no underflow term, so the normwise relative error is at most `u`. |
| `ExecComplex.abs_roundedMul_sub_le`, `abs_toComplex_mul_sub_le` | The conventional product, componentwise: the real part is within `(2u + u²)(|a c| + |b d|) + (2 + 2u) η` of `a c - b d`, and the imaginary part within the same with `|a d| + |b c|`. The bound is relative to the sum of magnitudes; `a c - b d` can cancel. |
| `ExecComplex.norm_roundedMul_sub_le`, `norm_toComplex_mul_sub_le` | The conventional product, normwise: `‖fl(x y) - x y‖ ≤ √5 u ‖x y‖ + 5 η` when the format has at least five bits of precision (`4 ≤ fracWidth`). Theorem 1 of Brent, Percival and Zimmermann (Math. Comp. 2007), who assume no underflow and `u ≤ 2⁻⁵`. |
| `ExecComplex.toComplex_mulFma_eq_roundedMulFma`, `norm_roundedMulFma_sub_le`, `norm_toComplex_mulFma_sub_le` | `ExecComplex.mulFma` rounds `b d` and `b c` and then each component with one fused multiply-add, and `‖fl(x y) - x y‖ ≤ 2 u ‖x y‖ + 5 η` for every descriptor. `2u` is the constant of Jeannerod, Kornerup, Louvet and Muller (Math. Comp. 2017), who prove it without underflow for `β^(p-1) ≥ 24`. |
| `ExecComplex.norm_roundedDivRealDominant_sub_le`, `norm_roundedDiv_sub_le`, `norm_toComplex_div_sub_le`, `ExecComplex.DivNormal`, `pow_four_div_pow_three_sub_one_le` | Division by the ratio formula (Smith 1962), in both branches: `‖fl(x / y) - x / y‖ ≤ √2 ((1 + u)⁴ / (1 - u)³ - 1) ‖x / y‖` for grid-point operands when no product or quotient of the branch underflows (`DivNormal`). The constant is at most `√2 γ₇`, `γ₇ = 7u / (1 - 7u)`; it is what the proof gives (four roundings in each numerator, three in the denominator), and we know of no published proof of a normwise bound for this formula. Underflow is a premise here: an underflow of the denominator's product is a relative error `η / |c|` of the denominator. |
| `ExecComplex.abs_roundedMagnitude_sub_le`, `abs_toReal_magnitude_sub_le`, `ExecComplex.MagnitudeNormal` | The scaled magnitude: `|fl(|z|) - |z|| ≤ ((1 + u)⁴ - 1) |z| + η` when the two ratios, their squares and the square root do not underflow (`MagnitudeNormal`); `η` is the underflow of the last product. No published bound for this algorithm was found; the constant is what the proof gives. |

With `import FloatLib.Floats.Formats.BinaryInterchange.Complex.Roundoff`, `roundoff`,
`roundoff theorem` and `roundoff mixed theorem` bound a component of any program on
`ExecComplex fmt`: the rules `ExecComplex.toReal_add_re`, `toReal_mul_im`, `toReal_mulFma_re`,
`toReal_div_re`, `toReal_magnitude` and their peers state each component as the scalar
expression that computes it, and the scalar rules bound each rounding. The generated bound of a
quotient or a magnitude counts every underflow where it happens, for every IEEE descriptor.

### Correctly rounded complex elementary functions

The functions are C's `<complex.h>` functions on `ExecComplex fmt` (C23 7.3 and Annex G):
`sqrt`, `rSqrt`, `log`, `log1p`, `atanh`, `atan`, `exp`, `expm1`, `sinh`, `cosh`, `sin`, `cos`,
`tanh`, `tan`, `asinh`, `asin`, `acosh`, `acos` and `pow`. Each takes an `IEEERoundingMode`,
nearest-even by default, and has one definition for every binary format. They are not exported by
`FloatLib`: import a family under `FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary`
(`Algebraic`, `Logarithm`, `Exponential`, `Tangent`, `Inverse`, `Power`) and the module of the
same name with `Proof` appended for its theorems; `ValueProof` identifies the exact results.
The theorems hold for every IEEE descriptor and every rounding direction, with no premise on a
search budget.

| Theorem | Informal statement |
| --- | --- |
| `Model.roundReal`, `Model.RoundsTo`, `Model.RoundsTo.signBit_of_isIEEE`, `Model.roundReal_roundsTo`, `Model.AlgebraicRounding.roundSigned_eq_roundReal` | `roundReal fmt mode x` is the rounding of the real `x`: the grid rounding `roundAt fmt x mode` when that is at most the largest finite magnitude, the overflow result of IEEE 754-2019 7.4 otherwise, for every format descriptor, and in a format with signed zeros the sign bit of `x` in both cases. An executable oracle that orders `x` against every rational computes it (`AlgebraicRounding.roundSigned`). |
| `Model.roundReal_eq_of_mem_Icc`, `Model.AlgebraicRounding.roundReal_eq_of_roundEnclosure?`, `roundReal_eq_of_zivRound?`, `Model.eq_of_toReal_eq` | Ziv's rounding test in every direction: two reals of the same sign that round to the same encoding enclose only reals that round to it, so an enclosure whose endpoints round alike decides the rounding. Finite encodings with the same value, and the same sign at zero, are equal. |
| `Model.roundReal_of_upperExponent_le`, `Model.roundReal_of_lt_lowerExponent`, `Model.roundReal_signed` | The rounding of a real outside the range from a bound on one side, for every format descriptor and every direction: a magnitude of at least `2 ^ upperExponent fmt` gives the overflow result of its sign, and a nonzero magnitude below `2 ^ lowerExponent fmt`, half the least positive number, gives the zero of its sign, or the least number of its sign where the direction rounds the magnitude up. |
| `ExecComplex.Exact`, `ExecComplex.Exact.round`, `ExecComplex.Parts.Denotes`, `Parts.ofUpperHalf_denotes`, `Parts.ofQuadrant_denotes`, `Parts.Denotes.round` | An exact result is a complex value with the signs of its exactly zero parts, and `round` rounds each part once. Conjugation, parity and the multiplications by `±i` of C23 G.6.1 act on the parts before rounding, so they are exact in every direction. |
| `ExecComplex.sqrt_eq`, `rSqrt_eq`, `rSqrt_zero` | At every finite argument, `sqrt` is the principal root with each part rounded once; `rSqrt` is its reciprocal rounded once, at every finite argument but zero, where it is `+∞ + NaN i`. |
| `ExecComplex.log_eq`, `log1p_eq`, `atanh_eq`, `atan_eq` | `log` at every finite argument but zero, `log1p` but `0` and `-1`, `atanh` but `±1` and `atan` but `±i` round each part of the exact result once. |
| `ExecComplex.log_zero`, `log1p_zero`, `log1p_neg_one`, `atanh_one`, `atanh_neg_one`, `atan_I`, `atan_neg_I`, `expm1_zero` | The finite arguments that the rounding theorems exclude, for every descriptor and direction: `log (±0 ± 0 i)` is `-∞` with the angle `0` or `π` of the zero rounded once (C23 G.6.4.2), `log1p` and `expm1` return a zero unchanged, `log1p (-1 ± 0 i) = -∞ ± 0 i`, `atanh (±1 ± 0 i) = ±∞ ± 0 i` (G.6.3.3) and `atan (±0 ± i) = ±0 ± ∞ i`. With them every finite argument of the eighteen functions of one argument is covered by a theorem. |
| `ExecComplex.exp_eq`, `expm1_eq`, `sinh_eq`, `cosh_eq`, `sin_eq`, `cos_eq` | At every finite argument (`expm1`: but zero) each part is the exact part rounded once, also where `exp a` alone would overflow. |
| `ExecComplex.tanh_eq`, `tan_eq` | At every finite argument each part of the tangent is the exact part rounded once, at the cost of a small argument however large the real part is. |
| `ExecComplex.asinh_eq`, `asin_eq`, `acosh_eq`, `acos_eq` | At every finite argument each part of the inverse sine or cosine is the exact part rounded once, on both sides of each branch cut. |
| `ExecComplex.contains_smallProduct?`, `contains_smallLog?`, `contains_smallArg?`, `contains_smallTanh?`, `contains_smallTan?`, `contains_smallArcsin?`, `contains_orElse`, `arg_eq_arctan` | At an argument below `1 / 16` in magnitude a part is enclosed by Taylor polynomials in exact rational arithmetic with their remainder bounds (`Enclosure.contains_expSmall`, `contains_sin`, `contains_cos`, `contains_logOneSub`, `contains_atanSmall`), at a degree that leaves the remainder four orders of the argument below the working precision. Each enclosure contains the part, so the rounding theorems above hold unchanged, and it separates the part from the representable numbers next to it: where a function is the identity to first order the rounding of a small argument needs no exact comparison. |
| `ExecComplex.dyadicAround_bounds`, `contains_coarseLog`, `contains_coarseArg` | The logarithm and the principal argument at a rational that is written with thousands of bits, as one part of the argument being subnormal makes it, are enclosed from the two ends of a short dyadic interval around it, by monotonicity. |
| `ExecComplex.exp_conj`, `expm1_conj`, `log_conj`, `log1p_conj`, `sqrt_conj`, `rsqrt_conj`, `sinh_conj`, `cosh_conj`, `tanh_conj`, `sin_conj`, `cos_conj`, `tan_conj`, `asinh_conj`, `asin_conj`, `acosh_conj`, `acos_conj`, `atanh_conj`, `atan_conj`; `sinh_neg`, `tanh_neg`, `asinh_neg`, `atanh_neg`, `sin_neg`, `tan_neg`, `asin_neg`, `atan_neg`, `cosh_neg`, `cos_neg`; `Parts.ofUpperHalf_conj`, `Parts.ofQuadrant_neg`, `Model.roundReal_neg`, `Model.AlgebraicRounding.roundSigned_neg` | The symmetries that head the tables of C23 Annex G hold at every argument, a NaN or an infinity included. Each of the eighteen functions commutes with conjugation and the eight odd ones are odd, in the four rounding directions that negation fixes (the two to nearest, toward zero, away from zero); `cosh` and `cos` are even in every direction. They follow from the construction of the functions (`Parts.ofUpperHalf_conj`, `Parts.ofQuadrant_neg`) and from the rounding of a negated real: `roundReal fmt mode (-x)` is the negation of `roundReal fmt mode.negate x` with the opposite sign of an exact zero, and `mode.negate` exchanges `up` and `down`. |
| `ExecComplex.pow_eq`, `powChecked_eq`, `powExact`, `gaussRatPow?_spec`, `powExtreme?_eq`, `contains_powArguments` | A power that `powCertified` accepts, at a finite base other than zero and a finite exponent, is `exp (w log z)` with each part rounded once. Certified: a zero exponent, the base one, the exponent `1/2`, an exponent `n / 2 ^ k` of a base whose principal `2 ^ k`-th root is a complex rational (integer exponents, and `(-4) ^ (1/4) = 1 + i`), formed exactly when of moderate size, a base on an axis or a diagonal whose power stays on an axis, a part that overflows or lies below half the least positive number by its exponent `Re (w log z)` alone, at any size of that exponent, and every part that an enclosure decides, with the angle of the base taken from the nearest axis where a part lies next to zero. Not certified: a part exactly on a rounding boundary outside those cases, a part that the last of the `levels` enclosures does not separate from a boundary, and a part with an exponent beyond `±powExponentCap` whose cosine or sine the first enclosure does not separate from zero. |
| `ExecComplex.expExact_value`, `expm1Exact_value`, `sinhExact_value`, `coshExact_value`, `tanhExact_value`, `sinExact_value`, `cosExact_value`, `tanExact_value` | The exact result is Mathlib's `Complex.exp`, `sinh`, `cosh`, `tanh`, `sin`, `cos`, `tan` at the argument, in every half-plane and quadrant. |
| `ExecComplex.sqrtExact_value`, `rsqrtExact_value`, `logExact_value`, `log1pExact_value`, `atanhExact_value`, `atanExact_value` | Off its branch cut, and on the cut where the sign bit that selects the side is clear, the exact result is Mathlib's principal value: `w ^ (2⁻¹ : ℂ)`, its reciprocal, `Complex.log w`, `Complex.log (1 + w)`, `Complex.log ((1 + w) / (1 - w)) / 2` and `Complex.arctan w`. On the cut with that sign bit set it is the mirror image, the limit from the other side (C23 7.3.3). |
| `ExecComplex.asinhValue_eq_log`, `acoshValue_eq_log`, `asinhExact_value`, `asinExact_value`, `acoshExact_value`, `acosExact_value` | Mathlib has no complex inverse sine or cosine. In the closed right half-plane `asinhValue w` is `log (w + √(1 + w²))`, and in the closed upper half-plane `acoshValue w` is `2 log (√((w + 1) / 2) + √((w - 1) / 2))`, the principal expressions of Kahan's Table 1 in Mathlib's principal `Complex.log` and square root. So where the sign bits put the argument in the quadrant or half-plane of C23 Annex G, `asinh`, `asin`, `acosh` and `acos` round these expressions (`asin`: `-i log (i w + √(1 - w²))`, `acos`: `-i` times that of `acosh`), and elsewhere their images under the symmetries of G.6. |
| `ExecComplex.sqrtExact_value_sq`, `rsqrtExact_value_sq`, `exp_logExact_value`, `exp_log1pExact_value`, `sinh_asinhExact_value`, `sin_asinExact_value`, `cosh_acoshExact_value`, `cos_acosExact_value`, `tanh_atanhExact_value`, `tan_atanExact_value` | The exact results of the functions with a branch cut solve the defining equation at every finite argument, on both sides of a cut: the square of the root is the argument, `Complex.exp` of the logarithm is the argument, `Complex.sinh` of the inverse hyperbolic sine is the argument, and so on. The inverse sines and cosines lie in the principal ranges (`asinhValue_re_nonneg`, `abs_asinhValue_im_le`, `acoshValue_re_nonneg`, `acoshValue_im_mem`). |
| `Enclosure.gaussianInt_add_sum_exp_div_ne_zero`, `Enclosure.sum_exp_mul_trig_ne_ratCast` | A Gaussian integer combination of exponentials at nonzero Gaussian rational arguments does not cancel a nonzero Gaussian integer (a Lindemann-Weierstrass step), so `∑ exp aₖ (cₖ cos bₖ + dₖ sin bₖ)` at rationals with no `(aₖ, bₖ) = (0, 0)` is not a nonzero rational. |
| `ProductComparison.prepare_eq_real`, `TanhComparison.compareRe_eq_real`, `compareIm_eq_real`, `ConfocalComparison.compareArcosh_eq_real`, `compareArcsin_eq_real`, `compareArccos_eq_real` | Total exact comparators with a rational boundary: of `exp a cos b` and its relatives, of the parts of `tanh (a + i b)`, and of `arcosh`, `arcsin` and `arccos` of the half sum and half difference of the distances of a rational point to two foci. |
| `ProductComparison.contains_trigBounds?`, `ProductComparison.Trig.converges_intervals`, `ConfocalComparison.arccos_eq_two_mul_arctan` | `trigBounds?` encloses the cosine or the sine of every real in a rational interval of any size: it subtracts quarter turns with the cached `π / 2` at as many bits as the angle needs, and uses `a - a³ / 6 < sin a < a` at small angles, so the relative accuracy does not depend on the size of the angle. The enclosures that the exact comparators refine start with these and converge. The inverse cosine of `m` in `[0, 1]` is `2 arctan √((1 - m) / (1 + m))`, the form that keeps the relative accuracy of a small result. |
| `RationalInterval.Converges`, `Converges.mul`, `Converges.prefixed`, `Converges.compare_eq`, `RationalInterval.contains_mul` | Sequences of rational enclosures that converge to a real are closed under the interval operations and under replacing a prefix by other sound enclosures, and the comparison of such a sequence with a rational is the order of its limit. |

### IEEE status flags

Import `FloatLib.Floats.Formats.BinaryInterchange.Status`.

With `(status := true)`, the operations `add`, `sub`, `mul`, `div`, `fma`, and `sqrt` return the
result together with its five IEEE flags and its ternary value, and so do `roundToIntegral`,
`scale`, `logB`, `remainder`, `nextUp`, `nextDown`, `minimum`, `maximum`, `minimumNumber`,
`maximumNumber`, `cast`, `sum`, and `ExecDType.convertFromInt`. `dot` and `parse` return it inside their
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
`sqrt_status_of_signBit`, and `sqrt_status_of_isInfinite` state the outcome on every class of input. When
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
| `ExecFloat.Binary.IEEEOutcome.toModel_remainder`, `toModel_roundToIntegral`, `toModel_scale`, `toModel_logB`, `toModel_nextUp`, `toModel_nextDown`, `toModel_minimum`, `toModel_maximum`, `toModel_minimumNumber`, `toModel_maximumNumber` and `ExecFloat.Binary.value_remainder` through `value_maximumNumber` | The same decoding and projection statements for the configured standard operations (`Configured.Operations.Proof`). `min_eq_minimum` and `max_eq_maximum` state that `min` and `max` run the configured `minimum` and `maximum`. |

Apart from the nearest-even default, which runs the selected capability, the configured functions
just repackage the existing descriptor-model operations. Since the bridge theorems above are `simp`
lemmas, a goal about a configured operation reduces to the corresponding `Model` theorem in
`Status.Proof` or `DirectedSemantics`.

We accumulate sticky flags with `FloatLib.Numerics.IEEEStatus.union`. Binary and decimal operations
report the same record, `Numerics.IEEEStatus`, and selection, clearing, saving, testing, and
restoration share one implementation too. `Numerics.IEEEStatus.Proof` proves their laws for every
flag state and selected group, and the decimal namespace exports those results.

### Exact integer exponents

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Proof`. `logBInt`
returns the exact integer exponent of a finite nonzero input, and `logB`, the same-format
convenience operation, rounds that integer into the source format.

| Theorem | Informal statement |
| --- | --- |
| `Model.logBInt_of_finite_nonzero` | The integer result is the significand's integer binary logarithm plus its stored exponent, with clear status. |
| `Model.logBInt_bounds` | Its exponent brackets the exact magnitude between consecutive powers of two. |
| `Model.logBSentinel_outside_logBBound` | The exceptional sentinel lies beyond twice the IEEE exceptional-result bound. |
| `Model.logBInt_mem_exponentRange`, `Model.abs_logBInt_lt_logBSentinel` | A finite nonzero answer lies between the least subnormal and the largest normal exponent, so it never equals the sentinel or its negation. |
| `Model.logBInt_of_zero`, `logBInt_of_infinity`, `logBInt_of_nan` | Zero returns a negative sentinel; infinity and NaN return a positive sentinel; each raises invalid. |

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

### Recommended operations of IEEE 754-2019 clause 9

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.Proof` for configured
values, or the `Proof` module of `Operations.MagnitudeExtrema`, `Operations.Payload` and
`Operations.Augmented` for the descriptor model. The text of IEEE 754-2019 is not public. Names
and special cases follow ISO/IEC 9899:2024 (C23, N3220) 7.12.12.6 to 7.12.12.11, F.10.9.4,
F.10.9.5 and F.10.13 for §9.6 and §9.7, and Riedy and Demmel (ARITH 2018) and Boldo, Lauter and
Muller (IEEE Transactions on Computers 70(7), 2021) for §9.5. The definitions cover every
`FloatFormat`; a theorem names the descriptors it needs.

| Theorem | Informal statement |
| --- | --- |
| `Model.magnitudeExtremum_of_compare_abs_lt`, `magnitudeExtremum_of_compare_abs_gt`, `magnitudeExtremum_of_compare_abs_eq`, `magnitudeExtremum_of_isNaN` | §9.6: `minimumMagnitude`, `maximumMagnitude`, `minimumMagnitudeNumber` and `maximumMagnitudeNumber` select the operand of smaller or larger magnitude, and are `minimum`, `maximum`, `minimumNumber` or `maximumNumber` when the magnitudes are equal or an operand is a NaN. |
| `Model.magnitudeExtremum_status`, `Model.value_magnitudeExtremum` | The four operations raise `invalid` exactly for a signaling NaN operand, and their value with `status := true` is the value without it. |
| `Model.abs_toReal_minimumMagnitude`, `abs_toReal_maximumMagnitude`, `abs_toReal_minimumMagnitudeNumber`, `abs_toReal_maximumMagnitudeNumber` | On finite operands of a format with signed zero the magnitude of the result is the `min` or `max` of the magnitudes. |
| `Model.getPayload_setPayload`, `Model.setPayload_getPayload`, `Model.toReal_getPayload` | §9.7: reading the payload of `setPayload x` gives an admissible `x` back; writing back the payload of a NaN gives the quiet NaN with that payload and a clear sign; `getPayload` of a NaN denotes its payload exactly (the last two for an IEEE descriptor whose exponent range reaches `2 ^ fracWidth`). |
| `Model.isNaN_setPayload`, `Model.signBit_setPayload`, `Model.getPayload_of_isNaN_eq_false`, `Model.setPayload_of_admissiblePayload?_eq_none` | `setPayload` gives a NaN exactly for an admissible operand, with a clear sign bit; the results outside the domains are `-1` and `+0`. |
| `Model.isSignaling_setPayloadSignaling`, `Model.getPayload_setPayloadSignaling` | In the IEEE encoding a nonzero admissible payload gives a signaling NaN whose payload reads back as the operand. |
| `Model.roundTiesTowardZeroAt_dyadic`, `Model.toReal_roundDyadicTiesTowardZero` | §9.5: the executable rounding to nearest with ties toward zero computes the real rounding `roundTiesTowardZeroAt`, for every descriptor on the unbounded grid and for a finite result of an IEEE descriptor. |
| `Model.toReal_augmentedAddition_head`, `Model.toReal_augmentedAddition_add` | With a finite head, the head of `augmentedAddition` is the sum rounded to nearest with ties toward zero, head and tail add up to the exact sum, the tail is finite and no flag is raised (IEEE descriptors). |
| `Model.toReal_augmentedSubtraction_sub` | The same for `augmentedSubtraction` and the exact difference. |
| `Model.toReal_augmentedMultiplication_head`, `toReal_augmentedMultiplication_tail`, `augmentedMultiplication_inexact_iff` | Head and tail of `augmentedMultiplication` are the two roundings of the product and of its error, and `inexact` (with `underflow`) is raised exactly when they do not add up to the product. |
| `Model.augmentedAddition_of_isFinite_head_eq_false`, `augmentedMultiplication_of_isFinite_head_eq_false`, `augmentedAddition_of_isFinite_eq_false`, `augmentedMultiplication_of_isFinite_eq_false` | An overflowing head comes with an equal tail and the flags `overflow` and `inexact`; an operand that is not finite gives the special value of ordinary addition or multiplication as head and tail. |
| `ExecFloat.Binary.toModel_magnitudeExtremum`, `toModel_getPayload`, `toModel_setPayload`, `toModel_setPayloadSignaling`, `map_toModel_augmentedAddition`, `map_toModel_augmentedSubtraction`, `map_toModel_augmentedMultiplication`, `toReal_augmentedAddition_add` | Decoding a configured result gives the model operation on the decoded operands, in every storage plan, and the error-free transformation holds for configured values. |

### Operation names of IEEE 754-2019

`FloatLib.Numerics.IEEENames` has three commands, `ieee_by_direction`, `ieee_by_predicate` and
`ieee_extrema`, that declare the members of an operation family under the names of the standard
(ISO/IEC 9899:2024 Annex F, Table F.2): `roundToIntegralTiesToEven` to
`roundToIntegralTowardNegative`, `convertToIntegerTiesToEven` to
`convertToIntegerExactTowardNegative`, and the 22 comparisons `compareQuietEqual` to
`compareSignalingGreaterUnordered`. Each member is its family at one rounding direction or
predicate by definition, so the theorems of `roundToIntegral`, `convertToIntegerExact`,
`compareQuiet` and `compareSignaling` apply after unfolding.

| Theorem | Informal statement |
| --- | --- |
| `ExecDType.convertToInteger_of_convertToIntegerExact_eq_success`, `convertToInteger_of_convertToIntegerExact_eq_failure` | §5.4.1: `convertToInteger` delivers the integer of `convertToIntegerExact` without the inexact signal and fails for the same reasons. |
| `IEEE754.Modes.getBinaryRoundingDirection_setBinaryRoundingDirection`, `getDecimalRoundingDirection_setDecimalRoundingDirection`, `getDecimalRoundingDirection_setBinaryRoundingDirection`, `getBinaryRoundingDirection_setDecimalRoundingDirection`, `restoreModes_saveModes` | §9.3: a direction that was set is the one read, setting one radix leaves the other, and restoring saved modes brings both back. |

### Operands and result in different formats

Import `FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Proof`. IEEE 754-2019
§5.4.1 specifies its arithmetic as formatOf operations: the operands may have any formats of
the radix and the exact result is rounded once into the destination (ISO/IEC 9899:2024 F.3
paragraph 2 states the requirement for C). `Model.formatOfAddition`, `formatOfSubtraction`,
`formatOfMultiplication`, `formatOfDivision` and `formatOfFusedMultiplyAdd` take any three
(for the fused operation four) descriptors and any rounding direction and return the value with
its flags and ternary value. Across formats the theorems are for finite operands: the value in
every direction for the sum, the difference, the product and the fused operation, and to
nearest-even for the quotient. In one format the whole outcome is proved for every operand,
NaNs and infinities included. The flags and the special cases across three formats are checked
by `oracle ieee2019 formatOf` with the rules of the standard on a six-bit format in six
directions.

| Theorem | Informal statement |
| --- | --- |
| `Model.toReal_formatOfAddition`, `toReal_formatOfSubtraction`, `toReal_formatOfMultiplication`, `toReal_formatOfFusedMultiplyAdd` | For finite operands of any formats and a conventional IEEE destination, a finite result to nearest-even denotes `roundAt destination` of the exact real sum, difference, product, or `x * y + z`: one rounding, where `cast` after an operation in a source format would round twice. |
| `Model.toReal_formatOfDivision` | The same for the quotient of a finite dividend and a finite nonzero divisor. |
| `Model.formatOfAddition_finite_roundAt`, `formatOfSubtraction_finite_roundAt`, `formatOfMultiplication_finite_roundAt`, `formatOfFusedMultiplyAdd_finite_roundAt`, `Factor.deliver_finite_roundAt` | **The formatOf operations round once in every direction.** For finite operands of any formats, a conventional IEEE destination and each rounding direction `mode`, an exact sum, difference, product or `x * y + z` within the largest finite magnitude of the destination gives a finite result that denotes `roundAt destination` of the exact value in that direction. |
| `Model.formatOfAddition_of_toDyadic?_eq_some`, `formatOfMultiplication_of_toDyadic?_eq_some`, `formatOfFusedMultiplyAdd_of_toDyadic?_eq_some`, `formatOfDivision_value_of_toDyadic?_eq_some` | In every rounding direction the outcome for finite operands is the delivery of the exact dyadic result (`Factor.deliver`): the sign rule of the direction for an exact zero, and otherwise the direction's rounding kernel applied once in the destination, `Internal.Directed.roundDyadic`, or `roundRatScaled` for a quotient. |
| `Model.formatOfAddition_value_eq_add`, `formatOfSubtraction_value_eq_sub`, `formatOfMultiplication_value_eq_mul`, `formatOfDivision_value_eq_div`, `formatOfFusedMultiplyAdd_value_eq_fma` | In one format (operands and destination) the value of each formatOf operation is `Model.add`, `sub`, `mul`, `div` and `fma` in the same rounding direction, for every operand, every descriptor and every direction: the same rounded result, the same signed zero of an exact zero, the same infinity or default NaN of a division by zero, and the same NaN or infinity for operands that are not finite. Import `Operations.FormatOf.Homogeneous`. |
| `Model.Reduction.Internal.Factor.deliver_finite_value`, `Factor.toReal_deliver_finite` | The delivery of a finite exact result: its value in every direction, and its real value `roundAt destination exact.toReal` to nearest-even when it is finite. |
| `Model.formatOfAddition_eq_add`, `formatOfSubtraction_eq_sub`, `formatOfMultiplication_eq_mul`, `formatOfDivision_eq_div`, `formatOfFusedMultiplyAdd_eq_fma`, `dyadicRoundingOutcome_zero` | **In one format the formatOf operations are the operations of that format.** The whole outcome of each formatOf operation, the value, the five exception flags and the ternary value, is that of `Model.add`, `sub`, `mul`, `div` and `fma` with flags in the same rounding direction, for every operand (finite, infinite or NaN), every descriptor and every direction. That covers the NaN that NaN operands select, `invalid` for a signaling NaN, for infinities of opposite signs added, for zero times infinity and for infinity divided by infinity, and the exact infinities. |
| `Model.Reduction.Internal.Factor.ofValue_self`, `Model.cast_quietNaN_self`, `quietNaN_quietNaN`, `eq_nativeOverflow_of_isInfinite`, `exactInfinityTernary_nativeOverflow` | What the formatOf operations read of an operand of the destination format: its exact dyadic when it is finite, the operand quieted when it is a NaN (a cast within one format returns a quieted NaN unchanged, and quieting twice is quieting once), and the overflow result of its sign when it is an infinity, which only the IEEE encoding has. |
| `Model.formatOfSquareRoot_roundsTo`, `toReal_formatOfSquareRoot`, `formatOfSquareRoot_inexact_iff` | **The formatOf square root is correctly rounded in every direction.** For every destination descriptor, a finite positive operand of any binary format and each direction `mode`, `formatOfSquareRoot` meets `RoundsTo destination mode (sqrt q)`: one rounding of the real root into the destination, with the overflow result of the direction. To nearest-even into an IEEE destination a finite result is `roundAt destination (sqrt q)`, and `inexact` is raised exactly when the finite result is not the root. Import `Operations.FormatOf.SquareRoot.Proof`. |
| `Model.formatOfSquareRoot_of_isZero`, `formatOfSquareRoot_of_isNaN`, `formatOfSquareRoot_of_isInfinite`, `formatOfSquareRoot_of_negative`, `formatOfSquareRoot_eq_sqrt`, `formatOfSquareRoot_value_eq_sqrt` | The square root of a zero is the zero of its sign without a flag, a NaN is quieted and converted with `invalid` when it was signaling, the positive infinity gives the infinity of the destination, and the negative infinity and a negative number give the default NaN with `invalid`. In one format these outcomes, value, flags and ternary value, are those of `Model.sqrt` in every direction and for every descriptor, and for a finite positive operand of an IEEE format the value to nearest-even is `Model.sqrt`. |

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
| `Backend.Certified.run_eq_spec`, `Backend.selectCertified_run_eq_spec`, `ExecFloat.Capability.run_eq_spec` | A certified candidate is a kernel with its cost estimate and the proof `run = spec`, so the candidate the planner selects computes the specification under every policy and every candidate set, and the operation a capability runs is its reference operation. `@[compiler_optimize]` (`FloatLib.Tactic.CompilerOptimize`) registers such a candidate for every format its specification covers, `Capability.ofTagged` and `Capability.ofStatic` build a family's capability from the tagged candidates, and `#compiler_backends` (`FloatLib.Tactic.CompilerBackends`) prints the registry. |
| `Model.NativePair.addFinite_eq`, `subFinite_eq`, `fmaFinite_eq` | On two 64-bit words, for every IEEE layout of at most 128 bits whose fraction is wider than one word (`NativePair.Eligible`), the fast finite addition, subtraction, and fused multiply-add agree with the exact finite kernel whenever they accept. |
| `Model.NativePair.mulNormalLimb_refines`, `divNormal_refines`, `sqrtNormal_refines` | The two-word normal multiplication, division (Algorithm D candidate, independent certificate, proved restoring repair), and square root refine the reference specification under the same eligibility. |
| `Model.WideLimb.toModel_add`, `toModel_sub`, `toModel_mul`, `toModel_div`, `toModel_sqrt`, `toModel_fma` | On the 32-bit limb carrier of `ExecFloat.BinaryLimbs`, for every IEEE layout wider than 128 bits with an exponent field of at most 32 bits, all six operations decode to their complete `Model.Spec` results. Division uses a direct integer quotient for finite inputs; square root uses an integer root for positive normal inputs, with exact fallbacks elsewhere. |
| `Model.NativeSmallWordAdd.addFinite_refines` | The all-`UInt64` addition and subtraction kernel for IEEE layouts within one machine word refines the exact finite kernel whenever it accepts. |

### Computing in the kernel

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath` for configured binary
types, `StaticByte.KernelPath` for the one-byte families, or `Descriptor.KernelPath` for plain
descriptors. Each brings `KernelPath.Value` and the tactic `float_decide`. The operations below
work on the natural-number encoding with operations that Lean's kernel computes natively, so a
closed statement about a floating-point computation can be checked by the kernel at about a
tenth of a millisecond per operation. Unless a row says otherwise, a theorem holds for every
`FloatFormat` (any field widths, any of the four encodings), every one of the six rounding
directions of `Model.IEEERoundingMode` and every operand.

| Theorem | Informal statement |
| --- | --- |
| `KernelPath.add_eq_spec`, `sub_eq_spec`, `mul_eq_spec`, `div_eq_spec`, `sqrt_eq_spec`, `fma_eq_spec` | Each kernel operation on encodings returns the encoding of the reference result in the direction `mode`: `KernelPath.add fmt mode x.toNatBits y.toNatBits = (Model.add x y (mode := mode)).toNatBits`, and the same for the other five. Finite operands are computed with shifts, masks, one comparison and, for division and square root, one or eight divisions. A square root whose eight Newton steps fail the check is computed again with sixteen, which reaches fractions of tens of thousands of bits. An infinity, a NaN, a zero divisor, and a zero or negative radicand are answered by the rules of the reference with flags computed on the encoding. Only the square root of a positive finite value in a format with `exponentBias < fracWidth + 1` takes the reference definition. Sums, products, quotients, square roots and the general rounding do not build a power of two of the size of an exponent difference (`roundAt_def`, `roundUpShift_eq`, `gap_clamped`, `divCore_def`), so their cost does not grow with the exponent range: the division works on numbers of about twice the significand width whatever the exponents of its operands are. |
| `KernelPath.addShort_eq_spec`, `subShort_eq_spec`, `mulFast_eq_spec` | The short paths that `float_decide` runs first compute the same encodings. A sum of two values of one sign that keeps the exponent of the larger operand is one addition on the words and one comparison (`addSameWith_eq`), a sum that carries takes `addCarryWith_eq`; neither builds a power of two of the size of the exponent gap (`roundUpShift_eq`, `gap_clamped`), so a sum with a zero costs the same in a format with a 35-bit exponent field, and a sum of two subnormal numbers is the sum of the words (`sumOrdered_tiny`). A difference that loses at most one leading bit and a product of two normal numbers take one rounding of a fixed shape (`sumOrdered_eq`, `mulFast_eq`). Every other case falls back to the general operation. |
| `KernelPath.Reference`: `add_of_finite`, `mul_of_finite`, `fma_of_finite`, `div_of_finite`, `sqrt_of_positive`, `add_of_nonFinite`, `mul_of_nonFinite`, `fma_of_nonFinite`, `div_of_nonFinite`, `sqrt_cases` | The reference operations in one shape for all six directions: one rounding of the exact result for finite operands, and the nearest-even specification, whose NaN and infinity rules do not depend on the direction, for the others. |
| `KernelPath.addSpecial_eq`, `mulSpecial_eq`, `divSpecial_eq_of_nonFinite`, `divSpecial_eq_of_zero_divisor`, `sqrtSpecial_eq`, `fmaSpecial_eq` | The results for operands that are not all finite: the NaN that `Model.chooseNaN2` or `chooseNaN3` selects with its quiet bit set, the invalid result, the signed infinity or the signed zero, in each of the four encodings. |
| `KernelPath.infFlag_eq`, `nanFlag_eq`, `zeroFlag_eq`, `signalingFlag_eq`, `quietNaN_bits` | The arithmetic flags on a word are `Model.isInfinite`, `isNaN`, `isZero` and `isSignaling`, and quieting a NaN is one `Nat.lor`, in every encoding. |
| `KernelPath.neg_eq_spec` | Negation on encodings is `Model.neg`. |
| `KernelPath.round_eq`, `roundUp_eq` | The shared rounding stage: `KernelPath.round` packs the rounding in the direction `mode` of a sign, a natural significand and a natural exponent pair, and equals the encoding of `Model.Internal.Directed.roundDyadic` on that dyadic, subnormal results, zeros and overflow included. `roundUp` is the rounding increment of the reference quotient rounding `Model.Policy.roundQuot`. |
| `Numerics.Kernel.bitLength_eq`, `laneLength_eq`, `searchLength_eq`, `KernelPath.significandLength_eq` | The bit length of a natural below `2 ^ B` is `Nat.log2 n + 1` (and `0` at `0`), for every `B`. `laneLength` computes it in seven accelerated operations by comparing with every power of two at once, on numbers of `B * (B + 1)` bits; `searchLength` by a binary search; `bitLength` takes the lanes up to 384 bits and beyond them, up to `2 ^ 24` bits, a search down to a window of 128 bits, so that the general rounding does not grow with the square of the width; `significandLength` answers for a significand with its leading bit set after one comparison. |
| `KernelPath.addStatus_eq`, `subStatus_eq`, `mulStatus_eq`, `fmaStatus_eq`, `roundStatus_eq`, `decodeStatus_eq_iff` | The IEEE status flags and the ternary value of addition, subtraction, multiplication and fused multiply-add: the number `KernelPath.addStatus fmt mode a b` decodes to the flags and the ternary value of `Model.add x y (mode := mode) (status := true)`, and the same for the other three. `roundStatus_eq` is the shared step: threshold comparisons on naturals compute `Model.dyadicRoundingStatus` and `Model.dyadicTernary` of any exact dyadic result and any delivered value. `decodeStatus_eq_iff` turns a statement that the flags are a given record into one comparison of natural numbers. The status numbers put the exact result on a grid of absolute exponents, so their cost grows with the exponent range of the format: they are meant for formats up to binary256. |
| `KernelPath.divStatus_eq`, `rationalRoundingStatusScaled_sticky`, `rationalTernaryScaled_sticky` | The status flags and the ternary value of division: `divStatus fmt mode a b` decodes to those of `Model.div x y (mode := mode) (status := true)`, with divide by zero, the invalid cases, overflow, underflow and inexactness. The two bridge theorems reduce the reference status of any rational result `± (n / d) * 2 ^ e` to the status of its sticky dyadic: the floor of the rational in units of `2 ^ (minSubnormalExponent - 2)`, doubled, plus one for a remainder. They hold for every delivered value, and `roundStatus_eq` then gives the flags. |
| `KernelPath.sqrtStatus_eq` | The status flags and the ternary value of the square root: `sqrtStatus fmt mode a` decodes to those of `Model.sqrt x (mode := mode) (status := true)`. On the checked path the root is inexact exactly when the scaled significand is not a square, and the ternary value is the comparison of the squared delivered root with it. |
| `KernelPath.roundToIntegralStatus_eq` | The status flags and the ternary value of rounding to an integral value: `roundToIntegralStatus fmt mode a` decodes to those of `Model.roundToIntegral x mode (status := true)`. In a conventional IEEE format with `fracWidth + exponentBias ≤ maxFiniteExpField` the result is inexact exactly when the operand has bits below the units place, and the ternary value comes from `roundStatus`. |
| `KernelPath.ratioStatus_eq`, `ofRat_status_eq` | The status flags and the ternary value of a rounded rational number: `ratioStatus fmt mode sign num den` decodes to those of delivering the reference rounding of `± num / den`, for every nonzero denominator, through the same sticky bridge as division. `ofRat_status_eq` states it for `Model.ofRat fmt q (mode := mode) (status := true)` and every rational `q`. |
| `KernelPath.ofScientific_eq`, `ofNatural_eq`, `ofRatio_eq_directed` | Literals: the encoding of a scientific literal and of a natural-number literal is that of `Model.ofRat` of its value, and `ofRatio fmt mode sign num den` is the encoding of the rational `± num / den` rounded in the direction `mode` (`Model.Internal.Directed.roundRat`). |
| `KernelPath.compareCode_eq`, `nanCode_eq`, `infCode_eq`, `zeroCode_eq`, `finiteCode_eq`, `signCode_eq` | Comparison and classification on encodings: `compareCode` decodes to `Model.compare` (NaNs are unordered, the zeros are equal), and the five codes are `Model.isNaN`, `isInfinite`, `isZero`, `isFinite` and `signBit`. The total order is `totalOrderCode_eq` below. |
| `KernelPath.ratValue_eq` | The exact rational value: `ratValue fmt x.toNatBits` is the value `Numerics.Dyadic.toRat` of the dyadic that a finite `x` decodes to, for every descriptor. The kernel builds it as one fraction: the signed significand shifted by the exponent field, over `2 ^ (exponentBias + fracWidth - 1)`. |
| `KernelPath.totalOrderCode_eq` | The IEEE total order: `Nat.beq (totalOrderCode fmt x.toNatBits y.toNatBits) 1 = Model.totalOrder x y`, for every descriptor and all operands. Two words that are not NaNs are ordered by their comparison keys with the negative ones moved down by one, which separates the two zeros; NaNs are ordered by sign, signaling class and fraction. |
| `KernelPath.cast_eq_spec` | Casts between any two descriptors: `cast src dst mode x.toNatBits = (Model.cast src dst x mode).toNatBits`, with the NaN payload rule, the overflow rule of the destination and rounding in the direction `mode`. |
| `KernelPath.castStatus_eq` | The status flags and the ternary value of a cast, for every pair of descriptors: `castStatus src dst mode a` decodes to those of `Model.cast src dst x mode (status := true)`. A finite value is its own exact result on the scale of the destination; an infinity raises overflow and inexact when the destination has no infinity; a NaN raises invalid when it is signaling or when the destination has no NaN. |
| `KernelPath.intMagnitude_eq`, `roundToIntegral_eq_spec` | Integers: the integer that rounds a finite value in the direction `mode` (`Model.roundDyadicToInt`) has the magnitude `intMagnitude fmt mode` of its encoding and the sign of the value, and `roundToIntegral fmt mode` is the encoding of `Model.roundToIntegral x mode`. |
| `KernelPath.Value.add_eq`, `sub_eq`, `mul_eq`, `div_eq`, `sqrt_eq`, `fma_eq` | For every family with a `KernelPath.NatView` instance whose capability has the lifted model operation as its reference, the public operation `ExecFloat.add x y` equals the kernel operation `KernelPath.Value.add .nearest x y`, and the same for the other five. The instances cover every configured binary type and storage plan, every static-byte family, and every descriptor. |
| `KernelPath.Value.add_notation_eq`, `sub_notation_eq`, `mul_notation_eq`, `div_notation_eq` | The same equations for `x + y`, `x - y`, `x * y` and `x / y`. |
| `Configured.liftBinary_add_eq`, `liftBinary_sub_eq`, `liftBinary_mul_eq`, `liftBinary_div_eq`, `liftTernary_fma_eq`, `liftUnary_sqrt_eq`, `liftUnary_roundToIntegral_eq`, `toInt?_eq`, `ofRat_eq`, `ofRat_outcome_eq`, `cast_eq`, `cast_status_eq`, `totalOrder_eq`, `toRat?_eq`, `add_outcome_eq`, `sub_outcome_eq`, `mul_outcome_eq`, `fma_outcome_eq`, `div_outcome_eq`, `sqrt_outcome_eq`, `roundToIntegral_outcome_eq`, `lt_eq`, `le_eq`, `isNaN_eq`, `isInfinite_eq`, `isZero_eq`, `isFinite_eq`, `signBit_eq`, `toNatBits_eq`, `ofNatBits_eq` | For configured binary types in every storage plan: an operation of `ExecFloat.Binary` called with a rounding direction, with `status := true` (the six arithmetic operations, integral rounding and rational literals), a conversion to an integer or to the exact rational value, a rational literal, a comparison, the total order or a classification equals its kernel operation on stored values or on encodings. The optional results of `toInt?` and `toRat?` are stated with `KernelPath.someWhen`, so that the rewrite of a loop of any length stays cheap to check. The cast rules rewrite the reference cast `Model.cast` of a decoded configured value, its flags and its ternary value; the public conversion `x.cast (target := T)` runs through the conversion framework and is not rewritten. |
| `KernelPath.addStatusWith`, `subStatusWith`, `mulStatusWith`, `fmaStatusWith`, `divStatusWith`, `roundToIntegralStatusWith`, `castStatusWith`, `ratioStatusWith`, `KernelPath.Value.add_status_eq_with`, `sub_status_eq_with`, `mul_status_eq_with`, `fma_status_eq_with`, `div_status_eq_with`, `roundToIntegral_status_eq_with`, `ofRatio_status_eq_with`, `Flat.castStatusWith_cast`, `Configured.add_outcome_eq_with`, `sub_outcome_eq_with`, `mul_outcome_eq_with`, `fma_outcome_eq_with`, `div_outcome_eq_with`, `roundToIntegral_outcome_eq_with`, `ofRat_outcome_eq_with`, `cast_status_eq_with` | The status numbers as functions of the delivered word: `addStatus fmt mode a b` is `addStatusWith fmt mode a b (add fmt mode a b)`, and the same for the other seven. The `status_eq_with` theorems give the flat status number of an operation as the flat function at the encoding of its kernel value, for every family with a `KernelPath.NatView` instance. The `outcome_eq_with` rules state the outcome of a configured operation with `status := true` in that form, and `cast_status_eq_with` the flags and the ternary value of a reference cast. A statement about the value and the flags of one operation then contains the value once, and Lean's kernel computes it once. The rules declare a kernel cost, so `float_decide` rewrites with them where `add_outcome_eq`, `cast_status_eq` and their siblings also match. |
| `ExecFloat.KernelPath.foldl_range`, `foldl_range'` | A left fold over `List.range n` or over `List.range' lo n step` is the primitive recursion on `n` with the same step, which the kernel runs in about four microseconds per step instead of fifty. |
| `ExecFloat.KernelPath.forall_fin_pairs` | A statement about all pairs of indices below `n` follows from one loop over the `n * n` pairs that counts no failure. `float_decide` uses it for a goal `∀ a b : Fin n, P a b`. |
| `Numerics.Packed.Expr.run_holds`, `Numerics.Packed.forall_pairs` | Lane programs: a program in the kernel's natural-number operations, run on rows that hold one number per lane, computes in every lane without an error the number that the program denotes, for every program and every lane width. So an equation between two functions of two indices holds on all pairs below `n` when one run of each side on rows of `n * n` lanes gives the same row. `lane_decide` proves a goal `∀ a b : Fin n, lhs = rhs` this way, reading the programs off the definitions, for the staged kernel operations of a small format among others. |
| `Numerics.Packed.lane_table`, `lane_pairsRow`, `lane_eq_of_differences` | Packed tables: lane `a * n + b` of a literal is `f a b` for all indices below `n`, when the program of `f` runs on all lanes without an error and its row has no difference with the literal. `lane_table` declares such a table with its lookup theorem. |
| `KernelPath.Value.toNat_of_table`, `E4M3.toNat_add_nearest` and its siblings | The encoding of a sum, difference or product of two stored values of a format of at most eight bits is one lane of its packed table (`kernel_tables`, in `Formats.OCP.FP8.KernelTables` for E4M3 and E5M2). The rules are tagged `@[kernel_optimize (cost := 4)]`, so `float_decide` looks the result up where the tables are imported. |
| `ExecFloat.KernelPath.add_eq_form`, `sub_eq_form`, `mul_eq_form`, `div_eq_form`, `sqrt_eq_form`, `fma_eq_form` and the four `_notation_eq_form` rules | For every format with a `KernelPath.KernelForm F operation form` instance, the public operation and its notation equal `form`, the proved form that Lean's kernel should evaluate. `KernelPath.DirectReference` gives the reference operation as the form (exact fixed point, logarithmic values, the bipolar codebook, P3109). |
| `Posit.Configured.Backend.dyadicAdd`, `dyadicSub`, `dyadicMul`, `dyadicDiv`, `dyadicSqrt`, `dyadicFma` with their `KernelPath.KernelForm` instances | For every posit format, storage plan and carrier, the public operation equals the direct dyadic operation on the decoded words (`Model.DirectDyadicArithmetic`), so `float_decide` evaluates posits without the plan's selection and without machine-word kernels. One registration schema reuses these existing backends and their refinement proofs. Posit Standard (2022), §§5.4–5.5; FMA is a FloatLib extension using §4.1 rounding. `Posit.Configured.ofRat_eq_kernel`, `ofScientific_eq_kernel` and `ofNat_eq_kernel` rewrite a literal to the flat rounding of a ratio of natural numbers on encodings (`Posit.KernelPath.Flat.ofRatio`): the numerator and the denominator of a rational, and the mantissa and the power of ten of a decimal literal as written. |
| `Posit.KernelPath.add_eq_spec`, `sub_eq_spec`, `mul_eq_spec`, `div_eq_spec`, `sqrt_eq_spec`, `fma_eq_spec`, `neg_eq`, `abs_eq`, `next_eq`, `prior_eq`, `lt_eq`, `le_eq`, `cast_eq_spec`, `ofRatio_eq` | Posit Standard (2022), §§3–4, 5.3–5.5 and 5.11: the operations of `Posit.KernelPath.Core` on natural-number encodings (the regime read by one bit length, exact integer arithmetic, one rounding of a bit stream) return the encoding of the specified result, for every standard width and every operand, NaR and zero included. FMA is a FloatLib extension with §4.1 rounding. These are the statements at `es = 2`; the functions take `es` as a parameter. |
| `Posit.KernelPath.add_eq_kernel`, `sub_eq_kernel`, `mul_eq_kernel`, `div_eq_kernel`, `sqrt_eq_kernel`, `fma_eq_kernel`, `negate_eq_kernel`, `abs_eq_kernel`, `next_eq_kernel`, `prior_eq_kernel`, `pₘToₙ_eq_kernel`, the six `compare*_eq_kernel` rules, `lt_iff_kernel`, `le_iff_kernel` | The `@[kernel_optimize]` rules of `Posit.KernelPath.Model`: each model operation is the word that stores the one-term operation of `Posit.KernelPath.Flat` on the encodings, so `float_decide` leaves Lean's kernel a closed natural-number computation. They assert equality for every standard width and every operand, and no speed bound. |
| `Posit.KernelPath.toFixedInt_eq_kernel`, `toUnsigned_eq_kernel`, `toFixedInt_toNatBits`, `toUnsigned_toNat` | Posit Standard (2022), §6.4: the conversions of a posit to a signed and to an unsigned integer are the words that `Posit.KernelPath.Flat.toSigned` and `Flat.toUnsigned` compute on the encoding, for every standard width, every positive integer width and every word. The first two are `@[kernel_optimize]` rules. |
| `Posit.KernelPath.quireAccumulate_eq`, `quireAddPosit_eq`, `quireAddProduct_eq`, `quireAddQuire_eq`, `quireNeg_eq`, `quireAbs_eq`, `quireRound_eq` and the rules `qAddP_eq_kernel`, `qSubP_eq_kernel`, `pToQ_eq_kernel`, `qMulAdd_eq_kernel`, `qMulSub_eq_kernel`, `qAddQ_eq_kernel`, `qSubQ_eq_kernel`, `qNegate_eq_kernel`, `qAbs_eq_kernel`, `qToP_eq_kernel` | Posit Standard (2022), §§3.3, 5.11 and 6.2: the quire operations of `Posit.KernelPath.Quire` on the natural-number word of a quire (accumulating a posit, an exact product or a quire, negation, absolute value, and the rounding to a posit) return the word of the specified result, for every standard width, every quire and every operand, with the quire NaR for a sum outside the quire range. |
| `Posit.General.value`, `value_eq_fields`, `pos_code`, `value_strictMono`, `pos_lt_pos_iff`, `roundTail_nearest`, `encode_nearest`, `encode_range`, `encode_value`, `encode_of_le_value_one`, `encode_of_value_max_le`, `encode_between`, `mul_of_eq_value`, `toRat?_eq_value` | FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`: for every number `es` of exponent bits and every number `p` of payload bits, the value of a positive magnitude code is `significand * 2 ^ (exponent - bias)` of the kernel fields, codes are ordered as their values, and `KernelPath.encode` rounds a positive dyadic number by the rule of §4.1 with `2 ^ es` in place of `4` (exact values returned, saturation at the least and the greatest code, and otherwise the code whose two neighbouring midpoints of the format with one more bit enclose the input, even at a midpoint). `toRat?_eq_value` identifies `es = 2` with the standard model. |
| `Posit.General.toRat?`, `IsRounded`, `IsRounded.unique`, `IsRoundedTo`, `IsRoundedTo.unique`, `exists_isRoundedTo`, `encode_isRounded`, `add_isRoundedTo`, `sub_isRoundedTo`, `mul_isRoundedTo`, `fma_isRoundedTo`, `div_isRoundedTo`, `ofRatio_isRoundedTo`, `IsRoundedSqrt`, `sqrt_isRoundedSqrt`, `cast_isRoundedTo`, `toRat?_neg`, `toRat?_abs`, `lt_iff`, `le_iff`, `signedKey_next`, `signedKey_prior`, `toSigned_of_lt`, `toSigned_of_gt`, `toUnsigned_of_lt`, `toUnsigned_of_gt`, `sameSide_jam`, `value_succ_even`, `toRat?_toNatBits`, `roundRat_isRoundedTo` | Every operation of `Posit.KernelPath.Core` for every number `es` of exponent bits, every number `p ≥ 1` of payload bits and all operands, zero, NaR and both signs included, against a specification on values. `toRat?` is the value of an encoding. `IsRounded p es x c` is the rule of §4.1 for a positive rational, stated with the values of the format with one more payload bit, and `IsRoundedTo` its signed form: at most one encoding satisfies it, and every rational has one. `add`, `sub`, `mul`, `fma` and `div` return the rounding of the exact result of the values (NaR for a NaR operand and for a zero divisor), `ofRatio` the rounding of `± num / den` (a literal, an integer), `sqrt` the rounding of the square root, stated on squares (NaR for a negative operand), `cast` the rounding in a format with other numbers of payload and exponent bits, `neg` and `abs` the exact negation and absolute value, `lt` and `le` the comparison of the values with NaR least, `next` and `prior` the successor and the predecessor in that order, and `toSigned` and `toUnsigned` the nearest integer of the value, ties to even, in `w` bits, with the word that has only its most significant bit set outside the range. A quotient or a root is rounded from at least `p + 1` bits with the remainder in the low bit: `sameSide_jam` and `value_succ_even` prove that no rounding boundary separates it from the exact number. At `es = 2` the specification is the standard's model: `toRat?_toNatBits`, `roundRat_isRoundedTo`. The quire and the elementary functions have no form for another `es`. |
| `ExecFloat.Posit.addition_eq_spec`, `subtraction_eq_spec`, `multiplication_eq_spec`, `division_eq_spec`, `sqrt_eq_spec` | Posit Standard (2022), §§5.4–5.5: each standard-named public operation equals the configured exact specification, for every valid width, invertible carrier codec and capability with `HasSpec`. The public six comparisons (§5.3) use complete signed-word order, including NaR as least; `negate` (§5.2) uses whole-word two's complement. |
| `Posit.Model.pₘToₙ_eq_append_zero`, `pₘToₙ_eq_precisionConvert`, `ExecFloat.Posit.toModel_pₘToₙ` | Posit Standard (2022), §6.1: conversion rounds the exact source value at the destination width and preserves NaR. Widening is exactly zero-bit extension, for every pair of valid widths and independent lawful carrier codecs. The compiled replacement and kernel rewrite reuse the existing widening preservation proof; narrowing uses the exact rounder. |
| `Posit.Model.toRat?_abs`, `toRat?_sign`, `ExecFloat.Posit.toRat?_abs`, `toRat?_sign` | Posit Standard (2022), §5.2: absolute value has exact rational value `abs q`, and sign has value −1, 0 or 1 according to the sign of `q`; both preserve NaR. These statements cover every standard width and every invertible storage codec. Signed-magnitude decoding proves the value claims; widening from two bits proves exact representation of the unit. |
| `ExecFloat.Posit.cast_fromIEEE`, `cast_toIEEE` | Posit Standard (2022), §6.5: generic casts reuse the exact-domain maps and proved conversion relations at independent descriptors and codecs. Incoming binary zero signs are forgotten; outgoing posit zero is positive. The binary direction is selected independently. Compiler reference certificates and kernel equations preserve the conversion result; the binary specification's independent nearest-real clause retains its existing IEEE/default-policy hypotheses. |
| `Backend.Certified.reference`, `compiled_reference%` | Posit Standard (2022), §§5.2, 5.5–5.8, 5.11, 6.3–6.4: registered operations share one reference certificate at their full function types. Their defining-equation kernel fallbacks reuse the exact model functions and their real, integer and quire correctness theorems. `qToP` retains its proved direct kernel replacement. These equality certificates assert no speed bound. |
| `OCP.MX.Standard.Element.quantizeFinite_eq_round`, `scan_eq_nearest`, `scan_eq_int8Nearest`, `bisect_spec`, `quantizeFinite_eq_scan`, `scan_eq`, `roundingKey_lt_iff`, `candidates_eq` | For all six MX profiles and every input, nearest-even element rounding is the code of the least packed entry `key * 2 ^ width + code` over the finite codes, where the key is four times the distance in units of `1 / (denominator * q)` plus the tie bits. A scan of the codes on natural numbers computes it, and a bisection does: over the magnitude fields of the five sign-magnitude profiles (the least of three entries, at the two fields that bracket the input and at the zero of the other sign) and over the magnitudes of INT8 (`scan_eq_int8Nearest`). `quantizeFinite_eq_round` is tagged `@[kernel_optimize]`, and `Element.quantize` is unfolded to reach it. `OCP.MX.Standard.elements_quantize` and `value_quantize_element` expose the element conversion in a stored element of a quantized tensor of `Standard.format` and in its value. `Element.finiteValue_decode_eq` is dequantization: the rational value of a decoded word is the signed magnitude of its code over the denominator of the profile, and `value_eq_codeValue` states the value of a position of a stored tensor with it. `Block.amax_eq_loop` computes the largest magnitude of a group of rational data indexed by `Fin n` by one loop on numerators and denominators, and `OCP.MX.Standard.scale_eq_amax` writes the scale of a block under the standard policy as the E8M0 rounding of that magnitude. |
| `KernelPath.toNat_eq`, `ofNat_eq`, `toNat_ofNat`, `ofNat_toNat` | `KernelPath.toNat` reads the encoding of a stored value and `KernelPath.ofNat` stores one, with primitive projections and constructors: they agree with the family's model conversions and invert each other on encodings in range. |
| `KernelPath.acceptsCode_eq`, `signalingCode_eq`, `KernelPath.Value.compareQuiet_eq_lift`, `compareSignaling_eq_lift`, `Configured.compareQuiet_eq`, `compareSignaling_eq` | The 22 comparisons of IEEE 754-2019 §5.11 on encodings: `Model.compareQuiet` and `Model.compareSignaling` at a predicate are that predicate at the comparison code of the two encodings (`acceptsCode`), with `invalid` exactly when an encoding is a signaling NaN (quiet) or a NaN (signaling), for every descriptor, every predicate and all operands. The members `compareQuietEqual` to `compareSignalingGreaterUnordered` of a configured type are unfolded to their family by `float_decide`. Import `Configured.Recommended.KernelPath`. |
| `KernelPath.copySign_eq_spec`, `abs_eq_spec`, `extremumOfNumbers_eq_spec`, `extremum_eq_spec`, `extremumNumber_eq_spec`, `magnitudeExtremum_eq_spec` | The sign operations of §5.5.1 and the minimum and maximum operations of §9.6 as selections between two encodings: `copySign` and `abs` flip or clear the sign bit (the zero and the NaN of an unsigned-zero format are kept), `extremum fmt larger` is the encoding of `Model.maximum` or `Model.minimum` (a NaN operand quieted, a signaling one first; `-0` below `+0`), `extremumNumber fmt larger` that of `Model.maximumNumber` or `Model.minimumNumber` (a number preferred to a NaN), and `magnitudeExtremum fmt larger flat` that of `Model.magnitudeExtremum larger base` when `flat` computes `base`. For every descriptor and all operands. |
| `Configured.liftUnary_abs_eq`, `liftBinary_copySign_eq`, `liftBinary_minimum_eq`, `liftBinary_maximum_eq`, `liftBinary_minimumNumber_eq`, `liftBinary_maximumNumber_eq`, `liftBinary_minimumMagnitude_eq`, `liftBinary_maximumMagnitude_eq`, `liftBinary_minimumMagnitudeNumber_eq`, `liftBinary_maximumMagnitudeNumber_eq`, `minimum_outcome_eq` and its seven siblings, `ofModel_outcomeWithInvalid` | The rules of `float_decide` for `abs`, `copySign` and the eight operations of §9.6 on configured values, in every storage plan: the operation is the kernel selection `KernelPath.Value.minimum` (and its siblings) between the two encodings, and with `status := true` the same value with `invalid` exactly when an encoding is a signaling NaN and the ternary value of an exact result. |
| `KernelPath.expCode_eq`, `fracCode_eq`, `normalCode_eq`, `subnormalCode_eq`, `classOf_eq`, `Configured.classify_eq`, `isNormal_eq`, `isSubnormal_eq`, `isSignaling_eq` | Classification of §5.7.2 on encodings: the exponent and fraction fields of a word, `Model.isNormal` and `Model.isSubnormal` as tests on them, and `classOf fmt x.toNatBits = Model.classify x` for the ten classes, for every descriptor and every word; the four rules rewrite `class`, `isNormal`, `isSubnormal` and `isSignaling` of a configured value. |
| `Configured.totalOrderMag_eq` | `totalOrderMag` of §5.10 on configured binary values, for every format descriptor and storage plan: in a format with signed zeros it is the total order of the two encodings with their sign bits cleared (`KernelPath.abs`, `Flat.totalOrder`), and in a format without signed zeros the rule leaves the model operation. |
| `KernelPath.scale_eq_spec`, `KernelPath.Value.scale_eq_lift`, `Configured.liftUnary_scale_eq` | `scaleB` of §5.3.3 on encodings: the significand with its implicit bit and the exponent field are read off the word, the integer `n` moves the exponent, and `KernelPath.round` rounds once in the given direction; an infinity is returned as it is and a NaN is quieted. `KernelPath.scale` computes the encoding of `Model.scale x n mode` for every format descriptor, rounding direction, integer `n` and value, and the configured `ExecFloat.Binary.scale` is rewritten to it in every storage plan. |
| `KernelPath.logB_eq_spec`, `KernelPath.roundInteger_eq`, `KernelPath.Value.logB_eq_lift`, `Configured.liftUnary_logB_eq` | `logB` of §5.3.3 on encodings: the bit length of the significand and the exponent field give the exponent of the leading bit as a difference of two natural numbers, whose magnitude `KernelPath.roundInteger` rounds to nearest-even (`roundInteger_eq`: the encoding of an integer rounded into a format in any direction, with the bit length of the integer as the bound of the rounding); a zero and an infinity give the overflow words of the format and a NaN is quieted. `KernelPath.logB` computes the encoding of `Model.logB x` for every format descriptor and value, and the configured `ExecFloat.Binary.logB` is rewritten to it in every storage plan. |
| `KernelPath.getPayload_eq_spec`, `KernelPath.Value.getPayload_eq_lift`, `Configured.liftUnary_getPayload_eq` | `getPayload` of §9.7 on encodings: for the word of a NaN, the bits under the payload mask rounded as an integer by `KernelPath.roundInteger`; for any other word, the word of `-1`. `KernelPath.getPayload` computes the encoding of `Model.getPayload x` for every format descriptor and value, and the configured `ExecFloat.Binary.getPayload` is rewritten to it in every storage plan. |
| `Numerics.Kernel.log2_eq` | `Kernel.log2 n = Nat.log2 n` for every natural number: the position of the leading bit read off the bit length `Kernel.size n`. Lean's kernel evaluates `Nat.log2` by its recursion, one step for each bit, and `Kernel.size` in a few native operations, so a kernel form uses `Kernel.log2` wherever its reference uses `Nat.log2`. |
| `KernelPath.toDyadic?_eq_decode`, `toDyadic?_eq`, `exactValue_eq`, `roundDyadic_eq`, `addExact_eq`, `subExact_eq`, `mulExact_eq` | Exact values of encodings: `decode fmt x.toNatBits` is the dyadic that a finite `x` decodes to and `exactValue fmt x.toNatBits = Model.exactValue x` for every word, `roundDyadic fmt mode d` is the encoding of `Model.Internal.Directed.roundDyadic fmt mode d` for every descriptor, direction and dyadic, and `addExact`, `subExact` and `mulExact` are `Numerics.Dyadic.add`, `sub` and `mul` with the alignment and the signed sum on natural numbers. An operation that decodes, computes exactly and rounds once has a kernel form with the same middle step. |
| `KernelPath.nextUp_eq_spec`, `nextDown_eq_spec`, `KernelPath.Value.nextUp_eq_lift`, `nextDown_eq_lift`, `Configured.liftUnary_nextUp_eq`, `liftUnary_nextDown_eq`, `nextUp_outcome_eq`, `nextDown_outcome_eq` | `nextUp` and `nextDown` of §5.3.1 on encodings: a NaN is quieted, an infinity at the end of the range and the largest finite value of a format without infinities stay, a zero gives the least subnormal of the right sign, and every other word moves by one modulo `2 ^ bitWidth`. `KernelPath.nextUp fmt x.toNatBits = (Model.nextUp x).toNatBits` for every descriptor and value, the configured operations are rewritten to them in every storage plan, and with `status := true` the same value with `invalid` exactly when the encoding is a signaling NaN. `copy` is unfolded to its operand. |
| `KernelPath.remainder_eq_spec`, `remainder_status_eq`, `exactValue_cases`, `Configured.liftBinary_remainder_eq`, `remainder_outcome_eq` | `remainder` of §5.3.1 on encodings: two finite words with a nonzero divisor are decoded, the exact remainder of the reference is formed and `roundDyadic` encodes it. `KernelPath.remainder fmt x.toNatBits y.toNatBits = (Model.remainder x y).toNatBits` for every descriptor and all operands, and the configured `ExecFloat.Binary.remainder` is rewritten to it in every storage plan. With `status := true` the outcome is the same value with the `invalid` flag that `remainderInvalid` computes on the two encodings: a signaling NaN, or without a NaN an infinite dividend or a zero divisor. |
| `KernelPath.admissiblePayload?_eq`, `setPayload_eq_spec`, `setPayloadSignaling_eq_spec`, `Configured.liftUnary_setPayload_eq`, `liftUnary_setPayloadSignaling_eq` | `setPayload` and `setPayloadSignaling` of §9.7 on encodings: whether the operand is a nonnegative integer below the payload bound is read off its exact value, and the word of the quiet or signaling NaN is built from it. Both kernel forms compute the encoding of the reference for every descriptor and value, and the configured operations are rewritten to them in every storage plan. |
| `KernelPath.convertToIntegerExact_eq_spec`, `inRangeCode_eq`, `Configured.convertToIntegerExact_eq`, `Configured.convertFromInt_eq`, `KernelPath.Value.ofInteger_eq_lift`, `KernelPath.toInt_ofInt_eq` | The conversions of §5.4.1 between a binary format and a fixed-width integer, on the descriptor model: `ExecDType.convertToIntegerExact` on a decoded configured value is the kernel conversion on its encoding (the rounded integer by `Flat.intMagnitude`, the range test by `inRangeCode`, the inexact signal off the exact value), for every width, signedness and rounding direction, and `ExecDType.convertFromInt` stored in a configured format is the kernel rounding of the integer. The members `convertToInteger…` and `convertToIntegerExact…` are unfolded to these. Import `DType.KernelPath`. |
| `KernelPath.formatOfAddition_eq_spec`, `formatOfSubtraction_eq_spec`, `formatOfMultiplication_eq_spec`, `formatOfDivision_eq_spec`, `formatOfFusedMultiplyAdd_eq_spec`, `roundRatio_eq`, `deliverFinite_eq`, `Configured.formatOfAddition_eq` and its four siblings | The formatOf operations of §5.4.1 on encodings: finite operands of any formats are decoded, the exact sum, difference, product or fused product and sum is formed and `roundDyadic` rounds it once into the destination, and the quotient is rounded as a scaled ratio (`roundRatio`); an operand that is not finite goes to the reference. Each kernel form computes the encoding of the value of the reference for all source and destination descriptors, every direction and all operands, and the value of the model operation on decoded configured values, stored in a configured format, is rewritten to it. |
| `KernelPath.augmentedWords_eq`, `gridTiesTowardZero_eq`, `magnitudeOverflows_eq`, `augmentedAddition_eq_spec`, `augmentedSubtraction_eq_spec`, `augmentedMultiplication_eq_spec`, `KernelPath.Value.augmented_eq`, `Configured.augmentedAddition_eq`, `augmentedSubtraction_eq`, `augmentedMultiplication_eq` | The augmented operations of §9.5 on encodings: two finite words are decoded, the exact sum or product is rounded to nearest with ties toward zero on the grid of the format (`gridTiesTowardZero`, the reference `Model.tiesTowardZeroGrid` with shifts and one comparison of natural numbers), the overflow is decided by a comparison with the largest finite value (`magnitudeOverflows`), and the head, the tail and the flags of the reference are delivered with the head and the tail as encodings. For every descriptor and all operands; the configured operations are rewritten in every storage plan, and `toNat_head_augmented`, `toNat_tail_augmented` and `status_augmented` read the three parts. |
| `KernelPath.sum_eq_spec`, `sumAbs_eq_spec`, `sumSquare_eq_spec`, `dot_eq_spec`, `pushWord_eq`, `pushProductWord_eq`, `finishWord_eq`, `Configured.sum_eq`, `sumAbs_eq`, `sumSquare_eq`, `dot_eq` | The exact reductions of §9.4 on lists of encodings: the state of the reference (an exact dyadic sum, or the special value that decides the result) is updated by each word with `decode` and `addExact`, and the final sum is rounded once by `roundDyadic`. Each kernel form computes the encoding of the reference result for all source and destination descriptors, every direction and every list, and the configured reductions are rewritten to them. |
| `KernelPath.scaledProd_eq_spec`, `scaledProdOfSums_eq_spec`, `factor_eq`, `factorSum_eq`, `finishProduct_eq`, `Configured.scaledProd_eq`, `scaledProdSum_eq`, `scaledProdDiff_eq` | The scaled products of §9.4 on lists of encodings: the exact factors of the words, or of the sums or differences of two words, are multiplied and the product is rounded once with its scale factor. For all descriptors, every direction and every list, with the errors of the reference. |
| `KernelPath.toNatBits_reduceInOrder`, `toNatBits_reduceAlong`, `foldAdd_eq`, `evalWord_eq` | The reductions of §9.4 that round at each addition (`Model.reduceInOrder` from left to right and `Model.reduceAlong` over an association tree): the encoding of the result is a fold of the kernel addition over the encodings of the terms, for every accumulator and destination descriptor. Import `Reduction.Schedule.KernelPath`. |
| `KernelPath.pown_eq_spec`, `powRatio_eq`, `ofRatio_eq_roundRat`, `Configured.liftUnary_pown_eq` | `pown` of §9.2 on encodings: a finite nonzero word is decoded and `ofRatio` rounds the quotient of the power of its significand and a power of two, or its reciprocal for a negative exponent, with the sign of an odd power of a negative value. `KernelPath.pown fmt n x.toNatBits = (Model.pown x n).toNatBits` for every descriptor, value and integer exponent, and the configured `ExecFloat.Binary.pown` is rewritten to it in every storage plan. |
| `KernelPath.rootn_eq_spec`, `rSqrt_eq_spec`, `rootRatio_eq`, `rootOf_eq`, `roundCertificate_eq_roundDyadic`, `roundWithAccuracy_eq_round`, `floorRoot_eq`, `rootQuarter_eq`, `Configured.liftUnary_rootn_eq`, `liftUnary_rSqrt_eq` | `rootn` and `rSqrt` of §9.2 on encodings: a finite nonzero word is decoded, the fraction of its magnitude or of the reciprocal is reduced by one greatest common divisor, and `rootRatio` rounds its root: the binade from the binary logarithm of the fraction, the integer root two bits below the rounding position by a Newton iteration whose result is checked (`floorRoot`), the place of the root between that integer and the next as two more bits (`rootQuarter`), and one `KernelPath.roundDyadic`. `roundCertificate_eq_roundDyadic` proves the rounding of a certificate of `AlgebraicRounding` equal to the reference rounding of the dyadic with those two bits whenever the integer has the bits of a significand, for every format descriptor (`roundWithAccuracy_eq_round` is the statement on Lean's model of IEEE arithmetic). `KernelPath.rootn fmt n` and `KernelPath.rSqrt fmt` compute the encodings of `Model.rootn x n` and `Model.rSqrt x` for every format descriptor, every value and every integer degree, with a zero, an infinity, a NaN, the degree zero, a root that does not exist, a root at the ends of the exponent range and a subnormal root delivered by the reference, and the configured `ExecFloat.Binary.rootn` and `rSqrt` are rewritten to them in every storage plan. |
| `KernelPath.hypot_eq_spec`, `sqrtDyadic_eq`, `sqrtTarget_eq`, `sqrtQuarter_eq`, `Configured.liftBinary_hypot_eq` | `hypot` of §9.2 on encodings: two finite words are decoded, the exact sum of their squares is formed on natural numbers (`KernelPath.mulExact`, `KernelPath.addExact`), and `sqrtDyadic` rounds its square root as Lean's model of IEEE arithmetic takes it: the checked integer square root of the significand shifted to the exponent `sqrtTarget`, the remainder as two more bits (`sqrtQuarter`), and one `KernelPath.roundDyadic`, by `roundCertificate_eq_roundDyadic`. `KernelPath.hypot fmt x.toNatBits y.toNatBits = (Model.hypot x y).toNatBits` for every format descriptor and every pair of values, with a NaN, an infinity, two zeros, a root with fewer bits than a significand and a format that is not an IEEE layout delivered by the reference, and the configured `ExecFloat.Binary.hypot` is rewritten to it in every storage plan. |
| `KernelPath.ofList_formatCharacters`, `parseCharacters_eq`, `decimalWord_eq`, `shortestDecimal_eq`, `digitCount_eq`, `Configured.format_eq`, `Configured.parse_eq`, `Numerics.Kernel.Text.naturalDigits_eq`, `digitChar_eq`, `decimalCharacters_eq`, `fixedCharacters_eq`, `scientificCharacters_eq`, `hexCharacters_eq`, `compact_eq`, `decimalDigit_eq`, `hexDigit_eq`, `parseDecimal_eq`, `parseHex_eq`, `ofList_eq_iff` | The conversions to and from character sequences of §5.12 on encodings and lists of characters: `String.ofList (formatCharacters fmt style mode x.toNatBits) = Model.format x style mode` for every descriptor, style and direction, and `parseCharacters fmt mode text.toList` is the encoding of the value that `Model.parse fmt text mode` reads, with its errors. A decimal record is rounded on encodings (`decimalWord`), the shortest search and the compact record take their loop bounds from `Kernel.log2`, the digits are written by a loop on the bit length of the number and read off the character codes (`Numerics.Kernel.Text`), and with `String.length_ofList`, `String.toList_ofList` and `ofList_eq_iff` a text that `float_decide` computes stays a list of characters. Import `Configured.Text.KernelPath`. |

`float_decide` rewrites with these equations (the rules tagged `@[kernel_optimize]`, the cheapest
matching rule first) and then asks the kernel to decide the statement. The proofs it builds depend on `propext`, `Classical.choice` and
`Quot.sound` only. `#kernel_eval t` (`FloatLib.Tactic.KernelEval`) prints the value and the time
of a kernel evaluation, `#kernel_cost t` (`FloatLib.Tactic.KernelCost`) the time of a term as
written and after the rewrite, and `#kernel_rules` (`FloatLib.Tactic.KernelRules`) the registered
rules with their declared costs.

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
| `ExecFloat.Binary.toModel_ofFloat_convertFromInt`, `toModel_ofFloat32_convertFromInt32` | Unbounded `Int` casts agree with FloatLib's dyadic rounder, including negative values and overflow. |
| `ExecFloat.Binary.toModel_ofFloat32_int64ToFloat32`, `toModel_ofFloat_int64ToFloat` | Signed integer casts agree with FloatLib's nearest-even integer conversion. The other native signed widths have corresponding lemmas. |
| `ExecFloat.Binary.float32ToInt8_eq_convertToIntegerExactSaturating`, `convertToIntegerExact8_eq_convertToIntegerExactSaturating` | Native signed casts truncate toward zero and saturate; NaN maps to zero. The other signed widths have corresponding lemmas. |
| `ExecFloat.Binary.ofFloat32_add_of_isFinite`, `ofFloat_add_of_isFinite` | On finite operands, importing a native sum equals adding the imports, including signed zeros and overflow. Corresponding subtraction, multiplication, and division lemmas have the same scope. |
| `Model.canonicalizeModel_sqrt_eq_model` | For every conventional IEEE input, square root agrees with Lean's model after NaN canonicalization. |
| `ExecFloat.Binary.toFloat32_sqrt`, `toFloat_sqrt` | Configured square root commutes with native export on every input. |

Here the `Model` names belong to `Formats.BinaryInterchange.Model`. These are equalities with Lean's
logical definitions. Executing a native call also trusts the compiler, runtime, and hardware, while
our software operations keep their existing refinement certificates.

### Native binary16 and bfloat16 carriers

Import `FloatLib.Floats.Formats.IEEE754.Native.Half`, also exported by `IEEE754` and `FloatLib`.
`FloatLib.Floats.Native.Carrier format` shares one representation and instance family across
16-bit layouts; `Half` and `BFloat16` specialize it with their widths and quiet NaN words. A
`Native.Format` has five to eight exponent bits (binary32 contains its range and has `2p + 2`
significand bits), a designated NaN word that is a NaN word, and a widening function that is the
reference cast to binary32 on every word a carrier holds.

| Theorem | Informal statement |
| --- | --- |
| `Native.Carrier.ofBits_toBits` | Every carrier value is recovered by normalizing its interchange word. |
| `Native.Carrier.toBits_ofBits` | A word whose magnitude does not exceed the format's infinity word is preserved. |
| `Native.Carrier.toBits_ofBits_nan` | The designated NaN word is preserved. |
| `Native.Format.infinity_lt_nan`, `Native.Carrier.isNaNWord_ofBits_iff` | The designated NaN word is a NaN word of the layout, so normalization keeps the class of every word: a NaN word becomes a NaN word and every other word is kept. |
| `Native.Carrier.val_eq_spec` | For every 16-bit carrier layout, widening a carrier value is the binary32 word of the nearest-even reference cast of its word. |
| `Native.Word.widenHalfWord_eq_cast`, `Native.Word.shiftLeft_eq_cast` | The two widening functions, binary16's field arithmetic and bfloat16's shift into the high half, are the reference cast to binary32 on every word that is not a NaN and on the format's quiet NaN. Lean's kernel checks all 65,536 words of each. |
| `Native.Word.roundWord_eq_spec` | For every source and destination descriptor, word rounding is the nearest-even `Model.cast`, stored in UInt64. |
| `Native.Word.roundWord_toNat` | If the destination width is at most 64 bits, the stored result is exactly the model encoding, without truncation. |
| `Native.Carrier.ofWord_eq_spec` | For every 16-bit carrier layout and source descriptor, conversion is the reference cast followed by the carrier's NaN normalization. |
| `Native.Carrier.ofFloat32_eq_spec`, `ofFloat_eq_spec` | Conversion of every binary32 or binary64 interchange word is the reference cast followed by normalization. Binary64 rounds directly. |

The normalization and host-word conversion theorems for `Native.Half` and `Native.BFloat16`
are generated corollaries of the common family. The word rounder uses the proved kernel cast;
its descriptor arguments include the widths, bias and exceptional-value encoding.
The host IEEE binary32 arithmetic and the Figueroa double-rounding argument remain outside these
proofs. Native addition, subtraction, multiplication, division, square root, negation and the
comparisons are checked against the software models on random words, and the four arithmetic
operations on every pair of bfloat16 words of the two lowest exponent fields; native
transcendentals have no correctly-rounded guarantee. The remaining unchecked paths are recorded
in the execution backends' README.

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
reduction, the `log 2` of exponential reduction and of generated configurations, the `log 2` of
the certified power, and the `log 2` of the correctly rounded logarithm and weighted exponential
searches. Each precision level of the cache is computed once, on first use, and these
readers share it from then on. The exact comparators and the certified logarithm are the
exception, since they compute their own `pi / 4` and `log 2`.

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
`expm1`, and `logp1` refine proved rational enclosures until both endpoints round to the same
finite encoding. Stable variants perform the subtraction or addition of one exactly before rounding.
They return `.ok result` on success, and otherwise `.error (failure : Certified.Failure)`: an
unsupported format, a nonfinite input, a domain or range failure, or an inconclusive search.
Certification never falls back to an approximation. The theorems below are partial correctness.
They describe every `.ok` result, but no theorem says which inputs succeed in general. The proved
successes are the signed-zero passthrough `Model.Transcendentals.Certified.expm1_of_isZero` and
`logp1_of_isZero`, and the power of one, `Model.Transcendentals.Certified.pow_posOne`. You set the starting degree and the number of enclosure attempts with the
`budget` option, a `Certified.Budget`, which bounds the attempts and not the total work. On the
model,
`Model.Transcendentals.Certified.pow` (finite floating inputs) and `powRat` (exact rationals) refine
enclosures of `exp (y * log x)` for a positive base in the same way.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.Certified.map_toModel_exp`, `map_toModel_log`, `map_toModel_pow`, `map_toModel_expm1`, `map_toModel_logp1` | Decoding preserves the certified model kernel's result or failure. |
| `ExecFloat.Binary.Certified.isFinite_of_exp_eq_ok`, `isFinite_of_log_eq_ok`, `isFinite_of_pow_eq_ok` | Every certified result is finite. |
| `ExecFloat.Binary.Certified.toReal_of_exp_eq_ok`, `toReal_of_log_eq_ok`, `toReal_of_pow_eq_ok` | A certified result equals nearest-even real rounding of the exact exponential, logarithm, or power. |
| `ExecFloat.Binary.Certified.toReal_of_expm1_eq_ok`, `toReal_of_logp1_eq_ok` | A certified result is one nearest-even rounding of `Real.exp x - 1` or `Real.log (1 + x)`, without first rounding the exponential or the sum. |
| `ExecFloat.Binary.toModel_pow` | The plain configured `pow` decodes to `Model.pow`. |
| `Model.Transcendentals.Certified.isFinite_of_powRat_eq_ok`, `toReal_of_powRat_eq_ok`, `base_pos_of_powRat_eq_ok` | A power of exact rationals accepted by `powRat` is finite and equals nearest-even rounding of the real power `base ^ exponent`; only positive bases are accepted. |
| `Model.Transcendentals.Certified.isFinite_of_pow_eq_ok`, `toReal_of_pow_eq_ok` | The same for finite floating inputs decoded exactly, including bases and results far outside binary64's exponent range. |
| `Model.Power.pow_spec_of_certified` | For a finite positive base and a finite exponent that is not an integer, `Model.pow` is finite and correctly rounded whenever `Certified.pow` settles within the budget `Model.Power.certifiedBudget`. |

The optional `FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded` import adds
total `ExecFloat.Binary.CorrectlyRounded.exp`, `log`, `expm1`, `logp1`, and `expMul`,
which rounds `exp x * w` once. Each returns the result of the enclosure search when it settles and
otherwise decides the rounding by exact comparisons, so the theorems have no premise on the
budget. The model functions and these theorems are in `Model.Transcendentals.CorrectlyRounded`.
Apart from the agreement with the certified search, the theorems need an IEEE descriptor and a
finite input in the domain.

| Theorem | Informal statement |
| --- | --- |
| `toReal_exp_eq_roundAt`, `toReal_log_eq_roundAt`, `toReal_expm1_eq_roundAt`, `toReal_logp1_eq_roundAt`, `toReal_expMul_eq_roundAt` | When the exact result, in absolute value for `log`, `logp1`, and `expMul`, lies below `Certified.overflowThreshold`, the result is its nearest-even rounding. |
| `toReal_exp_of_isFinite` and its siblings | Every finite result is the nearest-even rounding of the exact result. |
| `isFinite_exp_iff` and its siblings | The result is finite exactly when the exact result, in absolute value for `log`, `logp1`, and `expMul`, is below the overflow threshold. |
| `abs_toReal_exp_sub_le` and its siblings | Under the range premise of `toReal_exp_eq_roundAt` and its siblings, the result has relative error `unitRoundoffAt fmt` and absolute error `underflowErrorAt fmt`. |
| `exp_eq_nativeOverflow` and its siblings | When the exact result is at or above the overflow threshold in absolute value, the result is the infinity with its sign. |
| `toReal_pos_of_isFinite_log`, `neg_one_lt_toReal_of_isFinite_logp1` | A finite logarithm or `logp1` of a finite input comes from an input in the domain. |
| `toReal_exp_pos`, `toReal_expm1_lt_zero`, `toReal_expm1_pos`, `toReal_logp1_pos`, `isFinite_exp_of_nonpos`, `isFinite_expm1_of_nonpos`, `isFinite_logp1_of_nonneg` | The exponential is positive when its exact result exceeds `underflowErrorAt fmt` and is below the overflow threshold. `expm1` of a negative input is negative, and of a positive input is positive when its exact result is below the overflow threshold. The exponential and `expm1` of a nonpositive input are finite. `logp1` of a nonnegative input is finite, and of a positive input is positive. |
| `toReal_expMul_nonneg`, `toReal_expMul_nonpos`, `toReal_expMul_pos`, `toReal_expMul_lt_zero` | The weighted exponential is nonnegative for a nonnegative weight and nonpositive for a nonpositive one. It has the strict sign of its exact result when the magnitude of that result exceeds `underflowErrorAt fmt` and is below the overflow threshold. |
| `exp_eq_of_certified_exp_eq_ok`, `expm1_eq_of_certified_expm1_eq_ok`, `log_eq_of_certified_log_eq_ok`, `logp1_eq_of_certified_logp1_eq_ok` | Whenever the certified search returns a result, the total function returns the same encoding. |
| `ExecFloat.Binary.CorrectlyRounded.toModel_exp` and its siblings | The configured functions decode to the model functions, and they carry `isFinite_exp`, `toReal_exp_eq_roundAt`, `isFinite_exp_iff`, `abs_toReal_exp_sub_le`, the sign and domain theorems, and their siblings. `toModel_exp_eq_nativeOverflow` and its siblings state the overflow results. At a zero the exponential is exactly one and `expm1` and `logp1` return the zero, all finite: `toReal_exp_of_isZero`, `toReal_expm1_of_isZero`, `toReal_logp1_of_isZero` and their `isFinite` siblings. |

`ExactExpression` and `roundOnce` round once when the expression is exact in their chosen domain. A
rational domain cannot represent `log`, `sin`, or `tanh` in general, so composing the current
transcendental kernels approximates and rounds at each function boundary. Correctly rounding a whole
transcendental composition needs a certified real enclosure or another exact-real procedure.
Treating the expression as rational arithmetic can't give you that.

### The recommended functions of IEEE 754-2019 clause 9.2

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded` for configured
values, or `Transcendentals.Recommended.Proof` for the descriptor model. The functions are
`exp2`, `exp2m1`, `exp10`, `exp10m1`, `log2`, `log10`, `log2p1`, `log10p1`, `sin`, `cos`, `tan`,
`sinPi`, `cosPi`, `tanPi`, `asin`, `acos`, `atan`, `asinPi`, `acosPi`, `atanPi`, `sinh`, `cosh`,
`tanh`, `asinh`, `acosh`, `atanh`, `atan2`, `atan2Pi`, `powr`, `pow` and `compound`, in the
namespace `CorrectlyRounded` of `Model.Transcendentals` and of `ExecFloat.Binary`. The names are
those of ISO/IEC 9899:2024 (C23, N3220) Table F.2 for the operations that IEEE 754-2019 §9.2
recommends, and the special cases those of F.10.1 to F.10.4 of that document and, for `pow`,
of IEEE 754-2019 §9.2.1. `Model.Transcendentals.Directed` (import
`Transcendentals.Directed.Proof`) has `exp`, `expm1`, `log` and `logp1` in the same form, and
`Model.Algebraic.Directed` (import `Algebraic.Directed.Proof`) has `rSqrt`, `hypot`, `rootn`,
`cbrt` and `pown`, so every function of §9.2 has a form that returns the value with its
exception flags in the rounding direction `mode` (nearest-even by default). A finite operand is
decoded exactly and the real result is rounded once from an exact comparator of
`Numerics.Exact`, with no budget. To nearest-even a transcendental function first tries an
enclosure of `Numerics.Interval` on a binary grid a little finer than the format, and takes its
rounding when both ends of the enclosure agree; the comparator then only decides what the
enclosure leaves open, and rounds the operands whose enclosures do not settle. The other
directions locate the magnitude on the grid of the format by the same comparisons and round it
from its guard and sticky bits.

In every direction the result meets the contract `Model.RoundsTo fmt mode target`: it is finite
and denotes `roundAt fmt target mode`, the rounding of the real value on the grid of the format
with an unbounded exponent range, when that value is at most the largest finite magnitude; it
is the overflow result of the direction otherwise; and in a format with signed zeros it has the
sign of the real value. The contract is proved for every format descriptor: the conventional
IEEE descriptors (binary16 to binary256, OCP E5M2), the formats without an infinity such as OCP
E4M3, whose overflow result is their NaN when the direction rounds away from zero and their
largest finite value otherwise, the formats with one zero such as ONNX E4M3FNUZ and E5M2FNUZ,
and the formats in which every encoding is finite. The 26 functions of one
argument are the members of one enumeration, `Function`, and one theorem covers them. The
equations with `roundAt` and the enclosures below are the statements for a conventional IEEE
descriptor to nearest-even and in the two directed directions.

| Theorem | Informal statement |
| --- | --- |
| `Model.ComparisonRounding.toReal_round` | For a conventional IEEE descriptor and a comparator that orders a real number against every rational, the rounding built from the comparator alone delivers `roundAt fmt` of that number whenever its result is finite. |
| `Model.ComparisonRounding.deliver_inexact_iff`, `deliver_overflow_of_isFinite_eq_false` | The flags computed from the comparator, in every direction: `inexact` exactly when a finite delivery is not the real number, and `overflow` for a delivery that is not finite. |
| `Model.ComparisonRounding.outcome_overflow_iff`, `deliver_overflow_iff`, `Rule.deliver_overflow_iff`, `unary_overflow_iff`, `binary_overflow_iff`, `roundsBeyond_iff` | **The overflow flag is the overflow of IEEE 754-2019 §7.4.** For every format descriptor and rounding direction, a delivery for the nonzero real number `r` raises `overflow` exactly when `roundAt fmt r mode`, the rounding with an unbounded exponent range, exceeds the largest finite value in magnitude: whether the delivery is an infinity, the NaN of a format without one, or the largest finite value. The same holds through a rule and through the operand tables. |
| `Model.AlgebraicRounding.posMaxFinite_lt_abs_roundAt_iff`, `posMaxFinite_lt_roundAt_iff`, `Overflows` | Where the rounding of a real number overflows: `roundAt fmt (±t) mode` exceeds the largest finite value in magnitude exactly when `t` is past the boundary of the rule that the direction applies to that sign. The boundary is the first value of the grid beyond the largest finite one for a truncation, the largest finite value itself for a rounding up, and their midpoint to nearest, where a tie overflows with ties away from zero and, with ties to even, when the largest finite significand is odd. |
| `Model.ComparisonRounding.outcome_underflow_iff`, `deliver_underflow_iff`, `Rule.deliver_underflow_iff`, `unary_underflow_iff`, `binary_underflow_iff`, `roundsTiny_iff` | **The underflow flag is the underflow of IEEE 754-2019 §7.5, with tininess detected after rounding.** For every format descriptor and rounding direction, a delivery for the nonzero real number `r` raises `underflow` exactly when it raises `inexact` and `|r|` is tiny after rounding in the direction (`AlgebraicRounding.TinyAfterRounding`): below the least normal magnitude when the direction truncates the magnitude, at most `underflowPredecessor` when it rounds the magnitude up, and below `underflowMidpoint` to nearest. These are the boundaries of the tininess of the arithmetic operations (`dyadicIsTinyAfterRounding_eq_true_iff`). The same holds through a rule and through the operand tables, for a format with one zero, and for a result beyond the range, which is never tiny. |
| `Model.AlgebraicRounding.abs_roundAt_lt_minNormal_iff`, `roundAt_lt_minNormal_iff`, `abs_roundAt_eq_minNormal`, `RoundsBelowNormal`, `TinyAfterRounding.of_roundsBelowNormal`, `TinyAfterRounding.lt_minNormal` | Where the rounding of a real number stays below the least normal magnitude: `roundAt fmt (±t) mode` is below it in magnitude exactly when `t` is before the boundary of the rule that the direction applies to that sign (the least normal magnitude for a truncation, the largest subnormal number for a rounding up, and their midpoint to nearest, where a tie goes to the least normal magnitude), and a smaller magnitude that is not before the boundary rounds to the least normal magnitude. A magnitude that rounds below the least normal magnitude is tiny after rounding, and a tiny magnitude is below the least normal magnitude. |
| `Model.RoundsTo.eq_maxFinite`, `RoundsTo.signBit_of_toReal_ne_zero` | A finite value that is the rounding of a number beyond the range is the largest finite value of the sign, and a finite nonzero value that is the rounding of a nonzero number has the sign bit of that number, in every format. |
| `Model.ComparisonRounding.outcome_invalid_divideByZero`, `Rule.deliver_invalid_divideByZero`, `unary_invalid_divideByZero`, `binary_invalid_divideByZero` | A rounding by comparisons raises neither `invalid` nor `divideByZero`: at finite operands whose rule locates a real number, a function given by a table of rules leaves both flags clear, in every direction and for every format descriptor. |
| `Model.ComparisonRounding.toReal_unary`, `toReal_binary`, `Rule.toReal_deliver`, `Rule.deliver_inexact_iff` | A function given by a table of rules rounds once: at finite operands whose rule locates a real number, a finite result is `roundAt fmt` of it, with any hint that is right about that number. |
| `Model.ComparisonRounding.toReal_deliver`, `deliver_inexact_iff`, `outcome_inexact_iff`, `resolve_ternary`, `resolve_none`, `Hint.sound_none` | A delivery may take its nearest-even value from a hint. For a hint that is right about the located number (`Hint.Sound`: its value is finite and is `roundAt fmt` of the number, and an ordering it states is the ordering of the value and the number), a finite delivery is `roundAt fmt` of the number and `inexact` is raised exactly when the delivery is not the number. The hint without a result is right about every number. |
| `Model.ComparisonRounding.toEReal_round_down_le`, `le_toEReal_round_up` | For a conventional IEEE descriptor and a comparator of a real number, the rounding toward negative infinity is at most that number and the rounding toward positive infinity at least that number, in the extended reals (infinite results included). |
| `Model.ComparisonRounding.representative_toward_le`, `le_representative_away`, `representative_of_le` | The dyadic number that is rounded in a directed mode is on the side of the located number that the direction rounds to: at most its magnitude toward zero, at least its magnitude away from zero below `2 ^ (emax + 1)`, and that power itself from there on. |
| `Model.ComparisonRounding.Rule.deliver_encloses`, `unary_encloses`, `binary_encloses` | The two enclosures through a rule and through the operand tables: at finite operands whose rule locates a real number, the result toward negative infinity is at most it and the result toward positive infinity at least it. |
| `Model.AlgebraicRounding.powerBounds_compare`, `round_eq` | For an exact comparator, a comparison with a power of two that is read off `powerBounds` is the comparator's own answer, so `round` is the rounding that compares with `2 ^ lowerExponent` and `2 ^ upperExponent` directly. `powerBounds` compares with `1`, `2 ^ ±1`, `2 ^ ±2`, `2 ^ ±4`, … only, so those two powers are not built for a result of moderate size. |
| `Model.Transcendentals.CorrectlyRounded.Function.locates` | In its domain every one of the 26 functions is located by its rule: an exact zero where the function is zero, and otherwise an exact comparator of `Function.real`. |
| `Model.Transcendentals.CorrectlyRounded.Function.eval_expr`, `eval_powerExpr`, `eval_logarithmExpr`, `eval_piExpr` | In its domain the expression `Function.expr function q` of `Numerics.Interval` denotes `Function.real function q`: `2 ^ q` is `exp (q * log 2)`, the logarithms are quotients of natural logarithms, π is `4 * arctan 1`, and the inverse hyperbolic functions are their logarithms. |
| `Model.Transcendentals.CorrectlyRounded.settle_sound`, `nearest?_sound`, `Function.hint_sound`, `angleHint_sound`, `powrHint_sound`, `compoundHint_sound` | An enclosure that settles gives the correctly rounded value: for an expression that denotes a real number, the value that `settle` accepts is finite and is `roundAt fmt` of that number, and the ordering it states is the ordering of the value and the number. So the hints of the 26 functions, of `atan2`, `atan2Pi`, `powr` and `compound` are right about their real functions. |
| `Model.Transcendentals.CorrectlyRounded.eval_angleExpr` | The expression of an angle denotes `Complex.arg` of `x + i y`, divided by π in half-turns: the arcsine of `y / sqrt (x ^ 2 + y ^ 2)` in the right half-plane, moved by π in the left one. |
| `Model.Transcendentals.CorrectlyRounded.Function.toReal_apply` | **Correct rounding of the 26 functions of one argument.** For a conventional IEEE descriptor and a finite operand whose exact value `q` is in `Function.Domain`, a finite result is `roundAt fmt (function.real q)`: `2 ^ q`, `Real.logb 2 q`, `Real.sin q`, `Real.sin (q * π)`, `Real.arcsin q / π`, `Real.artanh q` and so on. |
| `Model.Transcendentals.CorrectlyRounded.Function.inexact_apply_iff` | For a finite operand in the domain and every rounding direction, `inexact` is raised exactly when the finite result is not the value of the real function. |
| `Model.Transcendentals.CorrectlyRounded.Function.overflow_apply_iff`, `powr_overflow_iff`, `compound_overflow_iff`, `pow_overflow_iff_of_pos`, `pow_overflow_iff_of_neg`, `atan2_overflow_iff` | **The overflow flag of the recommended functions.** For every format descriptor, a finite operand in the domain with a nonzero real value and every rounding direction, `overflow` is raised exactly when the rounding of the real value with an unbounded exponent range exceeds the largest finite value in magnitude: the 26 functions of one argument, `powr`, `compound`, `pow` and the two angles. |
| `Model.Transcendentals.CorrectlyRounded.Function.underflow_apply_iff`, `powr_underflow_iff`, `compound_underflow_iff`, `pow_underflow_iff_of_pos`, `pow_underflow_iff_of_neg`, `atan2_underflow_iff` | **The underflow flag of the recommended functions.** For every format descriptor, a finite operand in the domain with a nonzero real value and every rounding direction, `underflow` is raised exactly when `inexact` is raised and the magnitude of the real value is tiny after rounding in the direction: the 26 functions of one argument, `powr`, `compound`, `pow` and the two angles. |
| `Model.Transcendentals.CorrectlyRounded.Function.invalid_divideByZero_apply` | A finite operand in the domain raises neither `invalid` nor `divideByZero`, in every direction. |
| `Model.Transcendentals.CorrectlyRounded.powr_inexact_iff`, `compound_inexact_iff`, `pow_inexact_iff_of_pos`, `pow_inexact_iff_of_neg`, `atan2_inexact_iff`, `atan2Pi_inexact_iff` | **The `inexact` flag of the functions of two arguments.** For finite operands in the domain and every rounding direction, `inexact` is raised exactly when the finite result is not the real value: `p ^ q` for `powr` and for `pow`, `(1 + q) ^ n` for `compound`, and the angle of `x + i y`, divided by π for `atan2Pi`. |
| `Model.Transcendentals.CorrectlyRounded.powr_invalid_divideByZero`, `compound_invalid_divideByZero`, `pow_invalid_divideByZero_of_pos`, `pow_invalid_divideByZero_of_neg`, `atan2_invalid_divideByZero` | For finite operands in the domain, `powr`, `compound`, `pow` and the two angles raise neither `invalid` nor `divideByZero`, in every direction. |
| `Model.Transcendentals.CorrectlyRounded.toReal_powr`, `toReal_compound` | `powr` at a finite positive base and `compound` at a finite operand above -1 are `roundAt fmt` of `p ^ q` and of `(1 + q) ^ n` whenever the result is finite. |
| `Model.Transcendentals.CorrectlyRounded.toReal_atan2`, `toReal_atan2Pi` | At finite operands with a nonzero `y`, `atan2 y x` and `atan2Pi y x` are `roundAt fmt` of the angle of `x + i y` and of that angle divided by π. |
| `Model.Transcendentals.CorrectlyRounded.Function.apply_encloses` | **The directed results of the 26 functions enclose the real function.** For a conventional IEEE descriptor and a finite operand in the domain, the result toward negative infinity is at most `function.real q` and the result toward positive infinity at least that, in the extended reals. |
| `Model.Transcendentals.CorrectlyRounded.powr_encloses`, `compound_encloses`, `atan2_encloses`, `atan2Pi_encloses` | The same enclosure for the functions of two arguments, under the hypotheses of their nearest-even theorems. |
| `Model.Transcendentals.CorrectlyRounded.locates_powr`, `locates_compound`, `locates_atan2`, `locates_atan2Pi`, `compound_eq_unary` | The rules of the four functions locate `p ^ q`, `(1 + q) ^ n` and the two angles at the operands of the theorems above. |
| `ExecFloat.Binary.CorrectlyRounded.toModel_apply`, `toReal_apply` | The configured functions decode to the model functions, and are correctly rounded under the same hypotheses. |
| `Model.ComparisonRounding.round_roundsTo`, `roundMagnitude_roundsTo`, `resolve_roundsTo`, `deliver_roundsTo`, `Rule.deliver_roundsTo`, `unary_roundsTo`, `binary_roundsTo` | **Rounding by exact comparisons is correct rounding in every direction.** For every format descriptor and a comparator that orders a nonzero real number `r` against every rational, the rounding in each of the six directions meets `RoundsTo fmt mode r`, and so does a delivery with its flags, a rule, and a function given by a table of rules at finite operands, with any hint that is right about `r` and has its sign (`Hint.Sound`, `Hint.Signed`). |
| `Model.ComparisonRounding.round_of_eq_zero`, `Rule.isZero_deliver` | A comparator of zero is rounded to `+0` in every direction, and a rule that locates zero delivers a zero. |
| `Model.AlgebraicRounding.round_roundsTo`, `roundCertificate_roundsTo`, `signBit_round` | Nearest-even rounding by comparisons meets the contract for every format descriptor: zero at or below half the least subnormal, the overflow word at or above `2 ^ (emax + 1)`, and between them the certificate of the magnitude, which a descriptor that is not IEEE rounds as a dyadic number that stands in the same place between the values of the format. |
| `Model.AlgebraicRounding.located_of_truncated`, `located_of_quarter`, `accuracyQuarter_eq_zero_iff`, `Located.roundAt_eq` | A magnitude in a binade with a truncated significand and an exactness flag is located on the grid, and so is its quarter-integer stand-in, at the same place; every direction rounds a located magnitude from its integer part, guard bit and sticky bit. |
| `Model.roundReal_roundsTo`, `AlgebraicRounding.roundMagnitude_roundsTo`, `roundLocated_roundsTo`, `packGrid_roundsTo`, `signBit_directedOverflow` | The rounding of a real number in a chosen direction meets the contract for every format descriptor, and in a format with signed zeros the overflow result has the sign it is given. |
| `Model.roundRatScaled_of_grid`, `signBit_roundRatScaled_of_grid`, `roundDyadic_spec` | Every descriptor delivers a value of its grid exactly, with its sign bit, and nearest-even rounding of a dyadic number is the grid rounding when that is in range and the overflow word of the descriptor beyond it. |
| `Flocq.round_of_guardSticky`, `round_signed_of_guardSticky`, `negRound_roundingFunction`, `inbetweenInt_of_cmp_half` | In any radix, a magnitude whose scaled significand lies in the unit bracket above `m`, at the place that a guard bit and a sticky bit name, rounds in each direction to `m` or `m + 1`, as `MagnitudeRounding.increment` decides, times the radix power of its canonical exponent. Binary and decimal formats share the statement. |
| `Model.Transcendentals.CorrectlyRounded.Function.apply_roundsTo`, `Function.isZero_apply`, `Function.hint_signed` | **The 26 functions of one argument are correctly rounded in every direction.** For every format descriptor, a finite operand in the domain with a nonzero real value and each direction `mode`, the result meets `RoundsTo fmt mode (function.real q)`; a real value of zero gives a zero. |
| `Model.Transcendentals.CorrectlyRounded.powr_roundsTo`, `compound_roundsTo`, `atan2_roundsTo`, `atan2Pi_roundsTo` | The same contract for `powr` at a positive base, `compound` above -1, and the two angles at a nonzero `y`, where the result has the sign of `y`. |
| `Model.Transcendentals.CorrectlyRounded.pow_roundsTo_of_pos`, `pow_roundsTo_of_neg`, `locates_pow_of_pos`, `locates_pow_of_neg` | **`pow` is correctly rounded in every direction.** For a finite positive base and a finite exponent the result meets `RoundsTo fmt mode (p ^ q)`, and for a finite negative base and an integral exponent `RoundsTo fmt mode (p ^ n)` with the sign of `p ^ n`. No search has to settle. |
| `Model.Transcendentals.Directed.exp_roundsTo`, `expm1_roundsTo`, `log_roundsTo`, `logp1_roundsTo`, `exp_inexact_iff`, `expm1_inexact_iff`, `log_inexact_iff`, `logp1_inexact_iff`, `exp_invalid_divideByZero`, `expm1_invalid_divideByZero`, `log_invalid_divideByZero`, `logp1_invalid_divideByZero` | `exp`, `expm1`, `log` and `logp1` with flags meet the contract in every direction, raise `inexact` exactly when the finite result is not the real value, and raise neither `invalid` nor `divideByZero`. |
| `Model.Algebraic.Directed.rSqrt_roundsTo`, `hypot_roundsTo`, `rootn_roundsTo_of_pos`, `rootn_roundsTo_of_neg`, `cbrt_roundsTo_of_pos`, `cbrt_roundsTo_of_neg`, `pown_roundsTo`, `rSqrt_inexact_iff`, `hypot_inexact_iff`, `rootn_inexact_iff_of_pos`, `rootn_inexact_iff_of_neg`, `pown_inexact_iff`, `rSqrt_invalid_divideByZero`, `hypot_invalid_divideByZero`, `rootn_invalid_divideByZero_of_pos`, `rootn_invalid_divideByZero_of_neg`, `pown_invalid_divideByZero` | `rSqrt`, `hypot`, `rootn`, `cbrt` and `pown` with flags meet the contract in every direction, for `(√q)⁻¹`, `√(p² + q²)`, `q ^ (1 / n)` (its negative for a negative operand and an odd degree) and `q ^ n`. They raise `inexact` exactly when the finite result is not that value, and neither `invalid` nor `divideByZero`. `cbrt` is `rootn` of degree three. |
| `Model.Transcendentals.Directed.exp_overflow_iff`, `expm1_overflow_iff`, `log_overflow_iff`, `logp1_overflow_iff`, `exp_underflow_iff`, `expm1_underflow_iff`, `log_underflow_iff`, `logp1_underflow_iff` | `exp`, `expm1`, `log` and `logp1` with flags raise `overflow` exactly when the rounding of the real value with an unbounded exponent range exceeds the largest finite value in magnitude, and `underflow` exactly when `inexact` is raised and the magnitude of the real value is tiny after rounding in the direction, for every format descriptor. |
| `Model.Algebraic.Directed.rSqrt_overflow_iff`, `hypot_overflow_iff`, `rootn_overflow_iff_of_pos`, `rootn_overflow_iff_of_neg`, `pown_overflow_iff`, `rSqrt_underflow_iff`, `hypot_underflow_iff`, `rootn_underflow_iff_of_pos`, `rootn_underflow_iff_of_neg`, `pown_underflow_iff` | The same two statements on `overflow` and `underflow` for `rSqrt`, `hypot`, `rootn` and `pown` with flags. |
| `ExecFloat.Binary.CorrectlyRounded.apply_roundsTo` | The configured functions of one argument meet the contract in every direction. |

The special cases at zeros, infinities and NaNs are definitions and have no theorem. They are
tested: 195 cases of the standard on binary16, and in five
rounding directions every encoding of the eight-bit formats (an IEEE one, OCP E5M2 and E4M3,
and the ONNX formats E4M3FNUZ and E5M2FNUZ),
every pair of a six-bit and of a four-bit format, and pseudo-random operands of binary16,
binary32 and binary64 against `mpmath` (`tests/oracles/ieee2019.sh`). One call takes between 1 and 160 milliseconds for
binary64. Sine, cosine and tangent of an argument beyond about `2 ^ 500` take about a minute,
because the argument is reduced by exact enclosures of π.

## Error bounds inferred from code

Import `FloatLib.Tactic.Roundoff`. You write the
computation, and the analysis builds the reference, the same computation in exact arithmetic on the
decoded inputs, and the error budget from its code. At a call of a function whose real model the
analysis has no rule for, such as a real function the program takes, the reference applies that
model to the decoded computed argument, so the argument's rounding is not part of the bound. Here
is a quarter of a binary32 value:

```lean
import FloatLib
import FloatLib.Tactic.Roundoff

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
| `Model.cast_rounding`, `Model.isFinite_cast_of_mixedError` | A finite cast into an IEEE destination has its one-rounding mixed budget. An enclosure inside the destination's largest finite magnitude proves the cast finite. |
| `Model.cast_rounding_of_no_saturation` | A finite-input, finite-output cast to any non-saturating encoding, including E4M3 and FNUZ, has the destination's one-rounding budget `(u, eta)`. |
| `Model.cast_rounding_policy`, `Model.abs_toReal_cast_sub_le_policy` | Every finite-input, finite-output cast has bound `u*abs(x) + eta`, plus `max(0, abs(x)-M)` for a fully finite destination with largest finite magnitude `M`. |
| `Model.scale_rounding` | IEEE exponent scaling with a finite result has one relative/underflow rounding allowance when exact scaling's range premise is unavailable. |
| `ExecFloat.Binary.isFinite_add_of_mixedError` and its siblings | For an IEEE descriptor, finite operands whose exact result has an enclosure at most the largest finite value have a finite result; a quotient also needs a divisor that is not an executable zero. |
| `ExecFloat.Binary.isFinite_sub_self`, `isFinite_add_of_isZero_left`, `isFinite_mul_of_abs_toReal_eq_one_left` and their siblings | Under the hypotheses of the exact operation, an IEEE descriptor and its zero, unit-magnitude or finiteness facts, the result is finite with no range condition. |
| `Model.toReal_ofRat_eq_roundAt`, `Model.isFinite_ofRat`, `Model.abs_toReal_ofRat_sub_le` | For an IEEE descriptor, a finite conversion of a rational is its rounding to nearest, within one rounding error; a rational of magnitude at most the largest finite value converts to a finite value. |
| `Model.cast_toRat_eq_toReal`, `Model.toReal_abs_of_isFinite`, `Model.abs_toReal_sub_le_of_containsReal` | A value's rational decoding, read as `0` for an exceptional value, is its total real value; clearing the sign of a finite value is exact in a format with signed zero; and a rational enclosure bounds a finite candidate's error. |

`Analysis.MixedError.Rounding` also registers existing exact-widening theorems and the new
exact-product and exact-scaling families. Exact rules are tried before rounded bounds.
Configured `ofModel` observations and ordinary wrappers around casts preserve this selection.
Thus an ordered wide-accumulator dot has no product-rounding allowance; its additions still
round. FMA after exact widening uses the existing one-rounding FMA theorem.

### Backward error and closed forward bounds

`roundoff (backward := true) theorem name := computation` states a backward-error theorem: the
computed value is the exact computation on inputs `x * (1 + δ)`, with a bound on each `|δ|` read
off the code, up to an absolute error only where an operation has one. For the dot product
`Fin.foldl n (fun s j => s + x j * y j) 0` it proves, from a finite result,

```lean
∃ δx, (∀ j : Fin n, |δx j| ≤ (1 + u) ^ (n - 1 - ↑j + 2) - 1) ∧
  |toReal (dot x y) - List.foldl (fun s j => s + toReal (x j) * (1 + δx j) * toReal (y j)) 0
      (List.finRange n)| ≤ η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k
```

with `u = unitRoundoffAt format` and `η = underflowErrorAt format`. `(perturb := [y])` chooses the
perturbed inputs and `(factor := right)` the factor of a product that takes its rounding.
`roundoff closed theorem` states the forward bound that follows,
`∑ j, |toReal (x j)| * ((1 + u) ^ (n - 1 - ↑j + 2) - 1) * |toReal (y j)|` plus the same underflow
term. Each read is bounded by itself there, so it also covers literals, repeated reads, products
of entries, quotients by computed divisors, and the correctly rounded exponential and logarithm
(a softmax weight, a log-sum-exp). `#roundoff_shape name` says whether a generated mixed bound is
relative. The backward mode covers sums, dot products, Horner's rule, rows of matrix products,
squares and Euclidean norms, steps with several perturbed entries, loops inside a loop step,
branches, maxima and minima, the mixed-precision rules and the fused multiply-add. A rounding
that the inputs of its own operation cannot take moves onto the other factor of the product
around it, which covers a polynomial in monomial form and Estrin's scheme. A product of entries
is the exact product of entries perturbed by one rounding each. It refuses, naming the subterm,
a literal in a rounded sum, an input read with roundings that differ when no other factor takes
them, a function without a rule and a compensated sum. The names below are in
`FloatLib.Numerics` unless qualified.

| Theorem | Informal statement |
| --- | --- |
| `MixedError.eq_mul_factor_add_offset`, `MixedError.abs_factor_sub_one_le`, `MixedError.abs_offset_le` | A mixed error `MixedError x x₀ r a` is the standard model `x = x₀ * c + η` for the explicit factor `MixedError.factor` with `|c - 1| ≤ r` and offset `MixedError.offset` with `|η| ≤ a`. |
| `Backward.round` | One rounded operation: if `x` has the mixed error `(r, a)` against `X`, `X` is within `A` of a reference `R`, and `R` times the factor of the rounding is `R'`, then `x` is within `A * (1 + r) + a` of `R'`. |
| `Backward.scale_add`, `scale_sub`, `scale_neg`, `scale_mul_left`, `scale_mul_right`, `scale_div`, `scale_ite` | A sum, a difference and a branch take a factor in both sides, a product in one factor, a quotient in its numerator. |
| `Backward.scale_sq`, `Backward.abs_sqrt_sub_one_le`, `Backward.scale_sqrt`, `Backward.scale_max`, `Backward.scale_min` | A square takes a nonnegative factor `c` as `√c` in both factors, and `√c` is as close to one as `c`; a square root takes `c * c` in its argument; a maximum and a minimum take a nonnegative factor in both operands. |
| `Backward.move_left`, `Backward.move_right`, `Backward.restate` | A factor on one factor of a product is the same factor on the other, `A * c * B = A * B'` when `B * c = B'`, and a bound against a reference holds against an equal one: how a rounding that stayed on a factor moves to the other. |
| `Backward.abs_delta_scale`, `Backward.abs_mul_sub_one_le` | A perturbation within `g - 1` that takes a factor within `h - 1` of one is within `g * h - 1`: `k` roundings `u` give `(1 + u) ^ k - 1`. |
| `List.fold_backward`, `List.fold_backward_exact`, `List.fold_backward_fixed`, `List.fold_backward_fixed_exact` and their `_finRange` forms | The loop rule. If one step computes `G (observe s * ρ) v p` up to `a s v`, for a factor `ρ` within `q - 1` of one and perturbations `p`, and scaling the accumulator scales the step (`G (s * c) v (scale c p) = G s v p * c`), then the loop is within `List.foldBackwardAbsolute` of the exact loop of `G` on perturbed entries, and the perturbations at position `k` of `n` satisfy the bound after `n - 1 - k` further steps. `exact`: no absolute error, an equality. `fixed`: the accumulator takes no factor. `finRange`: perturbations indexed by `Fin n`. The slope `L v` of `G` in its accumulator is needed at the perturbations a step may take only, so a step may multiply its accumulator by a perturbed entry. |
| `Backward.abs_sub_le_of_eq_mul_le`, `Backward.abs_perturbed_le`, `Backward.abs_mul_le_mul` | The slope of such a step: `|D| ≤ L * |s - s'|` when `D = μ * (s - s')` and `|μ| ≤ L`, where a perturbed read is at most `|v| * g` for a perturbation within `g - 1` and a product is at most the product of bounds. |
| `List.foldBackwardAbsolute_le_geom` | The absolute term of the loop rule is at most `c * ∑ k < n, (ℓ * q) ^ k` when each step's slope is at most `ℓ` and its absolute error at most `c`. |
| `List.AllSteps.of_foldl` | A property that the accumulator has before a step whenever it has it after, such as finiteness under IEEE addition, holds at every visited step once it holds of the result. |
| `ExecFloat.Binary.isFinite_of_isFinite_add`, `isFinite_of_isFinite_sub`, `isFinite_of_isFinite_mul`, `isFinite_left_of_isFinite_div` | For an IEEE descriptor, a finite configured sum, difference or product has finite operands, and a finite quotient a finite numerator. |
| `List.abs_foldl_sub_foldl_le`, `List.abs_foldl_finRange_sub_le`, `List.abs_foldl_zip_sub_foldl_le` | A backward statement gives a forward bound: two loops whose steps differ by at most `D v` at one accumulator, the second with slope at most `L v`, differ by at most the loop `e ↦ e * L v + D v` of accumulated differences. |
| `List.abs_foldl_affine_sub_le`, `List.abs_foldl_add_sub_le`, `List.abs_foldl_add_sub_le_mul` | The same for loops `s ↦ s * m v + t v` whose terms differ by at most `c v`; for sums, the sum of the `c v`; and for sums of terms within `γ * t₀ v` of `t₀ v`, the relative bound `γ` times the exact sum. |
| `List.foldl_finRange_add_eq_sum` | The accumulated differences of a step with slope one over `Fin n` are `e + ∑ j, D j`. |
| `Backward.deviation_leaf`, `Backward.deviation_mul`, `Backward.forward` | A perturbed read `v * (1 + d)` with `|d| ≤ b` is within `|v| * b` of `v`; a product of values within `A` and `B` of `R` and `S` is within `A * (|S| + B) + |R| * B` of `R * S`; and a value within `A` of a reference within `B` of the exact value is within `B + A` of it. |
| `Backward.deviation_div`, `Backward.deviation_node`, `Backward.deviation_exp`, `Backward.deviation_log` | A quotient of values within `A` and `B < |S|` of `R` and `S` is within `(A * |S| + |R| * B) / (|S| * (|S| - B))` of `R / S`; a value within `A` of `R`, perturbed as a whole by `d` with `|d| ≤ b`, is within `A + (|R| + A) * b` of `R`; the exponential of a value within `A` of `R` is within `exp R * (exp A - 1)` of `exp R`; and its logarithm, for `A < R`, within `A / (R - A)` of `log R`. |

### Control flow, native floats and tighter bounds

`roundoff` analyzes a `match` alternative by alternative. The forward commands state the
reference, the budgets and the premise as the `match` of those of the alternatives; the closed
and backward commands state the `match` of the statements of the alternatives, and a branch that
binds the proof of its condition as the conjunction of its two cases. A program on `Float32` or
`Float`, observed through `ExecFloat.Binary.ofFloat32` or `ofFloat`, is analyzed as the same
program on `Binary32` or `Binary64` by the laws below (they come with `FloatLib.Tactic.Roundoff`,
from `FloatLib.Floats.Formats.IEEE754.Native.Roundoff`); the elementary functions of the native types are host library
calls and have no law. `#roundoff_check name inputs` evaluates the bound and the reference of a
generated theorem at given or sampled inputs and warns where the bound is at least the magnitude
of the reference. It is a report and proves nothing.

| Theorem | Informal statement |
| --- | --- |
| `ExecFloat.Binary.toReal_ofFloat32_add`, `isFinite_ofFloat32_add` and their `sub`, `mul`, `div` and `ofFloat` forms | When the imports of the operands are finite, the import of a native sum, difference, product or quotient has the real value of the `Binary32` (or `Binary64`) operation on the imports, and it is finite when that operation is. Generated by `native_rule` from the agreement theorems of the native carriers. |
| `ExecFloat.Binary.toReal_ofFloat32_sqrt`, `toReal_ofFloat32_neg`, `toReal_ofFloat32_ofNat`, `toReal_ofFloat32_toFloat32`, their `isFinite` forms and their `ofFloat` forms | The same for the square root and the negation; the import of the native literal `Float32.ofNat n` is `ofRat n`; and a `Binary32` exported to `Float32` and imported again is the value. |
| `ExecFloat.Binary.isFinite_ofFloat32`, `isFinite_ofFloat` | The import is finite exactly when the native value is. |
| `ExecFloat.Binary.sub_of_sterbenz` | The Sterbenz rule in the form of a generated theorem: for finite configured values of one sign within a factor of two, the difference is finite and adds no rounding error. `roundoff` proves its three conditions from order hypotheses by linear arithmetic, also from the classic bounds `y / 2 ≤ x ≤ 2 * y` and from interval facts. |
| `Model.unitRoundoffIn`, `Model.underflowErrorIn`, `Model.mixedError_roundAt_mode`, `Model.abs_roundAt_sub_le_mode` | The unit roundoff and the underflow allowance of a rounding attribute, `u` and `η` for `nearest` and `nearestAway` and twice those for the four directed attributes; `roundAt fmt t mode` has that mixed error for every attribute. |
| `Model.roundDyadicPosUp_finite_roundAt_of_le_posMaxFinite`, `Model.Internal.Directed.roundDyadic_finite_roundAt` | For an IEEE descriptor, upward rounding of a positive dyadic no larger than the largest finite value is finite and is the real ceiling on the format grid. So a rounding of an exact dyadic within the largest finite magnitude is finite and is `roundAt` of its real value, in each of the six attributes. |
| `Model.fract_scaledMantissa_eq_half_iff`, `Model.roundDyadicNearestAway_finite_roundAt` | The tie test that `nearestAway` runs on the bits of a dyadic holds exactly when its scaled mantissa is halfway between two integers. Off such a tie `nearestAway` is nearest-even rounding and at one it is rounding away from zero, so the executable rounding of a dyadic within the largest finite magnitude is finite and is `roundAt` in `nearestAway`. |
| `Model.add_finite_roundAt`, `Model.sub_finite_roundAt`, `Model.mul_finite_roundAt`, `Model.fma_finite_roundAt` | For an IEEE descriptor and every rounding attribute, finite operands whose exact sum, difference, product or `x * y + z` is within the largest finite magnitude have a finite result in that attribute, the rounding of the exact result. A finite result alone is not enough: a directed rounding saturates at the largest finite value. |
| `Model.abs_roundAt_sub_le_halfUlps_mul`, `Model.abs_roundAt_sub_le_mode_of_normal`, `Model.abs_roundAt_add_sub_le_mode`, `Model.genericFormat_add_of_abs_lt_minNormalAt` | A rounding in any attribute misses by at most `halfUlps` half units in the last place. At or above the least normal magnitude it has only the relative error of its attribute, and the rounding of a sum of two grid points has it at every magnitude, with no underflow term: below the least normal magnitude such a sum is itself a grid point. |
| `Model.mixedError_toReal_of_eq_roundAt_mode`, `ExecFloat.Binary.mixedError_toReal_of_eq_roundAt_mode` | A value equal to the rounding of `t` in a rounding attribute has the mixed error of that attribute. |
| `Model.add_rounding_mode`, `sub_rounding_mode`, `mul_rounding_mode`, `fma_rounding_mode`, `isFinite_add_of_mixedError_mode` and its `sub`, `mul` and `fma` forms, the same names under `ExecFloat.Binary`, and `Model.abs_toReal_add_sub_le_mode` and `ExecFloat.Binary.abs_toReal_add_sub_le_mode` with their `sub`, `mul` and `fma` forms | Under the premises of `add_finite_roundAt` the operation in the attribute `mode` has the mixed error `(unitRoundoffIn fmt mode, 0)` for a sum or a difference and `(unitRoundoffIn fmt mode, underflowErrorIn fmt mode)` for a product or a fused multiply-add; an enclosure of the exact result at most the largest finite value makes the result finite. These are the rules of `roundoff` for `add x y (mode := m)` and the three others, in its forward, closed and backward modes. `ExecFloat.Binary.fma_rounding` is the rule of a fused multiply-add on a configured type in the default attribute, with a finite result: its operand errors and one rounding `(u, η)`. `ExecFloat.Binary.toReal_add_nearest` and its `sub` and `mul` forms read the default attribute written out as the operator. |
| `MixedError.abs_sub_le_computed`, `MixedError.mem_Icc_computed` | The error in terms of the computed value, `(1 - r) * \|x - x₀\| ≤ r * \|x\| + a`, and for `r < 1` the exact value in the interval centered at the computed one with radius `(r * \|x\| + a) / (1 - r)`. |
| `Model.abs_toReal_add_sub_le_abs_right`, `Model.one_add_mul_abs_toReal_add_sub_le` | A finite sum errs by at most the magnitude of its right operand, and by at most `u / (1 + u)` of the exact sum, with no underflow term. |
| `Model.one_add_mul_abs_toReal_foldl_add_sub_le`, `Model.abs_toReal_foldl_add_sub_le`, `ExecFloat.Binary.abs_toReal_foldl_add_sub_le` | A finite left-to-right sum of `n` terms onto a seed has error at most `n * u / (1 + u) * (\|seed\| + ∑ \|term i\|)`, and from a seed of real value zero at most `(n - 1) * u * ∑ \|term i\|`: the linear constant of Rump (2012), for every IEEE descriptor and length. |
| `Model.abs_toReal_foldl_add_mul_sub_le`, `ExecFloat.Binary.abs_toReal_foldl_add_mul_sub_le` | A finite inner product loop over `n` indices from a seed of real value zero has error at most `n * u * ∑ \|left i * right i\|` when no exact product is in the subnormal range: the constant of Jeannerod and Rump (2013). |

### `exp x - 1 - x`

Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Expm1x` (or `FloatLib.Tactic.Roundoff`,
which has its contract). `ExecFloat.Binary.CorrectlyRounded.expm1x x (mode := m)` is
`exp x - 1 - x` with one rounding in the attribute `m`, nearest-even by default. The name is that
of the function in R's package DPQ; GSL's `gsl_sf_exprel_2` is the scaled form
`2 (exp x - 1 - x) / x ^ 2`. The rounding is decided by exact comparisons of `exp x` with rational
candidates, so no cancellation occurs at any argument.

| Theorem | Informal statement |
| --- | --- |
| `Model.AlgebraicRounding.toReal_roundDown_eq_roundAt`, `isFinite_roundDown`, `roundUp_eq_posInf_or_finite_roundAt` | For an exact comparison oracle of a positive real, `roundDown` is finite and, below `2 ^ (emax + 1)`, the largest value of the format at or below the target; `roundUp` is `+∞` or finite and the least value at or above it. |
| `CorrectlyRounded.roundAt_nearestAway_eq_of_irrational`, `irrational_exp_sub_one_sub` | An irrational real rounds alike in the two nearest attributes, and `exp q - 1 - q` is irrational for a nonzero rational `q`. |
| `CorrectlyRounded.toReal_expm1x_of_isFinite` | For an IEEE descriptor and a finite input, a finite result whose real value is below `2 ^ (emax + 1)` (below `Certified.overflowThreshold` in the configured statement) is `roundAt fmt (exp x - 1 - x) mode`, in each of the six attributes. |
| `CorrectlyRounded.isFinite_expm1x`, `toReal_expm1x_eq_roundAt` | In the nearest and the downward attributes the result is finite and correctly rounded when the real value is below the overflow threshold. The configured statements are those of the default attribute and are the contract `roundoff` uses. |
| `Model.AlgebraicRounding.roundUp_finite_roundAt_of_le_posMaxFinite`, `CorrectlyRounded.lt_overflowThreshold_of_le_posMaxFinite` | For a positive target at most the largest finite value, `roundUp` is finite and the least value of the format at or above the target; such a target is below the overflow threshold. |
| `CorrectlyRounded.isFinite_expm1x_of_le_posMaxFinite`, `toReal_expm1x_eq_roundAt_of_le_posMaxFinite`, and the configured `toReal_expm1x_eq_roundAt_mode`, `isFinite_expm1x_mode` | When the real value is at most the largest finite value, the result is finite and correctly rounded in each of the six attributes, the two upward ones included. The configured statements are the contract `roundoff` uses for a call that names an attribute. |
| `CorrectlyRounded.mixedError_toReal_expm1x` | Under the premises of `toReal_expm1x_of_isFinite`, the result has the mixed error `(unitRoundoffIn fmt mode, underflowErrorIn fmt mode)`. |
| `CorrectlyRounded.toReal_expm1x_nonneg`, `toReal_expm1x_of_isZero`, `isFinite_expm1x_of_isZero` | The result is never negative, for any input and attribute; a zero gives the positive zero. |
| `MixedError.exp_sub_one_sub`, `Numerics.Backward.deviation_exp_sub_one_sub`, `Numerics.exp_sub_one_sub_nonneg`, `Numerics.exp_sub_one_sub_pos` | `exp x - 1 - x` moves with an argument of error `e = r * \|x₀\| + a` by at most `(exp (\|x₀\| + e) - 1) * e`, in the mixed analysis and in the closed forward bound; it is nonnegative, and positive away from zero. |

## Stochastic rounding and fresh arithmetic

Import `FloatLib.Numerics.Quantization.Stochastic` for the grid law and
`FloatLib.Floats.Formats.Stochastic` for its binary, P3109 and fixed-point
instances. Import
`FloatLib.Numerics.Quantization.Stochastic.Affine` for fresh rounded sums,
dots, and affine computations. The probability command lives in
`FloatLib.Tactic.Roundoff.Stochastic`:
`roundoff stochastic theorem name := computation` generates a certificate and
`_mean`, `_second`, `_tail`, and `_confidence` theorems. It retains the
reachable-input admissibility premise. `Stochastic.Support` discharges it for a
concrete loop by a finite check, and the guide's “Fresh stochastic rounding”
section works through a three-step bfloat16 sum with a rational budget.

Names below are in `Numerics.Quantization.Stochastic` unless qualified otherwise.

| Theorem | Informal statement |
| --- | --- |
| `mean_cellLaw`, `variance_cellLaw`, `variance_cellLaw_le` | For `a < b` and `x ∈ [a,b]`, the two-neighbor law has mean `x` and variance `(x-a)(b-x) ≤ (b-a)²/4`. |
| `BinaryInterchange.Model.Policy.roundQuot_cell` | Uniform finite entropy implements the ideal quotient-rounding cell law when the denominator divides the entropy range. |
| `BinaryInterchange.Model.Policy.binaryRounder_law` | Every binary descriptor has the local unbiased rounding law under `StochasticSafe`: finite, unclipped endpoints, a valid range, and entropy divisibility. |
| `sum_certificate`, `dot_certificate`, `affine_certificate` | Actual fresh-entropy rational executions have the exact reference mean; local second-moment and exponential-moment budgets add under reachable-step admissibility and proxy bounds. |
| `run_mem_reach`, `Rounder.Support.sum_safe`, `Rounder.Support.safe` | When a list holds every possible outcome of each rounding, the lists `reach` builds hold every state of the loop for every entropy history, and a check of the listed accumulators proves `SumSafe` or `DotSafe`. `BinaryInterchange.Model.Policy.binarySupport` is the two-outcome list of the binary runtime. Import `Stochastic.Support`. |
| `Rounder.Support.sum_certificate`, `Rounder.Support.affine_certificate` | The same checks with rational bounds on the listed cell widths give the certificate of a sum or an affine map with a rational budget. |
| `Certificate.tail`, `Certificate.confidence`, `Certificate.exact_of_zero` | A positive budget gives a two-sided tail and confidence radius; a zero budget gives almost-sure exactness. |
| `Network.gap_mgf`, `classification_confidence` | Composed network gap bounds account for uncertain ReLU signs; suitable positive margins and allocated failure budgets imply a classification confidence bound. Import `Stochastic.Network` and `Stochastic.Classification`. |

These are probability theorems for specified entropy laws, not an identification
of a hardware random source with independent uniform words. Saturation, flushing,
finite-word bias, and exceptional encodings are treated explicitly by the boundary
and implementation refinements; a finite unbiased-value conclusion needs its
stated premises.

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
| `Numerics.ReductionTree.depth`, `depth_le_nodeCount`, `clog_le_depth`, `depth_leftChain`, `length_leaves_le_two_pow_depth` | The depth of a schedule is the largest number of additions between an input and the result. Over `n` inputs it lies between `⌈log₂ n⌉` and `n - 1`, and the left-to-right chain reaches `n - 1`. |
| `Numerics.ReductionTree.mixedBudget_zero_le_depth`, `abs_eval_sub_exact_le_depth`, `depth_factor_le` | Under local relative bounds the error is at most `((1 + u) ^ depth - 1) * Σ\|xᵢ\|`: an input is rounded once at each addition above it. The bounds in the number of additions follow, since no schedule is deeper than its size. |
| `Model.ReductionTree.abs_toReal_eval_sub_sum_le_depth`, `Model.abs_toReal_reduceAlong_sub_le_depth`, `abs_toReal_reduceAlong_sub_le_of_tree` | Every finite IEEE reduction tree of depth `d` has error at most `((1 + u)^d - 1) * Σ\|xᵢ\|`, and a reduction along an association order in an accumulator format has that bound plus the half unit of its final conversion. A schedule that pairs its `n` inputs has depth about `log₂ n`. |

| `Model.abs_toReal_reduceAlong_sub_le` | IEEE 754-2019 §9.4 lets a reduction associate in any order and evaluate in any wider format (ISO/IEC TS 18661-4, N1797, Introduction). `Model.reduceAlong acc out term schedule` adds the terms of the inputs along the association order `schedule` in the accumulator format `acc` and converts the result to `out`. For every schedule and term function, IEEE `acc` and `out`, and a finite evaluation, its distance from the exact sum of the terms is at most `((1 + u) ^ n - 1) * Σ\|tᵢ\|` for the `n` additions (`u = unitRoundoffAt acc`) plus half a unit in the last place of `out` for the final conversion. `sumAlong`, `sumAbsAlong`, `sumSquareAlong` and `dotAlong` are `reduceAlong` at the terms of the four reductions. Import `BinaryInterchange.Reduction.Schedule.Proof`. |
| `Model.reduceInOrder_eq_reduceAlong`, `Numerics.ReductionTree.eval_extend` | The left-to-right loop `Model.reduceInOrder`, defined for a list of any length (the empty reduction is `+0`), is `reduceAlong` along the left-leaning schedule that starts at `+0`. |
| `Model.sumInOrder_mixedError`, `sumAbsInOrder_mixedError`, `sumSquareInOrder_mixedError`, `dotInOrder_mixedError` | The bounds that `roundoff` generates from `sumInOrder`, `sumAbsInOrder`, `sumSquareInOrder` and `dotInOrder`: a mixed relative and absolute error against the exact real sum, sum of absolute values, sum of squares and dot product of the inputs, for a list of any length and all source, accumulator and destination descriptors with `src.fracWidth ≤ acc.fracWidth` and `acc.minSubnormalExponent ≤ src.minSubnormalExponent` (the grid of the accumulator contains the grid of the source, so the conversion of an input is exact). Premises, as `roundoff` states them: IEEE accumulator and destination, finite inputs and result, and no overflow at the states the loop visits (`List.AllSteps`). |

Model results live in `BinaryInterchange.Reduction.Tree` and require finite leaves and finite
intermediate additions. They don't identify an arbitrary native CPU or GPU reduction with a
particular tree. That connection needs a downstream execution proof.

### Blocked dot-product order

Import `FloatLib.Numerics.Reduction.Blocked`. Names below are in
`FloatLib.Numerics.BlockedDot`. `kernelEntry` forms each block with a left-to-right chain of
`fma` calls from zero, then adds block partials in order, with an optional starting value.

| Theorem | Informal statement |
| --- | --- |
| `kernelEntry_eq_sum` | Over a commutative semiring, with exact `fma a b c = a*b+c` and positive block width, the result is `start.getD 0 + ∑ k < K, a k * b k`. |
| `kernelEntry_congr` | For any supplied operations, changing operands beyond the first `K` entries cannot change the result. |
| `kernelEntry_first` | A nonempty initial range gives the corresponding prefix fold when the width is positive and the range ends on a block boundary or at `K`. |
| `kernelEntry_continue` | A later range beginning at a positive block boundary extends the prefix fold when its end is a block boundary within `K`, or `K` itself. |
| `kernelEntry_eq_blocks` | For every positive block width `w`, `kernelEntry` is a loop over the `K / w` full blocks of exactly `w` terms, from the start value or the first block's partial, followed by one block of `K % w` terms when that is not zero: the shape of a generated kernel. |
| `min_succ_mul_eq`, `blockPartial_of_lt_div`, `blockPartial_div`, `mul_lt_of_lt_blockCount`, `blockCount_eq_div_add` | Block `u ≤ K / w` ends `w` terms after its start `u * w` when `u < K / w`, and `K % w` terms after it when `u = K / w`. So a block below `K / w` is the `w` terms from `u * w`, and block `K / w` is the `K % w` terms after the full blocks. A block below the block count starts below `K`, and the number of blocks is `K / w`, plus one when terms remain. |

The order and continuation identities need no associativity of the supplied operations, so they
apply to rounded arithmetic too. The semiring sum identity concerns exact operations. Relating an
external kernel to this schedule still requires proving that kernel's operations and order agree.

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
| `Model.Reduction.toReal_sumAbs`, `Model.Reduction.toReal_sumSquare` | IEEE 754-2019 §9.4 `sumAbs` and `sumSquare` (ISO/IEC TS 18661-4, N1797 F.10.10a.2 and F.10.10a.3): on finite operands with a finite result, the value is the exact sum of the magnitudes or of the squares rounded once to nearest-even. |
| `Model.Reduction.sumAbs_status_of_decidingInfinity?`, `sumSquare_status_of_decidingInfinity?`, `dot_status_self_eq_sumSquare`, `sumAbs_status_eq_sum` | An infinite operand gives `+∞` even beside a quiet NaN, unless a signaling NaN comes first; without one, `sumSquare` is the dot product of the array with itself and `sumAbs` the sum of the magnitudes. |
| `Model.Reduction.toReal_scaledProd_product`, `mixedError_scaledProd` | §9.4 `scaledProd` (N1797 F.10.10a.5): for finite nonzero factors the scaled product is the exact product times `2 ^ -sf` rounded once, the scaled exact product has magnitude in `[1, 2)`, and the result carries one mixed relative and absolute rounding error. |
| `Model.Reduction.toReal_scaledProdOfSums_product` | The same rounding statement for `scaledProdSum` and `scaledProdDiff`, the scaled products of exact sums and differences. |
| `ExecFloat.Binary.toModel_sumAbs`, `toModel_sumSquare`, `map_toModel_scaledProd`, `map_toModel_scaledProdSum`, `map_toModel_scaledProdDiff` | The configured reductions decode to the model reductions on the decoded operands. |

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
| `Arithmetic.sameQuantum_quantum`, `Arithmetic.toRat?_quantum` | IEEE 754-2019 §5.3.2 `quantum` (C23 `quantumdN`, N3220 7.12.15.3): the quantum of a finite datum has its quantum exponent `q` and the value `10 ^ q`. |
| `Arithmetic.extremum_status`, `extremum_of_isNaN_eq_false`, `extremum_value_eq_or`, `extremum_number_nan_left`, `extremum_number_nan_right` | §9.6: the eight minimum and maximum operations raise `invalid` exactly for a signaling NaN; without a NaN the result is one of the operands, unchanged; a number is preferred to one NaN in the four `...Number` operations. |
| `Arithmetic.numericValue?_selectExtremum`, `numericValue?_abs_selectByMagnitude`, `numericValue?_minimum`, `numericValue?_maximum` | The selected datum has the smaller or the larger exact value, infinities included, or the smaller or larger magnitude. Equal values are ordered by `totalOrder`, the rule of the General Decimal Arithmetic Specification 1.70 for `max` and `min`. |
| `Datum.getPayload_setPayload`, `Datum.toRat?_of_admissiblePayload?`, `Datum.setPayload_getPayload`, `Datum.setPayloadSignaling_getPayload`, `Datum.setPayload_valid` | §9.7: the payload read from `setPayload f x` is the integer that an admissible `x` denotes; writing back the payload of a NaN of the format gives the quiet or the signaling NaN with that payload and a clear sign; a NaN built by `setPayload` is a datum of the format. |
| `decodeDecimal_of_encodeDecimal_eq_some`, `decodeBinary_of_encodeBinary_eq_some` | §5.5.2: decoding the decimal (DPD) or the binary (BID) encoding of a datum gives the datum back. |
| `Arithmetic.sum_eq_project`, `sumAbs_eq_project`, `sumSquare_eq_project`, `dot_eq_project` | IEEE 754-2019 §9.4 (ISO/IEC TS 18661-4, N1797 F.10.10a.1 to F.10.10a.4): for finite operands, of any decimal formats, each decimal reduction is one `project` of the exact result, in every format and rounding direction: the sum of the exact values, of their magnitudes, of their squares, or of the products. The terms are added as rationals, so nothing overflows or underflows in between. |
| `Arithmetic.sum_error_le_half`, `Arithmetic.sum_inexact_iff`, `Arithmetic.sum_valid`, `sumAbs_valid`, `sumSquare_valid` | To nearest the decimal `sum` is within half a unit of the rounding quantum of the exact sum when no overflow is signaled; in every direction `inexact` is raised exactly when the result is not the exact sum; and every reduction returns a datum of the format, for all operands. |
| `Arithmetic.scaledProd_eq_project`, `scaledProdSum_eq_project`, `scaledProdDiff_eq_project`, `Reduction.abs_scaled_mem` | IEEE 754-2019 §9.4 (N1797 F.10.10a.5 to F.10.10a.7): for finite operands whose exact product `P` is not zero, the scale factor of the decimal `scaledProd` is `Int.log 10 \|P\|`, the decimal exponent of the leading digit of `P`, and the scaled product and the flags are those of one `project` of `P / 10 ^ sf`, a rational of magnitude in `[1, 10)`, in every format and rounding direction. `scaledProdSum` and `scaledProdDiff` are the same for the product of the exact sums and differences. |
| `Arithmetic.scaledProd_inexact_iff`, `scaledProd_status`, `Format.unitDecade_of_quantum`, `scaledProd_valid`, `scaledProdSum_valid`, `scaledProdDiff_valid` | `inexact` is raised exactly when `pr × 10 ^ sf` is not the exact product; a format that holds the decade from one to ten in its normal range (decimal32, decimal64, decimal128) raises neither `overflow` nor `underflow`; and every result is a datum of the format, for all operands. |
| `Arithmetic.reduceInOrder_eq_reduceAlong`, `reduceAlong_valid`, `reduceInOrder_valid` | The decimal reductions in a chosen association order and accumulator format (`reduceAlong`, `reduceInOrder` at the terms `Reduction.sumTerm`, `sumAbsTerm`, `sumSquareTerm`, `dotTerm`): the left-to-right loop is the member along the left chain, and every result is a datum of the destination. Import `DecimalInterchange.Reduction.Schedule.Proof`. |
| `Arithmetic.abs_eval_sub_le`, `abs_reduceAlong_sub_le`, `add_error_lt_one`, `zpow_roundingQuantum_le` | For every association order, accumulator, destination and rounding direction, finite terms and a result without the `overflow` flag (the flags of every step accumulate, so the premise is observable): the accumulated value is finite and within `ReductionTree.mixedBudget` of the exact sum of the terms, with the relative allowance `10 ^ (1 - precision)` and the absolute allowance `10 ^ minQuantum` of the accumulator at each addition, and the delivered result adds less than one unit of the rounding grid of the destination. |
| `KernelPath.add_eq`, `KernelPath.sub_eq`, `KernelPath.mul_eq`, `KernelPath.datum_eq` | The kernel path: decimal addition, subtraction and multiplication on the fields of the data are the specified operations, value and flags, for every format, rounding direction and pair of data. The four theorems are tagged `@[kernel_optimize]`, so `float_decide` rewrites with them. |
| `KernelPath.fma_eq`, `KernelPath.finiteValue_mul` | The kernel path of the decimal fused multiply-add: `Arithmetic.fma f mode x y z = KernelPath.fma f mode x y z` for every format, rounding direction and three data. For three finite data the exact product is the product of the coefficients at the sum of the quantum exponents, and the kernel sum of that product and the third datum rounds once. |
| `KernelPath.project_eq`, `KernelPath.projectAt_eq`, `KernelPath.decimalLength_eq`, `KernelPath.roundMagnitude_natCast_div` | The pieces of that proof: the projection of an exact value `c × 10 ^ e` at its own exponent on naturals, the digit count, and the rounding increment from quotient and remainder. |
| `KernelPath.compare_eq`, `KernelPath.compare_finiteValue`, `KernelPath.compareNat_eq`, `KernelPath.compareQuiet_eq`, `KernelPath.compareSignaling_eq` | The kernel path of the 22 decimal comparisons (§5.6.1): `Datum.compare`, specified on exact rationals extended by the infinities, is `KernelPath.compare`, which aligns two finite data at the smaller quantum exponent and compares the natural coefficients by their signs, for every pair of data. The two rules state `Datum.compareQuiet` and `Datum.compareSignaling` at a predicate with that comparison; the 22 members are unfolded to their family. Import `DecimalInterchange.KernelPath.Comparison` (part of `DecimalInterchange`). |
| `KernelPath.scale_eq`, `KernelPath.convertFormat_eq`, `KernelPath.convertFromInt_eq` | The kernel path of decimal `scaleB` (§5.3.3), of the conversion between decimal formats (§5.4.2) and of the conversion from an integer (§5.4.1): each rounds one exact value `c × 10 ^ e` at its own exponent, which `KernelPath.project` computes on natural numbers, so `Arithmetic.scale`, `Conversion.convertFormat` and `Conversion.Integer.convertFromInt` equal their kernel forms for every format, rounding direction and operand. An exponent of magnitude above `2 ^ 20` is left to the specification, which never builds a power of ten beyond the range of the format. |
| `KernelPath.div_eq`, `KernelPath.divFinite_eq`, `KernelPath.projectRatio_eq`, `KernelPath.deliverRounded_eq` | The kernel path of decimal division (§5.4.1). `projectRatio` rounds a ratio of natural numbers on the scale of the least quantum, `(num / den) × 10 ^ minQuantum`: the integer part of the ratio gives the rounding quantum, one division with remainder the rounded coefficient, the remainder the increment and the `inexact` flag, one comparison the tininess, and an exact result is moved to the preferred exponent; it equals `projectMagnitude` for every format, rounding direction, numerator, nonzero denominator and preferred exponent. The delivery of a rounded coefficient (carry, overflow, flags, preferred cohort) is one definition, `deliverRounded`, shared with the square root. `Arithmetic.div` equals its kernel form for every format, rounding direction and pair of data: the same datum and the same flags. |
| `KernelPath.sqrt_eq`, `KernelPath.rSqrt_eq`, `KernelPath.hypot_eq`, `KernelPath.sqrtRatio_eq`, `KernelPath.sqrtIncrement_eq` | The kernel path of the decimal square root (§5.4.1), reciprocal square root and hypotenuse (§9.2). `sqrtRatio` rounds the root of a radicand `(num / den) × 10 ^ (2 × minQuantum)`, a ratio of natural numbers: the number of digits of its integer part gives the rounding quantum, `Numerics.Kernel.isqrt` the integer square root at that quantum, and comparisons of natural numbers the increment in each rounding direction, the `inexact` flag and the tininess; it equals `sqrtMagnitude` for every format, rounding direction, numerator, nonzero denominator and preferred exponent. `Arithmetic.sqrt`, `rSqrt` and `hypot` equal their kernel forms for every format, rounding direction and operand; a zero and a negative operand of `sqrt` and `rSqrt`, an infinity and a NaN are left to the specification. |
| `KernelPath.sum_eq`, `KernelPath.sumAbs_eq`, `KernelPath.sumSquare_eq`, `KernelPath.dot_eq`, `KernelPath.sumLoop_eq`, `KernelPath.deliverSum_eq`, `KernelPath.collect_eq`, `KernelPath.collectProducts_eq` | The kernel path of the decimal reductions (§9.4). For finite operands the exact sum is kept as two natural numbers, the sums of the positive and of the negative terms at the least quantum exponent, with the sign of an exact zero sum; `sumLoop_eq` proves that this state stands for the exact rational sum of the specification after every term, and `deliverSum_eq` that one kernel projection of the difference is the specified delivery. `Arithmetic.sum`, `sumAbs`, `sumSquare` and `dot` equal their kernel forms for every format, rounding direction and array; an array with an infinity or a NaN, and two arrays of different lengths, are left to the specification. |
| `KernelPath.pown_eq`, `KernelPath.powerSign_eq`, `KernelPath.zpow_sign` | The kernel path of the decimal integer power (§9.2): with a natural exponent the power of the coefficient is projected at the quantum exponent times the exponent of the power, and with a negative exponent the reciprocal of that power is rounded as a ratio of natural numbers (`projectRatio_eq`); the sign is that of an odd power of a negative datum, also for a zero result. `Arithmetic.pown` equals its kernel form for every format, rounding direction, datum and integer exponent; a zero to a negative power, an infinity and a NaN are left to the specification. |
| `KernelPath.logB_eq` | The kernel path of decimal `logB` (§5.3.3): for a nonzero finite datum the quantum exponent plus the number of decimal digits less one, with the digits counted by `KernelPath.decimalLength`; equal to `Arithmetic.logB` for every format and datum, the invalid results of a zero, an infinity and a NaN included. |
| `KernelPath.nextUp_eq`, `KernelPath.nextUpValid_eq`, `KernelPath.neighborAbove_eq`, `KernelPath.neighborBelow_eq`, `KernelPath.roundedPair_of_fits` | The kernel path of decimal `nextUp` and `nextDown` (§5.3.1): for a nonzero coefficient within the precision at a quantum exponent of the format, the normalization of the specification rounds nothing and scales the coefficient to the finest quantum, whose offset the number of digits decides (`roundedPair_of_fits`, in every rounding direction); the neighbouring coefficient, the step across a power of ten and the step to an infinity are comparisons of natural numbers. `Arithmetic.nextUp` equals its kernel form for every format and datum; a zero, a datum outside the format, an infinity and a NaN are left to the specification. `nextDown` is unfolded to `nextUp`. |
| `KernelPath.quantize_eq`, `KernelPath.roundToIntegralExact_eq`, `KernelPath.roundToIntegral_eq`, `KernelPath.convertToInteger_eq`, `KernelPath.quantizeAt_eq`, `KernelPath.roundAtQuantum_eq`, `KernelPath.roundAt_eq_div_add`, `KernelPath.roundAt_exact_iff`, `KernelPath.roundInteger_finiteValue`, `KernelPath.inRange_eq`, `KernelPath.fits_eq` | The kernel path of decimal `quantize` (§5.3.2), of the integral roundings (§5.3.1) and of the ten conversions to an integer (§5.4.1): the magnitude `c × 10 ^ q` rounded at a quantum `r` is a quotient of natural numbers plus the increment that the remainder decides, in every rounding direction, and the rounding is exact exactly when the remainder is zero. The range of a signed or unsigned integer format of any width, and the quantum range and precision of a decimal format, are decided by comparisons of natural numbers. `Arithmetic.quantize`, `Arithmetic.roundToIntegralExact`, `Arithmetic.roundToIntegral` and `Conversion.Integer.convertToInteger` equal their kernel forms for every format, rounding direction and operand: the same value and the same flags. |
| `KernelPath.classify_eq`, `KernelPath.isNormal_eq`, `KernelPath.isSubnormal_eq`, `KernelPath.tiny_eq` | The kernel path of the decimal classification (§5.7.2): a nonzero coefficient `c` at the quantum exponent `q` is below the least normal magnitude of the format exactly when its digit count plus the offset of `q` from the least quantum is below the precision, so `Datum.classify`, `isNormal` and `isSubnormal`, specified by a rational comparison, are tests on natural numbers, for every decimal format and every datum. |
| `KernelPath.totalOrder_eq`, `KernelPath.totalOrderFinite_eq` | The kernel path of the decimal total order (§5.10): `Datum.totalOrder`, specified on lexicographic keys with a rational component, is `KernelPath.totalOrder` for every pair of data: the classes by constructor and sign, two finite data of one sign by the kernel comparison and then by their quantum exponents, two NaNs of one sign by signaling state and payload. `Datum.totalOrderMag` is unfolded to it. |
| `KernelPath.extremum_eq`, `KernelPath.selectExtremum_eq`, `KernelPath.selectByMagnitude_eq` | The kernel path of the eight decimal minimum and maximum operations (§9.6): `Arithmetic.extremum` is `KernelPath.extremum` for every format, selection and pair of data, value and flags. Two data that are not NaNs are selected with the kernel comparison, operands of equal value are ordered by the kernel total order, and a NaN operand is left to the specification. |
| `KernelPath.remainder_eq`, `KernelPath.remainderFinite_eq` | The kernel path of decimal `remainder` (§5.3.1): the two coefficients are put on their common quantum by powers of ten and the nearest integer quotient, ties to even, is decided by three comparisons of natural numbers. `Arithmetic.remainder f x y = KernelPath.remainder f x y` for every format and all data. |
| `KernelPath.rootn_eq`, `KernelPath.rootRatio_eq`, `KernelPath.rootIncrement_eq`, `KernelPath.evenDegree_eq` | The kernel path of the decimal root of integer degree (§9.2): the radicand, or its reciprocal for a negative degree, is a ratio of natural numbers on the grid `10 ^ (degree × minQuantum)`, the integer root is `Numerics.IntegerRoot.newton`, and comparisons of natural numbers decide the increment, the `inexact` flag and the tininess. `rootRatio` is `rootMagnitude` for every format, direction, sign, degree, numerator, nonzero denominator and preferred exponent, and `Arithmetic.rootn f mode x n = KernelPath.rootn f mode x n` for every datum and degree. |
| `KernelPath.encodeDecimal_eq`, `decodeDecimal_eq`, `encodeBinary_eq`, `decodeBinary_eq`, `KernelPath.encode?_eq`, `decode_eq`, `valid_eq`, `encodeDeclet_eq`, `decodeDeclet_eq` | The kernel path of the encoding operations (§5.5.2): the interchange word of a valid datum as a natural number, and the datum of a word, with the fields cut by divisions and remainders and the declets packed by arithmetic on three digits, in the decimal and in the binary encoding of the significand. Equal to the reference codecs for every format, datum and word. |
| `KernelPath.formatExact_eq`, `KernelPath.parse_eq`, `KernelPath.characters_eq`, `KernelPath.convert_eq` | The kernel path of the decimal conversions to and from character sequences (§5.12): `Formatting.formatExact x` is `String.ofList` of the characters of the datum, written by the digit loop of `Numerics.Kernel.Text`, and `Formatting.parse f mode text` is the kernel form on the characters of the text, which rounds a finite datum with `KernelPath.project`. For every format, direction, datum and string. |
| `Arithmetic.scale_quantum_closest` | Exact scaling chooses the cohort quantum closest to the shifted input quantum. |
| `Arithmetic.logB_bounds`, `Arithmetic.logB_eq_of_equal_magnitude` | The finite exponent query bounds the input by consecutive powers of ten and is unchanged by cohort or sign. |
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
| `Arithmetic.square_valid`, `pown_valid`, `rSqrt_valid`, `hypot_valid`, `rootn_valid` | The delivered datum is valid for the destination format. |
| `Arithmetic.rootn_degree_zero` | Degree zero returns a canonical quiet NaN and raises invalid for every input, including NaNs. |
| `Arithmetic.square_error_le_half`, `pown_error_le_half`, `rSqrt_error_le_half`, `hypot_error_le_half`, `rootn_error_le_half` | A finite nearest-rounded result is within half the selected decimal grid step of the exact real expression, under its domain hypotheses. |
| `Arithmetic.rootn_error_lt_one` | For a finite nonzero input and a nonzero degree in the real domain, every rounding mode has error strictly less than one selected grid step when no overflow occurs. |
| `Arithmetic.rootn_down_le`, `le_rootn_up` | Directed roots lie on their requested side of the exact root when no overflow occurs. |
| `Arithmetic.rootn_inexact_iff`, `rootn_underflow_iff` | Root status records numerical inexactness and tininess before rounding. |
| `Arithmetic.integerRoot_pow_natAbs` | The real root specification satisfies its defining power equation, using the reciprocal operand for a negative degree. |

Stable `expm1` and `logp1` and their correctness theorems come from the optional import
`FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof`. In its
`Transcendentals.Certified` namespace, `toReal_of_expm1_eq_some` and
`toReal_of_logp1_eq_some` identify a successful result with nearest-even rounding of
`Real.exp x - 1` and `Real.log (1 + x)`. A returned datum is valid and finite, and valid signed
zeros keep their quantum. An inconclusive enclosure or an invalid domain returns `none`. This is
partial correctness: no theorem says which inputs succeed, except that a valid signed zero passes
through (`expm1_of_isZero`, `logp1_of_isZero`).

The same import has the 26 functions of one argument that IEEE 754-2019 §9.2 recommends, as
`Transcendentals.Certified.exp2`, `sin`, `atanh` and so on (the names of ISO/IEC 9899:2024
Table F.2), the members of `Transcendentals.Certified.apply` over the enumeration that the
binary formats use, and `exp`, `log`, `powr` and `compound`. A function returns a result when an enclosure of `Numerics.Interval` on a
binary grid settles the nearest-even rounding, and `none` otherwise. This is partial
correctness too.

| Theorem | Informal statement |
| --- | --- |
| `Transcendentals.Certified.toReal_of_apply_eq_some` | **A certified decimal function is correctly rounded.** For every format, every member of the enumeration and every operand, a returned result has the real value `roundAt f` of the real function at the real value of the operand. |
| `Transcendentals.Certified.error_le_half_ulp_of_apply_eq_some` | A returned result is within half a decimal unit in the last place of the real function. |
| `Transcendentals.Certified.valid_of_apply_eq_some`, `isFinite_of_apply_eq_some` | A returned result is valid in the format and finite. |
| `Transcendentals.Certified.toReal_of_unary_eq_some`, `valid_of_unary_eq_some`, `isFinite_of_unary_eq_some`, `unary_cases` | The same three facts for `unary`, the certified function of one operand that an expression gives: for an expression that denotes a real function wherever it is given, a returned result is valid, finite and the nearest-even rounding of that function at the operand. Every certified decimal function of this section is `unary` at its expression. |
| `Transcendentals.Certified.toReal_of_exp_eq_some`, `toReal_of_log_eq_some`, `toReal_of_compound_eq_some`, `toReal_of_powr_eq_some` | A returned `exp`, `log`, `compound` or `powr` is `roundAt f` of `Real.exp x`, `Real.log x`, `(1 + x) ^ n` or `x ^ y` at the real values of the operands. |
| `Transcendentals.Certified.apply_cases`, `exists_enclosure_of_settle_eq_some`, `zero_facts` | A result of `apply` is a valid zero operand of a function that is zero at zero, returned unchanged, or a result of `unary`; an enclosure that settles contains the number its expression denotes. |

The import `FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Proof`
has the functions of §9.2 as total functions: `Transcendentals.CorrectlyRounded.exp2`, `sin`,
`atanh` and the other members of `apply`, `exp`, `expm1`, `log`, `logp1`, `powr`, `pow`,
`compound`, `atan2` and `atan2Pi`. Each returns an `Outcome`, the datum with its exception
flags, for every operand, every decimal format and each of the five rounding directions. The
rule tables are those of the binary functions, and a real result is rounded once by
`ComparisonRounding.round`, the decimal rounding from an exact comparator: a bisection over the
quantum exponents, a bisection over the coefficients, and the guard and sticky bits of the
cell. A rational enclosure only saves comparisons. The result has the least possible quantum
exponent, and an operand that is a zero of a function with `f (±0) = ±0` is returned with its
quantum exponent.

| Theorem | Informal statement |
| --- | --- |
| `ComparisonRounding.round_roundsTo`, `roundMagnitude_roundsTo`, `Located.round_roundsTo`, `locate_spec` | **Decimal rounding from an exact comparator is correct in five directions, with flags.** For every format, direction and comparator of a nonzero real number `x`, the outcome meets `RoundsTo f mode x`: with `roundTo f mode x` the rounding of `x` on the decimal grid with an unbounded quantum range, when that value is at most the largest finite magnitude the datum is finite, valid, has the sign of `x` and denotes it, `inexact` is raised exactly when it differs from `x`, `underflow` exactly when moreover `x` is below the least normal magnitude, and no other flag; beyond it the outcome is the overflow result of the direction with `overflow` and `inexact`. |
| `ComparisonRounding.deliver_roundsTo`, `deliver_of_eq_zero`, `within_eq`, `round_of_eq_zero` | The contract through the rules: a rule that locates a nonzero real number delivers its rounding with any enclosure that contains it, an enclosure does not change a comparator's answers, and a rule that locates zero delivers `+0` with the least quantum exponent. |
| `Transcendentals.CorrectlyRounded.apply_roundsTo`, `apply_zero` | **The 26 decimal functions of one argument are correctly rounded with flags in five directions**, for every format and every finite operand in the domain with a nonzero real value; a zero operand of a function with `f (±0) = ±0` is returned unchanged. |
| `Transcendentals.CorrectlyRounded.exp_roundsTo`, `expm1_roundsTo`, `log_roundsTo`, `logp1_roundsTo`, `powr_roundsTo`, `compound_roundsTo` | The same contract for `exp`, `expm1`, `log`, `logp1`, `powr` at a positive base and `compound` above -1. |
| `Transcendentals.CorrectlyRounded.pow_roundsTo_of_pos`, `pow_roundsTo_of_neg`, `atan2_roundsTo`, `atan2Pi_roundsTo` | The same contract for `pow` at a positive base, `pow` at a negative base with an integral exponent, and the two angles at a nonzero `y`. |
| `Transcendentals.CorrectlyRounded.contains_enclosure`, `contains_of_enclose`, `contains_enclosePower`, `contains_encloseExp` | The enclosures that save comparisons contain the real value: the expression on an adaptive binary grid, a power with its exponent split into an integer and a rest, and an exponential with its argument split. |

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
| `Model.exp_eq_real`, `Model.expMinus1_eq_real` | The result is the standard posit rounding of the exact real exponential, with subtraction performed before rounding for `expm1`. |
| `Model.log_eq_real`, `Model.logPlus1_eq_real` | Positive logarithm arguments are rounded from their exact real values; `logp1` adds one exactly first. |
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
terminates because it separates irrational targets from rational boundaries, while exact rational
cases are handled directly.

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

## Embedded C fixed point

Import `FloatLib.Floats.Formats.FixedPoint.Embedded.Roundoff` and open
`FloatLib.Floats.Formats.FixedPoint.Embedded`.
The source is WG14 N1169, labelled ISO/IEC TR 18037:2006(E), §§4.1.1–4.1.9
and proposed C clauses 6.2.6.3, 6.3.1.3a, 6.3.1.8, 7.18a.6 and 7.19.6.1–2.
This is the inspected committee draft, not the published 2008 text.
Annex G item 2 specifies that rounding precedes overflow handling.

| Theorem | Informal statement |
| --- | --- |
| `ofBits_toBits`, `toBits_ofBits` | Every signed or unsigned coefficient grid has exact word round trips, at arbitrary integral and fractional widths. |
| `fxbits_eq_some_iff`, `bitsfx_eq_scaled` | Coefficient conversion succeeds exactly at the stored coefficient; the coefficient is the decoded value times `2^F`. |
| `convert_eq_some_iff`, `convert_eq_none_iff` | Every adjacent rounding policy gives the complete result, including saturation and undefined unsaturated overflow of the rounded coefficient. |
| `convert_adjacent`, `convert_decode`, `convert_below`, `convert_above` | In-range conversion chooses the adjacent grid value, preserves stored values, and saturates outside either endpoint. |
| `Arithmetic.apply_eq_some_iff`, `Layout.evaluate_eq_some_iff` | Ordinary exact arithmetic followed by conversion; usual type evaluation performs the required preliminary conversions and the selected arithmetic policy. |
| `Arithmetic.applyWith_allowed`, `Format.unitProduct_closest` | Every implementation policy selects a permitted ordinary, neighboring, or inward-unit result; the exceptional unit value is the closest on its strict side. |
| `Arithmetic.applyWith_error_le`, `Arithmetic.applyWith_mixedError` | Every admitted arithmetic policy has error at most two grid steps plus clipping, also available as a `roundoff` contract. |
| `roundCoefficient_nearest`, `roundfx_low_bits`, `roundfx_error_le_half` | Coarse rounding is nearest, has zero low bits before saturation, and stays within half a coarse step even after saturation. |
| `countlsfx_in_range`, `le_countlsfx`, `countlsfx_eq_direct` | The returned shift is globally greatest for a nonzero coefficient; a proved logarithm formula implements the search. Zero returns the value precision. |
| `convert_coefficient`, `Unary.neg_eq_coefficient`, `Unary.update_eq_coefficient`, `shift_eq_coefficient` | Exact scale cancellation gives coefficient conversion, negation, updates and shifts at every width, preserving all rounding and overflow choices. |
| `Arithmetic.applyWith_add_codes`, `Arithmetic.applyWith_sub_codes` | Every admissible precision policy gives integer addition or subtraction on a common grid, followed by the same overflow step. |
| `convert_error_le_one`, `convert_nearest_error_le_half` | Adjacent and nearest conversion have one-step and half-step error bounds, with an explicit clipping term. |
| `convert_mixedError`, `convert_nearest_mixedError`, `roundfx_mixedError` | The rational error bounds embed into real contracts registered for `roundoff`. |
| `Layout.example_valid`, `Layout.example_recommended` | One concrete layout satisfies every mandatory and recommended precision relationship. |
| `Arithmetic.assignInteger_eq_some_iff` | Integer compound assignment first rounds its fixed intermediate, then truncates into the destination integer range. |
| `Format.minimum_le`, `Format.le_maximum`, `Format.epsilon_le` | Every stored value lies between the named endpoints; epsilon is the least positive stored value at positive precision. |
| `Layout.precision_pos`, `Format.bitsInteger_inRange` | Every valid layout has positive precision, and every associated integer width contains every coefficient. |
| `Text.scan_eq_some_iff`, `Text.scan_eq_none_iff` | A successful scan consumes the greatest accepted subject prefix after whitespace; failure rejects every prefix. |
| `Text.convert_value_spec`, `Text.convert_outcomes`, `Text.convert_mixedError` | Text conversion refines shared saturated conversion, preserves the end/range outcomes, and admits its one-step-plus-clipping `roundoff` bound. |
| `Constant.translate_fract_one`, `Constant.translate_eq_none_iff` | N1169 C 6.4.4.2a's exact range constraint and separate fract-one maximum are independent of the translation policy. |
| `Constant.rounded_hexadecimal`, `Constant.rounded_decimal_distance` | Hexadecimal translation follows the specified rounding mode; decimal translation selects a nearest coefficient or a stored neighbor, as inherited from N1256 C 6.4.4.2. |
| `Constant.translate_error_le`, `Constant.translate_mixedError` | Every accepted constant has error at most three halves of a grid step, including the fract-one case, and the bound composes through `roundoff`. |
| `Formatted.decimal_toRat`, `Formatted.parse_decimal_fixed` | The formatted numeric core parses to the chosen integer coefficient divided by the requested decimal power. |
| `Formatted.decimal_error_le_one`, `Formatted.decimal_error_le_half`, `Formatted.decimal_mixedError` | Output conversion has one decimal-step error for adjacent rounding, or half a step for nearest rounding, with a registered real contract. |
| `Text.subject_has_completion_iff`, `Formatted.item_eq_some_iff_has_completion`, `Formatted.le_item_length_of_completion`, `Formatted.scan_consumed` | N1169 C 7.19.6.2: an input item is recognized exactly when it has a complete numeric continuation; scanning consumes a maximal such prefix after whitespace, for arbitrary character-list lengths. |
| `Formatted.scan_incomplete`, `Formatted.scan_value_eq_some_iff` | Incomplete nonempty items are consumed and fail; successful scans have exactly the parsed and rounded coefficient. |
| `Formatted.scanValue_eq_none_iff`, `Formatted.scanValue_mixedError` | Formatted input is undefined exactly when its rounded coefficient is out of range; successful primary-type conversion has the common one-step-plus-clipping bound. |

The 98 stdfix function spellings are generated from shared schemas in
`Standard.lean`, with compiled reference certificates and kernel registrations.
`Embedded.Examples` evaluates every generated spelling (the limit macros, the
associated integer types, the functions of each type and the operators) at
`Layout.example` by Lean's kernel, one theorem per clause of N1169.
`countlsfx` additionally uses the proved direct logarithm path. Negation,
updates and shifts have compiled coefficient replacements. Same-grid addition
and subtraction have kernel coefficient equations for every admitted policy.
Fallback defining equations preserve these direct rules during kernel rewriting.
The independent corpora cover 8,258,066 observations, including 1,310,720
Clang fixed-point comparisons; the universal theorems are not limited to those widths.
An additional 9,699,264 Fraction observations check six ordinary, relaxed and
inward-unit policies across all pairs at widths one through six.
The 48 precision macros and 12 integer typedef descriptors share the same
arbitrary-layout definitions. Another 7,462,248 Fraction observations check
limits, associated integer ranges and directed integer comparisons and assignments.
Another 6,179,175 observations check all twelve numeric text conversions against
an independent regular-expression/Fraction oracle. This covers the C locale
and maximal-prefix behavior, with explicit range and end-pointer outcomes.
Constant translation passes 1,881,909 independent observations, including the
distinct decimal and hexadecimal rounding rules. Single resolved `fprintf`
and `fscanf` conversions pass 35,513,511 DFA/Fraction comparisons covering flags,
widths, precision, incomplete input and numeric outcomes. Whole formatted
streams, whole format-string parsing and ABI object layout remain
separate obligations.

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

Import `FloatLib.Floats.Formats.Block` for block-scaled formats. One definition covers them all:
a `Block.Format` has an element format for each position and a list of scale levels, outermost
first, each with its groups (the block shape, or a tensor, row, expert or token for an outer
scale), its scale format and its scale-selection rule. `Block.Rounding K` is the value a scalar
format stores for an exact input, over any ordered field `K`. The following names are in `Block`,
and hold for every element format, scale format, level structure and selection rule that meets the
stated premise:

| Theorem | Informal statement |
| --- | --- |
| `Format.reconstruct_eq` | Each reconstructed element is one rounding of its input in the element format scaled by the element's total scale. |
| `Format.abs_reconstruct_sub_le` | With element budget `(u, η, M)` and total scale `σ`, the error is at most `u * abs x + σ * η + max 0 (abs x - σ * M)`. |
| `Format.abs_reconstruct_sub_le_abs` | The same budget with `abs σ`, with no condition on the scale, zero included. |
| `Format.sum_abs_reconstruct_sub_le` | The same budget summed over a block or any set of elements. |
| `Format.abs_reconstruct_sub_le_of_max` | If the scale lies between `c₁` and `c₂` times `amax / target` and nothing saturates, the error is at most `u * abs x + c₂ * (amax / target) * η`. |
| `Format.reconstruct_eq_zero_iff_mem`, `Format.reconstruct_eq_zero_iff_abs_le` | An element is flushed to zero exactly when its scaled input is in the element format's zero set, for any rounding direction; with ties to zero this is magnitude at most `τ * σ`. |
| `roundAt_eq_zero_iff_mem`, `Rounding.saturating_round_eq_zero_iff_mem`, `Rounding.fixed_round_eq_zero_iff_mem`, `Format.reconstruct_eq_zero_iff_of_mode`, `Format.e2m1_reconstruct_eq_zero_iff` | The zero set of every binary descriptor and fixed-point grid in each of the six rounding directions (`modeZeroSet`, in units of the least subnormal or the step), and the flush-to-zero rule it gives a block format: for E2M1 with total scale `σ`, `abs x ≤ σ / 4` with ties to even, `abs x < σ / 4` with ties away, `abs x < σ / 2` toward zero. |
| `abs_div_scale_le`, `le_div_scale`, `ofMax_abs_div_scale_le` | A scale of at least `c` times `amax / target` keeps every scaled magnitude at most `target / c`; a scale of at most `c` times it scales the maximum to at least `target / c`. |
| `total_append_ofMax` | Under outer scales with constant product `o` on a block, the block's effective scale is one rounding of `amax / target` in the scale format scaled by `o`. |
| `ofCandidates_error_le` | The target kept among candidates has the least measured error among them. |
| `Format.reconstruct_relabel`, `reconstruct_transpose`, `nvfp4_reconstruct_transpose`, `fourOverSix_reconstruct_transpose` | Relabelling positions commutes with quantization when every level selects the relabelled scales; transposition exchanges the tile sizes. |
| `Rounding.Nearest.round_eq_left`, `Rounding.Nearest.round_eq_right`, `Rounding.Nearest.round_eq_of_ge`, `Rounding.Nearest.round_eq_of_le`, `Rounding.saturating_nearest`, `Rounding.fixedRat_nearest` | A nearest rounding (each stored value at least as close as every other stored value) is determined between two adjacent stored values away from their midpoint, and beyond its largest and least stored values. Saturating nearest-even rounding of every binary descriptor is one, and so is rational fixed point clipped to two grid points. `Rounding.RoundsTo.round_eq` evaluates the first at a dyadic rational by integer arithmetic, and `Rounding.fixed_round_ratCast` identifies real fixed point on rationals with the rational computation `Rounding.fixedRat`. |
| `Format.reconstruct_ratCast`, `total_ratCast`, `Level.ofMax_scale_ratCast`, `Codec.ofFormat_round_eq_grid`, `Rounding.pow2Floor_round_ratCast` | A format over the rationals and a format over the reals reconstruct the same values when their levels select the same scales at the data (`LiftsAt`) and their element formats round alike. A largest-magnitude level lifts when its scale format does; the codec of an IEEE descriptor is the real grid rounding inside its finite range; rounding down to a power of two commutes with the cast. |
| `sum_decode_mul_decode` | A dot product of decoded operands is the sum over blocks of the two block scales times the dot product of the stored elements. |
| `abs_foldl_round_sub_le`, `abs_accumulate_sub_le`, `abs_accumulateChunked_sub_le` | Ordered accumulation of `n` terms in an accumulator with budget `(u, η)` has error at most `((1 + u) ^ n - 1) * ∑ abs t + n * (1 + u) ^ n * η`, with propagated term errors, and with promotion of a narrow accumulator every `k` terms. |
| `kernelEntry_eq_accumulateChunked`, `abs_kernelEntry_sub_le` | The blocked dot product `BlockedDot.kernelEntry` from zero, with its fused multiply-add rounded in `N` and its addition in `W`, is accumulation with promotion over the products of its blocks, and differs from the exact dot product of `n` terms in `m` blocks of width `w` by at most `((1 + u_W) ^ m * (1 + u_N) ^ w - 1) * ∑ abs (a k * b k) + m * (1 + u_W) ^ m * (w * (1 + u_N) ^ w * η_N + η_W)`. |
| `accumulate_eq_eval`, `accumulate_scaled`, `abs_accumulate_sub_accumulate_le_of_perm` | Ordered accumulation is the left chain of `ReductionTree` (`ReductionTree.eval_leftChain`), so it commutes with scaling the format; two orders of the same terms differ by at most twice the accumulation bound. |
| `Rounding.saturating_budget`, `Rounding.fixed_budget`, `roundAt_eq_zero_iff` | Every binary descriptor and fixed-point grid is a rounding map over the reals, with its budget and its zero set. |
| `mx_scaled_max`, `mx_abs_reconstruct_sub_le`, `nvfp4_abs_scale_sub_le`, `nvfp4_abs_reconstruct_sub_le_of_scale`, `nvfp4_reconstruct_eq_zero_iff` | The instances: OCP MX puts the block maximum in the binade of `2 ^ emax`, and its element error bound has no premise on the data; NVFP4's stored scale differs from `amax / 6` by at most a sixteenth of it plus the E4M3 range terms; with a scale within a relative `ε` of `amax / 6` the element error is at most `abs x / 4 + (1 + ε) * amax / 24 + ε * amax`; NVFP4 flushes magnitudes up to a quarter of the block scale. |
| `Format.quantizeWith`, `Format.abs_reconstructWith_sub_le`, `Format.abs_reconstructWith_mul_sub_le`, `Format.quantizeWith_eq_quantize`, `Rounding.Accurate.abs_round_mul_sub_le`, `Rounding.Nearest.round_eq_round`, `nvfp4_abs_reconstructWith_sub_le`, `nvfp4_quantizeWith_eq_quantize` | Quantizers that compute the scaled input in a working arithmetic (`Block.Working`), for every element format, level structure and scale selection: if the computed scaled input is within `δ * abs (x / σ) + θ` of the exact one, the element error is at most `(u * (1 + δ) + δ) * abs x + σ * (η + (1 + u) * θ) + max 0 ((1 + δ) * abs x + σ * θ - σ * M)`; one rounded product with a reciprocal scale of relative error `ρ` gives `δ = (1 + ε) * (1 + ρ) - 1`; and a nearest element format stores the computed input as the exact one when both lie between two adjacent element values and differ by less than the distance of the exact one to their midpoint. The NVFP4 instances are E2M1 elements with binary32 products in the order of torchao's `nvfp4_quantize`. Real and rational values only: no overflow of the working arithmetic, and no bit-level binary32 implementation. |
| `Working.Quantizer`, `Working.div_eq_round_or_inf`, `Working.mul_eq_round_or_inf`, `Working.Quantizer.toReal_scale`, `Working.Quantizer.toReal_element`, `Working.Quantizer.reciprocal_eq`, `Working.Quantizer.abs_element_sub_le`, `nvfp4Working`, `nvfp4Working_toReal_scale`, `nvfp4Working_toReal_element`, `nvfp4Working_abs_element_sub_le`, `Working.KernelPath.words_eq` | The quantizer on the encodings of a binary working format (`Block.Working.Binary`), in the order of torchao's `nvfp4_quantize`, for every IEEE working format, scale format and element format, with the machine's overflow. One quotient or product of finite operands is the exact result rounded once, or the infinity with its sign. For a finite block and a finite positive outer scale, the stored scale is the scale format's rounding of `g (g (amax / target) / outer)` clamped to `[floor, ceiling]`, and for a finite reciprocal `r` a stored element is the element format's saturating rounding of `g (x * r)` clamped to the target, with `g` the rounding onto the working grid: both hold when the quotient or the product overflows, because the clamp sends the infinity where the formula sends a number beyond the largest finite value. A reciprocal is finite and equal to `g (g (1 / outer) / s)`, or `+∞`. With a finite reciprocal the error of an element is the budget of `Format.abs_reconstructWith_sub_le` at `δ = (1 + u) * (1 + ρ) - 1`, `ρ = (1 + u) * (1 + (u + θ * o)) - 1 + θ * σ`. `nvfp4Working` is binary32, E4M3 and E2M1 with the constants `6`, `2 ^ -6` and `448`. The kernel rules compute the words of a block on natural numbers. Not covered: a NaN operand, and a zero element under a reciprocal that overflowed (`0 * ∞`). |
| `signedFixed_budget`, `combine_abs_reconstruct_sub_le`, `combine_abs_reconstruct_sub_le_of_ceil`, `combine_reconstruct_eq_zero_iff` | The fixed-point combine format: half a step of error times the block scale; with the scale rounded up to a power of two and the largest element value as target nothing saturates and the error is at most `2 ^ (-frac)` times `amax / target` (`amax / 127` for S2F6); magnitudes up to half a step times the block scale are flushed. |
| `CodedFormat.value_quantize` | The stored codes of the executable quantizer have the values of the value theory, for every codec and policy. |
| `Reference.quantize`, `Reference.decode` | Certified compiled reference paths and kernel unfolding registrations for every stored-tensor codec, grouping and policy. The quantizer's reconstruction theorem and the decoder's exceptional behavior are unchanged. |
| `Tensor.decode_finite`, `Tensor.decode_infinity`, `Tensor.decode_of_not_isFinite` | Exact decoding: the closed product of the element and its total scale under finite scales, and NaN under a scale with no finite value. |
| `Tensor.abs_toReal_Dot_sub_le` | A finite dot of stored tensors into an IEEE descriptor is one rounding of the exact sum: at most half an ulp. |

The test module `Conformance/Formats/BlockExamples.lean` has kernel-checked instances on explicit
data: the values NVFP4 and MXFP4 flush
around one outlier for `1 × 16`, `1 × 32` and `16 × 16` blocks, a matrix whose `1 × 16`
quantization does not commute with transposition, and a block for which neither Four Over Six
candidate is the best scale. They cover those data only.

Import `FloatLib.Floats.Formats.Block.Roundoff` to have `roundoff` use these budgets. The rules
`Format.reconstruct_mixedError`, `accumulate_mixedError` and `accumulateChunked_mixedError` bound
a quantized element, an ordered accumulation and an accumulation with promotion, for every element
or accumulator format with a `Rounding.HasBudget` or `Rounding.HasAccumulatorBudget` instance
(every binary descriptor, fixed point, or a budget given as a hypothesis). The rule for an element
has no premise. `Format.quantize_mixedError` states the same budget for a stored element against
its exact scaled input. A kernel on stored element words and scale words takes it as a hypothesis
on its operands, and `roundoff` then bounds the kernel against the exact scaled inputs. Scale
selection in a finite working precision is not covered.

For NVFP4, the exact source is NVIDIA, *Pretraining Large Language Models with
NVFP4*, arXiv:2509.25149v2, Appendix B.1–B.3 (vendor description, not a standard).
The independent oracle records 445,793 exact observations with no mismatches:
gfloat/Fraction/MPFR for the rational policies, and CPU torchao 0.18.0 for
`nvfp4Working`, the quantizer on binary32 encodings. That quantizer has a floor
of `2^-6` on local scales and rounds its intermediate arithmetic in binary32.
With the same floor, the exact policy's codes differ from it in 18 single-level
and 368 two-level observations in this corpus, each within `2^-20` of a rounding
tie of the scaled input, where the exact policy rounds the exact quotient once.
Those are different contracts: no theorem states the binary32 quantizer equal to
the rational policy, and none is about a hardware GEMM. A second oracle compares
`nvfp4Working` with the processor's binary32 arithmetic on 271,932 words, among
them the tensors in which a quotient or a product overflows, with no mismatch.

For the six concrete OCP MX profiles, import `FloatLib.Floats.Formats.OCP.MX`. `Standard.format`
is their storage format in the general block format and `Standard.policy` the scale selection of
§6.3. The following names are in `OCP.MX.Standard`:

OCP MX v1.0, §5.3: `Element.Compiled.quantizeFinite_eq` proves the existing
natural-number bisection equal to the finite argmin for every profile and signed
rational input. `Element.Compiled.quantize_eq` lifts it through the exceptional
dispatcher for both overflow policies. Their compiler certificates and `csimp`
equations install the bisection in direct scalar calls and the block codecs.
Scalar medians are 1.744–6.161 µs per conversion; this does not establish
the same cost for a block or for kernel evaluation.

| Theorem | Informal statement |
| --- | --- |
| `format_elements_quantize` | Each stored element follows the element contract of §5.3 at its exact scaled input, under SAT or OVF. |
| `Profile.codec_budget`, `Profile.codec_round_eq_zero_iff`, `Profile.abs_value_quantize_sub_le_budget`, `Profile.value_quantize_eq_zero_iff` | On exact rationals the element codec of each profile has relative error `2 ^ (-precision)` (zero for INT8), absolute error half the least positive element value, saturation at the largest element value, and stores exactly the magnitudes up to half the least positive value as zero. So the stored codes of every block format with these elements have the element error bound and the flush-to-zero rule of the value theory (NVFP4 storage: `Block.nvfp4Stored_abs_value_sub_le_budget`, `Block.nvfp4Stored_value_eq_zero_iff`). |
| `Profile.codec_round_eq_real`, `Profile.value_quantize_eq_real`, `Block.nvfp4Stored_value_eq_saturating`, `Block.int8_value_eq_signedFixed` | For each of the six profiles the executable codec with SAT is, on every rational, the real rounding `Profile.real` of the value theory: `Block.Rounding.saturating` of the descriptor for E5M2, E4M3, E3M2, E2M3 and E2M1, and nearest-even fixed point clipped to `[-2, 127 / 64]` (S2F6, `Block.Rounding.signedFixed 2 6`) for INT8. So in every block format with these elements, for every level structure and policy, the stored value is that real rounding of the input at the stored scale, and the theorems about the real rounding hold for the codes. |
| `Block.nvfp4Stored_value_eq_reconstruct`, `Block.mx_value_eq_reconstruct`, `Block.mxMaxCeil_value_eq_reconstruct`, `Block.combine_value_eq_reconstruct` | The executable quantizers compute the real formats. Stored NVFP4 with NVIDIA's selection has, at every position, the value the real format `Block.nvfp4` reconstructs, when the ideal outer scales are inside binary32's finite range. Stored OCP MX with the standard selection has the values of the real format `Block.mx` with the profile's real element rounding, for each of the six profiles and every block size, when the scale exponents do not exceed `127`. Both premises hold for every tensor of magnitudes below `2 ^ 128`, so for every tensor of finite binary32 values (`nvfp4Stored_value_eq_reconstruct_of_lt`, `mx_value_eq_reconstruct_of_lt`). With the scale rounded up to a power of two (`Block.mxCeil`, `Block.mxMaxCeil`), stored MX of every profile has the values of the real format with the scale format `Block.Rounding.pow2Ceil`, for every rational tensor (`Block.mxMaxCeil_value_eq_reconstruct`); the combine format with S2F6 elements is the case `Block.combine`. So the theorems about these real formats (scale bounds, block-maximum bounds, transposition, the flush-to-zero counts) hold for the stored values. |
| `Profile.toReal_ofNatBits`, `Profile.encode_mixedError` | The binary word with the bits of a stored element code of a floating profile has the code's value, and it approximates the encoded input with relative error `Profile.unitRoundoff` and absolute error `Profile.zeroThreshold` plus the excess over the largest element value, stated as a `MixedError`. A `roundoff` bound for a kernel on stored words that takes this as a hypothesis on its operands is then a bound against the exact scaled inputs of the stored tensors, for every policy. |
| `Profile.codec_round_eq_of_nearest`, `Profile.codec_round_midpoint` | A nearest rounding over any ordered field that agrees with a profile's codec at the values of its finite words, at the midpoints of adjacent words and beyond the two ends is the codec on every rational. At a midpoint the codec stores the value of the word with the even code. The kernel checks these premises for the real roundings on the word lists (`Profile.midpointsAgree`). |
| `Profile.abs_value_quantize_sub_le`, `abs_value_quantize_sub_le` | With SAT, each stored element minimizes absolute error among finite element words at the selected scale: for every block format whose elements round as the profile's codec (NVFP4 storage through `Block.nvfp4Stored_abs_value_sub_le`), and for OCP MX. |
| `toFormat_format` | With the standard policy, the format is one largest-magnitude level over E8M0, so the general scale-selection theorems apply. |
| `Tensor.isFinite_iff`, `Tensor.decode_finite`, `Tensor.decode_of_nan_scale` | A block is finite exactly when its scale is not the NaN code; a finite element decodes to its value times `2 ^ exponent`. |

Dot products accept different element formats on their two sides. `OCP.MX.Dot` and
`DotGeneral` accept an explicit `Block.Reduction`, including exact intermediates and
actual binary-word intermediates. The default is exact. The scale-selection theorems
don't claim global optimality over other shared scales.

OCP MX v1.0, §§6.1–6.2 names the operations `Dot` and `DotGeneral`.
`OCP.MX.DotGeneral` reduces an ordered list of blocks with one final rounding;
`Block.Tensor.toReal_DotGeneral_eq_roundAt` identifies its real value with the
rounding of the sum of block sums. The theorem covers any operand codecs,
scale levels, block counts, block lengths, order and IEEE output descriptor,
assuming finite decoded operands and result. The standard's padded blocks
and recommended binary32 output are instances.
`Block.Tensor.Dot_rounding` and `DotGeneral_rounding` register the resulting
mixed error in `roundoff`: relative error `unitRoundoffAt` and absolute
error `underflowErrorAt` against the decoded stored operands. The checked
clients first expose the proved bound as a local contract; automatic discovery
of stored `Tensor.value` observations remains open. Error relative
to inputs before quantization requires their separate quantization budgets.
Compiled certificates and kernel unfold registrations are reference paths;
they do not assert a faster algorithm.

For finite binary intermediates, `Block.Tensor.Dot_binary_rounding` accepts
any product projection with a proved mixed-error contract. Its concrete
nearest-even instance is `Dot_nearest_binary_rounding`; the block form is
`DotGeneral_nearest_binary_rounding`. These theorems reuse the existing
cancellation-safe finite-word summation bound and then compose final rounding.
They assume finite projected products, finite partial sums and a finite output.
Accumulator and output descriptors are independent. The block form preserves
the word state across block boundaries. The statements cover every ordered list
and stored operand codec; they do not claim vendor hardware semantics.

`Numerics.Interval α` stores arbitrary endpoint representations. Its partial arithmetic uses
`Numerics.OutwardRounding α β`: a scalar decoder and a certified partial enclosure function. Generic
corner bounds apply over any ordered field. Successful finite operations preserve containment, and
unavailable enclosures, exceptional inputs, and zero-crossing division return `none`. Concrete
binary, decimal, and posit adapters use exact rational scalar arithmetic. `Interval.ContainsReal`
interprets those rational endpoints in the reals, and the `containsReal_add?`, `containsReal_sub?`,
`containsReal_mul?`, and `containsReal_div?` theorems cover arbitrary real members, rational
inputs or otherwise. `contains_fma?` proves the ordered-field multiply-add enclosure, and
`containsReal_fma?` gives its real interpretation, with outward rounding applied only after the
product and addend are combined.

`Numerics.Interval.Expr` composes arithmetic, natural and real powers, and elementary functions. Its
`containsReal_eval?` theorem proves real containment for any backend satisfying
`Numerics.Interval.Backend.Sound`. `rational_sound`, `binaryGrid_sound`, and `ofRounding_sound`
establish this contract for exact rational endpoints, integer binary-grid endpoints, and custom
outward rounders, respectively. `Expr.check_sound` proves inequalities over a rational box,
including adaptive subdivision. `Expr.evalZero?` is the evaluation with one more rule: a product
with a factor that is exactly zero, and a quotient with such a numerator, need no enclosure of the
other operand. `containsReal_evalZero?` is its containment theorem, and it has every enclosure of
`Expr.eval?` (`Expr.evalZero?_of_eval?`). `Expr.checkZero` is the check on that evaluation. It
passes every box that `Expr.check` passes (`Expr.checkZero_of_check`), `Expr.checkZero_sound`
proves its inequalities, and the `interval` tactic uses it to produce kernel-checked proofs
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
containment, and its `toExtension_sound` theorem supplies the general contract automatically.
`Extension.Sound` connects a computable enclosure to a curried real function or constant, and
`Backend.withExtensions_sound` preserves containment when you extend any sound endpoint backend.
`@[interval_extension]` registers constant certificates or those proofs for the tactic to use.
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
the fallbacks conservative, but each soundness theorem requires its stated input hypotheses all the
same.
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
| `Flocq.sqrt_round_residual_flx` | For precision above one, the residual `x - q^2` of a nearest-rounded square root is representable. |
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
apply only to nearest rounding.

`Flocq.RoundOddPoint` fixes parity at a grid exponent you supply. `Flocq.RoundOddCanonicalPoint`
uses the result's canonical exponent, matching Flocq's `Rnd_odd_pt`. `round_odd_canonical_point_fix`
proves this contract for fixed-point grids, and `round_odd_canonical_point_of_cexp_eq` transports it
when rounding preserves the canonical exponent.

## OFP8 conversion

OCP OFP8 revision 1.0 (2023-12-01), §§5.1 and 5.2.1, calls its formats
`E4M3` and `E5M2`. `Formats.OCP.FP8.convert` reuses the shared binary
quantizer for every exact source decoder and destination descriptor.
Binary32, binary16 and bfloat16 sources, nearest-even rounding, and both
SAT and NONSAT are the standard instances.

| Theorem | Scope |
| --- | --- |
| `Formats.OCP.FP8.convert_spec` | Every result satisfies the complete shared runtime outcome specification, including failure and status fields. |
| `Formats.OCP.FP8.convert_finite` | A finite source is passed to the existing exact rational rounder with gradual underflow and the chosen overflow mode. |
| `Formats.OCP.FP8.toReal_convert_finite` | Every finite delivered result equals independent nearest-even real-grid rounding, clipped for SAT or a fully finite encoding, for all descriptors and exact source decoders. |
| `Formats.OCP.FP8.convert_sat_finite` | Every finite exact source has a successful finite SAT result whose real value is nearest-even grid rounding followed by endpoint clipping; no output-finiteness premise is required. |
| `Formats.OCP.FP8.isFinite_convert_iff`, `isFinite_convert_native_iff` | Finite-source conversion is finite exactly when the policy/encoding saturates or the magnitude of the nearest-even real-grid value is at most the finite endpoint. For NONSAT and an exceptional encoding, only the rounded-value inequality remains. |
| `Formats.OCP.FP8.convert_native_eq_overflow_of_not_isFinite` | Every nonfinite NONSAT result from a finite source is exactly the native overflow word: NaN for E4M3, signed infinity for E5M2. |
| `Formats.OCP.FP8.convert_infinity_sat` | SAT maps either infinity to maximum finite of the same sign, as in §5.2.1 Table 3. |
| `Formats.OCP.FP8.convert_infinity_nonsat` | NONSAT uses the destination's native overflow, giving NaN for E4M3 and signed infinity for E5M2. |
| `Formats.OCP.FP8.convert_nan` | A source NaN propagates to a destination NaN whenever the descriptor supports NaN; sign and payload are free in OFP8. |

The compiled reference certificate and kernel unfold registrations cover the
whole polymorphic conversion. The independent value theorem reuses the generic
rational-grid identity and the normal/carry packing theorem with a selectable
overflow endpoint. The SAT theorem removes the finite-result hypothesis
for SAT; the NONSAT theorem classifies finiteness by the rounded magnitude.
The research topics record these contracts, the exhaustive
binary16/bfloat16 tests, and two independent reference checks.
OFP8 defines conversion, not arithmetic; arithmetic on these nominal types
is a FloatLib extension.

## P3109 representation, projection, and arithmetic

Import `FloatLib.Floats.Formats.P3109`. A P3109 descriptor supplies exact representation semantics
and the interim report's v4.1 round-then-saturate projection. Ordinary `convert`, `cast`, and
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

The operation names and the new classifier follow the **unapproved P3109 interim report
v4.1 (14 September 2026)**. `ExecFloat.P3109.Class` implements §4.13.1, Table 2;
`class_eq_iff` proves every row equivalent to the returned class for every valid descriptor,
including precision one. `TotalOrder` implements §4.12.1 with independently typed operands:
NaN precedes every datum, including itself, and otherwise the operation uses exact
`CompareLessEqual`. Its branch equations cover these cases. The compiled baselines and
`Class_eq_kernel`/`TotalOrder_eq_kernel` preserve these definitions. `RoundOf` and `SatOf`
return the components of any projection policy (§4.15).

`Formats.P3109.Block` adds nonempty blocks with independently typed scales and elements.
Conversions, exact sums, products, dots, and generic unary, binary, and ternary closed rational
operations normalize at the requested result scale before one destination projection. Block roots
use P3109 destinations and handle negative result scales through signed exact roots. Stochastic
policies carry one caller-supplied word per lane.

The chapter 5 names follow v4.1, §§5.5–5.8: `ConvertFromBlock`, `ConvertToBlock`,
`ConvertToBlockMaxAbsFinite`, `BlockReduceAdd`, `BlockReduceMultiply`, `BlockDotProduct`,
and the rational `BlockOp` and `ScaledOp` families. Three arity schemas generate the
named operations; the same lane theorem covers every elementwise instance and every
independently typed source. Scaled roots use one-lane block roots at result scale one.
`Arithmetic.Scaled` registers 56 complete polymorphic operations as compiled reference
paths, using the shared `Backend.Certified.reference`, and registers their kernel
unfold rules. These are reference paths, without a speedup claim.
The report's transcendental functions beyond square roots and hypotenuse are not
provided by these schemas.

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
| `ExecFloat.P3109.toClosedRat_eq_prepared`, `projectRat_eq_prepared`, `projectSqrt_eq_prepared` | P3109 v4.1, §§4.7 and 4.10.8: shared prepared decoding and projection functions equal the existing exact stages for every valid descriptor, input, rounding mode and saturation mode, including each supplied random word. Congruence preserves arithmetic with independent source descriptors. These are execution equalities, with no additional distribution or runtime-bound claim. |
| `Formats.P3109.KernelPath.projectRat_eq`, `add_eq`, `sub_eq`, `mul_eq`, `div_eq`, `fma_eq`, `negate_eq`, `abs_eq`, `convert_eq`, `recip_eq`, `faa_eq`, `copySign_eq` and the rules `Add_eq_kernel`, `Subtract_eq_kernel`, `Multiply_eq_kernel`, `Divide_eq_kernel`, `FMA_eq_kernel`, `Negate_eq_kernel`, `Abs_eq_kernel`, `Recip_eq_kernel`, `FAA_eq_kernel`, `CopySign_eq_kernel`, `square_eq_kernel`, `convert_eq_kernel`, `ofRat_eq_kernel`, `ofNat_eq_kernel`, `ofScientific_eq_kernel`, `reference_add` to `reference_sqrt` | P3109 v4.1, §§4.7 and 4.10: the operations of `P3109.KernelPath.Core` on natural-number encodings (a class and an unnormalized ratio of natural numbers per operand, one projection that rounds to the precision, saturates and encodes) return the stored reference result, for every valid descriptor of each operand and of the destination, every rounding mode with every supplied random word, every saturation mode and every operand. The rules rewrite the public operations, the operators of one format and the literals to the flat forms of `P3109.KernelPath.Flat`. These are execution equalities, with no distribution or runtime-bound claim. |
| `Formats.P3109.KernelPath.sqrtQuantumOf_eq`, `sqrtAway_eq`, `roundSqrtRatToPrecision_eq`, `projectSqrt_eq`, `rsqrtRadicand_closed`, `hypotRadicand_closed`, `sqrt_eq`, `rsqrt_eq`, `hypot_eq` and the rules `Sqrt_eq_kernel`, `RSqrt_eq_kernel`, `Hypot_eq_kernel` | P3109 v4.1, §§4.10.8 and 4.10.14: `KernelPath.sqrt`, `rsqrt` and `hypot` on encodings store the reference `Sqrt`, `RSqrt` and `Hypot`. The root of the exact radicand, a ratio of natural numbers that need not be in lowest terms, is rounded once from an integer square root and comparisons of squares in each of the nine modes, for every supplied random word, then saturated and encoded by the last stage of the projection (`encodeRounded_eq`). Every descriptor, saturation mode and operand, with NaN for a negative radicand. |
| `Formats.P3109.KernelPath.compareLess_closed`, `compareEqual_closed`, `compareLess_eq`, `compareEqual_eq`, `compareLessEqual_eq`, `compareGreater_eq`, `compareGreaterEqual_eq`, `compare_eq` and the rules `CompareLess_eq_kernel` to `CompareGreaterEqual_eq_kernel`, `compare_eq_kernel` | P3109 v4.1, §4.12: the five comparisons of two values of independent formats, and the order behind `==` and `<`, are `KernelPath.less`, `equal` and `lessEqual` on the encodings, which compare two ratios on their cross products. False, and `none`, for a NaN operand. |
| `Formats.P3109.KernelPath.Selects`, `minimum_selects`, `maximum_selects`, `minimumMagnitude_selects`, `maximumMagnitude_selects`, `Selects.number`, `Selects.finite`, `binary_eq_extremum`, `clamp_closed`, `clamp_eq` and the rules `Minimum_eq_kernel`, `Maximum_eq_kernel`, `MinimumNumber_eq_kernel`, `MaximumNumber_eq_kernel`, `MinimumMagnitude_eq_kernel`, `MaximumMagnitude_eq_kernel`, `MinimumMagnitudeNumber_eq_kernel`, `MaximumMagnitudeNumber_eq_kernel`, `MinimumFinite_eq_kernel`, `MaximumFinite_eq_kernel`, `Clamp_eq_kernel` | P3109 v4.1, §4.11: each of the ten extrema selects, on closed values given by class, sign and ratio, the operand that `extremumSel` names from three options (minimum or maximum, by value or by magnitude, and the plain, the number or the finite variant), and a binary operation that selects this way is `KernelPath.extremum` on the encodings, projected once into the destination. `KernelPath.clamp` stores the reference clamp, NaN for a NaN operand and for reversed bounds. Every descriptor of every operand and of the destination, every rounding mode with every random word and every saturation mode. |
| `Formats.P3109.KernelPath.isZero_eq`, `isNaN_eq`, `isInfinite_eq`, `isFinite_eq`, `isSignMinus_eq`, `isNormal_eq`, `isSubnormal_eq`, `isOne_eq`, `nextGreaterThan_eq`, `nextLessThan_eq` and the rules `IsNaN_eq_kernel` to `IsOne_eq_kernel`, `NextGreaterThan_eq_kernel`, `NextLessThan_eq_kernel` | P3109 v4.1, §§4.13 and 4.16: the classification queries and the two neighbours are the kernel tests and codes of `P3109.KernelPath.Core` on the encoding, for every descriptor and every code. `IsOne` compares the numerator and the denominator of a finite code with a clear sign. Conversions into a binary format, the scaled and the block operations and the elementary functions have no flat form: the kernel evaluates them on the prepared path. |
| `Formats.P3109.KernelPath.decode_closed`, `binaryClass_eq`, `convertBinary_eq`, `Flat.convertBinary_eq` and the rule `Convert_binary_eq_kernel` | P3109 v4.1, §§4.8.1 and 4.9.1: the value that mixed arithmetic reads from a binary interchange value is the closed value of its encoding, read with shifts and masks: the exact value of a finite word with the sign of a zero dropped, an infinity with its sign, and the one NaN for every NaN, for every binary format descriptor, IEEE or not. `Mixed.Convert` of such a value into a P3109 format stores `convertBinary` of the encoding, for every destination descriptor, rounding mode, random word and saturation mode. |
| `Formats.P3109.KernelPath.ClosedSource`, `binarySource`, `p3109Source`, `ratSource`, `mixedConvert_eq`, `mixedRecip_eq`, `mixedAdd_eq`, `mixedSubtract_eq`, `mixedMultiply_eq`, `mixedDivide_eq`, `mixedFMA_eq`, `mixedFAA_eq` | P3109 v4.1, §§4.8 to 4.10: mixed arithmetic on operands of any types whose exact value is the closed value of a class, a sign and a ratio of natural numbers computed from the operand (`ClosedSource`: the values of every P3109 format, of every binary interchange format, and the rationals), alike or not. Each of the eight operations stores the flat projection of the class, the sign and the ratio of its exact result, with no intermediate rounding, for every destination descriptor, rounding mode, random word and saturation mode. Each theorem is a kernel rule. An operand of a configured binary carrier has no such instance. |
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
| `Formats.P3109.Block.decode_unary_lane`, `decode_binary_lane`, `decode_ternary_lane` | For every positive block length, independent exact source types, result scale and policy, each output lane is the destination projection of the normalized exact closed operation. |
| `Formats.P3109.Arithmetic.Mixed.decode_scaledUnary`, `decode_scaledTernary`, `decode_scaledBinary` | Scaled arithmetic multiplies each source by its scale exactly, then projects the closed result once. The `scaledUnary_eq_project_div_one`, `scaledBinary_eq_project_div_one` and `scaledTernary_eq_project_div_one` theorems relate this to explicit normalization at one when the operation's results are canonical. |
| `Formats.P3109.Format.codec`, `Formats.P3109.Block.convertTo_lane`, `Formats.P3109.Block.decode_lane`, `Formats.P3109.Block.dotExact_eq` | A P3109 format is an element or scale codec of the general block format under any projection policy. Conversion to a block at a finite nonzero scale stores what the general quantizer stores, decoding under a finite scale is the general decoding, and the exact dot product of two blocks under finite scales is the general exact dot product. The report's infinite scales and its zero result scale in conversion are not instances. |
| `Formats.P3109.Block.normalize_finite`, `normalize_zero`, `normalize_infinite_finite` | Ordinary division and the report's zero/infinite-scale normalization rules hold exactly. |
| `Formats.P3109.Block.sumExact_finite`, `productExact_finite`, `dotExact_finite` | Finite reductions equal exact rational sums, products, and independently scaled dot products. |
| `Formats.P3109.Block.decode_reduceAdd`, `decode_reduceMultiply`, `decode_dotProduct` | The complete exact reduction is projected only once. |
| `Formats.P3109.BlockRoot.normalize_finite_real`, `rounded_eq_real`, `decode_project` | Normalization gives the exact scaled real root, square comparisons implement its rounding, and encoding preserves the saturated datum. |
| `Formats.P3109.Arithmetic.roundSqrtRatToPrecision_eq_real` | Integer square-root comparisons select the same precision-grid value as the real square-root rounding rule. |
| `Formats.P3109.Arithmetic.sqrt_floorLog2_eq_log`, `roundSqrtRatToPrecision_eq_report` | P3109 v4.1 §§4.7.4 and 4.10.8: the executable root quantum and dyadic result equal the independent real logarithm/floor/fraction formula for every descriptor, nonnegative rational radicand and supplied rounding word, before saturation and without a finiteness premise. |
| `Formats.P3109.Format.saturate_finite_eq_range`, `sameDatum_saturate_finite` | Saturation is the rational lower/upper endpoint test; equal finite denotations give the same saturated datum, including either representation of zero. |
| `ExecFloat.P3109.decode_sqrt_report`, `decode_rsqrt_report`, `decode_hypot_report` | Independent source and destination descriptors deliver the report projection of `√q` for `q ≥ 0`, `1/√q` for `q > 0`, and `√(x²+y²)` for finite `x,y`, respectively. |
| `Formats.P3109.BlockRoot.decode_project_normalize_report`, `Formats.P3109.Block.decode_projectRoots_report` | P3109 v4.1 §§5.4.2 and 5.7: for a nonnegative finite radicand and finite nonzero result scale `s`, each selected lane delivers the report projection of `√q/s`, for either sign of `s`, arbitrary block length and lane policy. Zero and exceptional scale contracts remain the separate closed-domain equations. |
| `Formats.P3109.Arithmetic.sqrtRoundAway_stochasticA`, `sqrtRoundAway_stochasticB`, `sqrtRoundAway_stochasticC` | Each stochastic square-root threshold agrees with the report's floor or nearest-integer formula on the exact root fraction, for every supplied word. |
| `ExecFloat.P3109.decode_sqrt` | Executable square root decodes to the declared real-root projection, including exceptional inputs. |
| `ExecFloat.P3109.decode_rsqrt` | Reciprocal square root follows the same real-root projection after exact rational inversion. |
| `ExecFloat.P3109.decode_hypot` | Hypotenuse rounds the root of the exact sum of squares once. |
| `Formats.P3109.ComparisonRounding.lowerCode_eq_referenceLower`, `referenceLower_bracket` | Exact comparison bisection selects the same capped greatest index as the real reference, with adjacent-value bracketing below its overflow sentinel. |
| `Formats.P3109.ComparisonRounding.rounded_eq_referenceRounded`, `rounded_fitsPrecisionGrid` | Exact rational-boundary comparisons reproduce the real-comparison reference and produce an encodable precision-grid datum. The clipped overflow representative is not the unrestricted precision-rounded dyadic. |
| `Formats.P3109.Format.decodePositiveFinite_succ_toRat`, `ComparisonRounding.floor_scaledTarget_eq_significand`, `decodeQuantum_eq_log` | Consecutive codes have one quantum of spacing; any uncapped positive bracket identifies the exact scaled floor and the logarithmic quantum, including precision one. |
| `Formats.P3109.Format.roundMagnitudeUp_eq_fraction`, `roundMagnitudeUp_scaled_eq_fraction` | Every one of the nine threshold decisions equals the shared fractional-part formula over real inputs, including supplied stochastic words and code parity. |
| `Formats.P3109.ComparisonRounding.referenceValue_eq_reportValue`, `value_eq_reportValue` | P3109 v4.1 §§4.7.4–4.7.5: exact comparison implements the full logarithmic precision-rounding formula after saturation, for every real input, valid descriptor and policy. The proof includes clipped overflow and unsigned formats. |
| `Numerics.FunctionExpr.prepare_eq_real` | Every domain-indexed expression compares exactly with every rational boundary; rational affine transformations do not round their child. |
| `Numerics.Softplus.compare_eq_real` | For every rational argument and boundary, the adaptive result is the ordering of `log(1+exp x)` and that boundary. The exponential-sum separation theorem proves termination. |
| `ExecFloat.P3109.decode_projectFunction`, `decode_Log`, `decode_Log2`, `decode_Softplus` and the generated function clients | P3109 v4.1 §§4.10.9–4.10.13 and §§4.10.15–4.10.16: independent source and destination descriptors reach the exact real-expression reference through one projection, for every rounding and saturation policy. |
| `Formats.P3109.Functions.finiteUnary_tanPi_of_cos_eq_zero`, `finiteUnary_tanPi_of_cos_ne_zero`, `toReal_angle` | The half-integer test exactly classifies `TanPi` poles and their signed infinities; axis and infinity angles have the report's real values. |
| `ExecFloat.P3109.decode_Exp10`, `decode_Exp2MinusOne`, `decode_Exp10MinusOne`, `decode_Log10`, `decode_Log2OnePlus`, `decode_Log10OnePlus`, `decode_Rootn`, `decode_Cbrt`, `decode_Pown`, `decode_Pow`, `decode_Powr`, `decode_Compound` | The functions of IEEE 754-2019 §9.2 that the report does not list (FloatLib extensions): each decodes to the real-expression reference through one projection, for independent source and destination descriptors and every rounding and saturation policy. |
| `Formats.P3109.Functions.exponential_finite`, `logarithmIn_of_pos`, `root_of_pos`, `root_of_neg`, `integerPower_of_ne_zero`, `power_of_pos`, `power_of_neg`, `positivePower_of_pos`, `compound_of_gt` | The real number that a finite expression of those functions denotes: `base ^ x` (less one), `logb base (x + offset)`, `x ^ (1 / degree)` and its negative for a negative operand and an odd degree, `x ^ n`, `x ^ y`, and `(1 + x) ^ n`. |
| `Formats.P3109.FunctionBlock.normalize_finite_real`, `normalize_zero`, `normalize_infinite_finite_real`, `normalize_exceptional`, `normalize_exceptional_scale` | P3109 v4.1 §5.4.2: exact real expressions divide by finite nonzero scales; zero, infinite and NaN scales follow the report's case table. |
| `Formats.P3109.Block.decode_unaryFunction_lane`, `decode_angleFunction_lane` | P3109 v4.1 §5.7: every positive block length, independent scale and element types, result scale and per-lane policy refines normalized exact function evaluation followed by the real-comparison reference. |
| `Formats.P3109.Arithmetic.Mixed.decode_scaledUnaryFunction`, `decode_scaledAngleFunction` | P3109 v4.1 §5.8: the fifty-four block/scaled public functions share two lane schemas; scaled functions use length one and exact result scale one. |
| `Formats.P3109.Block.Named.scaled`, `block`, `scaled_roots`, `scaled_functions`, `block_functions`, `scaled_angles`, `block_angles` | P3109 v4.1 §§5.7–5.8: every named scaled and block operation is checked against the generic operation it instantiates. The exact operations are evaluated by Lean's kernel on rational operands with independent scales (the roots into Binary8p4se), and each named elementary function is the generic lane and scaled theorem at its name, for every descriptor, policy, scale type and operand. |
| `Numerics.findLeast_eq_find`, `findLeastFrom_eq_find`, `findWithPrefix_eq_find` | `findLeast` is `Nat.find`, and every finite prefix length of `findWithPrefix` selects the same least witness as unrestricted `Nat.find`. The search recurses on an accessibility proof with `2 ^ 64 - 1` constructors in front of the proof that a witness exists (`accGuard`), so Lean's kernel runs it without reducing that proof, also where the proof is a theorem of another module; this changes the reduction strategy without restricting the adaptive search. |
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
The general function projector's greatest-index and exact-threshold reference is identified
with the complete logarithmic and fractional-part report formula by
`ComparisonRounding.value_eq_reportValue`, including saturation outside the stored range.
The independent Fraction/MPFR corpora provide additional finite comparisons.

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
If you only need executable rational quantization, you can import
`Numerics.Quantization.Affine` on its own.

## Theorem names and lookup

We use a few recurring names across the format families:

- `*_eq_spec` rewrites executable code to its reference definition.
- `*_refines`, `implements_*`, `spec_*`, and `preparedSpec_*` prove a relational capability.
- `toReal_*` and `toRat_*` state decoded mathematical behavior.
- `isFinite_*` establishes the side condition needed by a finite real theorem.
- `*_abs_error`, `*_relative_error`, and `*_mem_Icc` provide error or enclosure bounds.
- `*_eq_none_iff` characterizes exceptional values in optional exact views.

`#float_info YourType` lists the theorems for that type. For most configured types, such as
`Binary32`, `E4M3`, `Posit32`, or a fixed-point type, it lists the theorems about values of that
type first, such as `ExecFloat.Proof.add_notation_eq_spec` for `x + y`, and then the theorems about
each type those values reach, such as the proof model, the code, or the associated quire, with the
function that takes a value there. Other reports, such as those of P3109 types and Lean's native
floats, list their theorems under one heading, and each group's topic says what it is about.
Within a proof, Lean's `exact?`, `apply?`, and `rw?` can help you find a declaration that matches
the goal.
