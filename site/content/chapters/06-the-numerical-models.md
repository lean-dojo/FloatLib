---
number: "06"
slug: "the-numerical-models"
title: "The numerical models"
summary: "Bits, exact dyadics, and real numbers let us state different properties of the same stored value."
phases: [numerical-models, binary-format, binary-arithmetic, status-and-directed]
---

We've used addition theorems to answer two questions: which bits does the operation return, and what does that result mean as a number? The first includes the sign of zero and the choice of NaN. For the second, we can prove that the result's real value is the exact sum rounded once, provided the inputs and output are finite. A real-valued error bound cannot distinguish the two zeros or describe a NaN payload. Exact dyadics connect the finite bit patterns to real values while preserving the sign of zero.

## One word, three readings

We'll keep the stored word fixed and change only how we read it. The binary proof model is [[FloatLib.Floats.Formats.BinaryInterchange.Model]]. A value of `Model fmt` contains one field, `bits`, of type `fmt.ExecWord`, an abbreviation for `BitVec fmt.bitWidth`. The decoders give that word its meaning; no decoded value is stored alongside it:

```lean
open FloatLib.Floats.Formats.BinaryInterchange

#print Model
-- structure FloatLib.Floats.Formats.BinaryInterchange.Model (fmt : FloatFormat) : Type
-- number of parameters: 1
-- fields:
--   FloatLib.Floats.Formats.BinaryInterchange.Model.bits : fmt.ExecWord
-- constructor:
--   FloatLib.Floats.Formats.BinaryInterchange.Model.mk {fmt : FloatFormat} (bits : fmt.ExecWord) : Model fmt
```

Programs normally use `ExecFloat`. Its storage is chosen per format: a byte, a 16-, 32-, or 64-bit word, the exact-width bit vector itself above 64 bits, or an explicitly requested array of 32-bit limbs. It converts to and from `Model` through [[FloatLib.Floats.ExecFloat.Binary.toModel]] and its inverse. A single `Model` layout lets theorems quantify over all formats, while executable values can use a native word at each supported width. [Chapter 05](#/chapter/why-execution-and-proofs-are-separate) explains the proofs connecting the two representations.

The first reading is the bits themselves. [[FloatLib.Floats.Formats.BinaryInterchange.Model.signBit]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.expField]], and [[FloatLib.Floats.Formats.BinaryInterchange.Model.fracField]] extract the three IEEE fields by masking, and the classifiers [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero]], and [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]] read them according to the descriptor's exceptional-value policy.

The format descriptor specifies that policy: it is the value `fmt : FloatFormat` that every `Model fmt` is indexed by. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] records the exponent and fraction widths, the exponent bias, and an `encoding` field of type [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]] with four constructors: `ieee`, where an all-ones exponent means infinity or NaN; `finiteMaxNaN`, with no infinity, where the all-ones exponent and all-ones fraction pattern is NaN in either sign; `finiteUnsignedZero`, where the negative-zero word is the sole NaN; and `finite`, where every word is a number; [chapter 09](#/chapter/low-precision-formats-for-machine-learning) is about the three non-IEEE encodings. Carrying the bias in the descriptor is why FP8 E4M3 FNUZ and IEEE binary16 are values of the same structure. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.isIEEE]] is true exactly when the encoding is `ieee` and the bias is the conventional $2^{w-1} - 1$ for exponent width $w$; many theorems below take it as a hypothesis.

The second reading is the exact value. A finite word denotes a dyadic rational, $(-1)^s \cdot m \cdot 2^e$ with $m \in \mathbb{N}$ and $e \in \mathbb{Z}$, and [[FloatLib.Numerics.Dyadic]] stores exactly those three fields: `negative`, `significand`, and `exponent`. The sign of a zero survives in this representation because the sign is a separate field; a dyadic with `significand = 0` still remembers whether it was negative. The decoder is [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]]. It returns `none` for a NaN or an infinity and `some` for everything else, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?_isSome_eq_isFinite]] says that success is exactly finiteness. For an IEEE descriptor the rule is the usual one. A zero exponent field with a zero fraction is a signed zero. A zero exponent field with a nonzero fraction $f$ is the subnormal $f \cdot 2^{e_{\min}}$, where $e_{\min}$ is [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.minSubnormalExponent]]. A nonzero exponent field $E$ that is not all ones, with fraction $f$, is $(2^{p} + f) \cdot 2^{E - \mathrm{bias} - p}$, with $p$ the fraction width; the $2^{p}$ is the hidden leading one. For binary32 that puts one at $8388608 \cdot 2^{-23}$, where $8388608 = 2^{23}$, and the least subnormal at $1 \cdot 2^{-149}$.

```lean
/-- The binary32 word for 1.0. -/
def one32 : Model FloatFormat.binary32 := Model.ofNatBits 0x3f800000

/-- The binary32 word nearest to 1e-8. -/
def tiny32 : Model FloatFormat.binary32 := Model.ofNatBits 0x322bcc77

#eval Model.toDyadic? one32
-- some { negative := false, significand := 8388608, exponent := -23 }

#eval Model.toDyadic? tiny32
-- some { negative := false, significand := 11258999, exponent := -50 }

#eval Model.toDyadic? (Model.posMinSubnormal FloatFormat.binary32)
-- some { negative := false, significand := 1, exponent := -149 }
```

Keep the significand and exponent of the small value in mind; we'll use them to explain why adding it to one loses the increment.

The exact reading does not stop at finite values. [[FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue]] is an inductive type with three constructors, `finite`, `infinity`, and `nan`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] decodes any word into it without losing anything: a finite value keeps its dyadic, an infinity keeps its sign, and a NaN keeps its sign, whether it is signaling, and its whole fraction field. Bit-for-bit comparison against an external oracle needs these exceptional-value fields as well as the finite value. Mapping to a real number would discard them.

```lean
#eval Model.exactValue (Model.negZero FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.finite { negative := true, significand := 0, exponent := 0 }

#eval Model.exactValue (Model.posInf FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.infinity false

#eval Model.exactValue (Model.canonicalNaN FloatFormat.binary32)
-- FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue.nan false false 4194304
```

The canonical NaN is positive and quiet, and its fraction field is $4194304 = 2^{22}$, the single quiet bit; the two booleans in the output are the sign and the signaling flag.

The third reading is the real number. [[FloatLib.Numerics.Dyadic.toReal]] sends a dyadic to $m \cdot 2^{e}$ with the sign applied, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] composes it with the decoder. The dyadic interpretation is independent of any packed format.

`Model.toReal` is total: a NaN or an infinity is sent to $0$. The partial version `toReal?` returns an `Option ℝ` and exposes the nonfinite case, but a total function is more convenient inside algebraic statements, where `toReal (add x y)` should be a real number. An arithmetic theorem must therefore establish finiteness before treating `toReal` as the numerical value of a result. The relation `Represents` packages the two facts, and `represents_iff` states that `Represents x r` holds exactly when `isFinite x = true` and `toReal x = r`. A rounded-real contract then states that the real value of the result equals the exact real result rounded to the format's grid.

For example, `toReal x = 0` alone cannot tell us whether `x` is a finite zero, an infinity, or a NaN: all of them reach the same real number under this total decoder. Adding `isFinite x = true` rules out the exceptional cases, but still leaves both signs of zero. A proof of `Represents x 0` is therefore sufficient for real algebra while remaining insufficient for a bit-for-bit conformance claim.

We can follow `tiny32` through [Figure 6.1](#/chapter/the-numerical-models/figure-ch06-three-readings). It has a nonzero fraction field. Decoding supplies its integer significand and exponent; applying `Dyadic.toReal` then interprets that pair as a real value.

![The word tiny32 read three ways: its 32 bits and their fields, the Dyadic record that toDyadic? returns, and the real number Dyadic.toReal gives it, with Model.toReal the composite of the last two steps](assets/ch06-three-readings.png "One stored word, decoded first as an exact dyadic and then as a real number. These are three descriptions of the same value.")

<a id="why-the-readings-cannot-be-collapsed"></a>

## What rounding discards

Take $x = 1$ and $y$ the binary32 value nearest to $10^{-8}$, which is $11258999 \cdot 2^{-50}$. The exact sum $1 + y$ is a perfectly good dyadic with a fifty-bit fraction. Binary32 has twenty-three fraction bits, and the spacing of representable numbers just above $1$ is $2^{-23} \approx 1.19 \times 10^{-7}$. The increment $y$ is about $0.084$ of that spacing, so the nearest representable value to the exact sum is $1$ itself.

```lean
#eval Model.add one32 tiny32
-- { bits := 0x3f800000#32 }

#eval Model.addWithStatus one32 tiny32
-- { value := { bits := 0x3f800000#32 },
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true } }
```

We don't need to rely on the approximate $0.084$ above. Measure everything in units of $2^{-50}$, the scale already used by `tiny32`. One is then $2^{50}$ units, the next binary32 value above one is another $2^{27}$ units away, and their midpoint is $2^{26}$ units above one. The increment has only $11258999$ units, with

$$
0 < 11258999 < 2^{26} = 67108864.
$$

The exact sum is strictly above one and strictly below the midpoint. This proves both facts the example reports: nearest rounding returns one, and the rounding is inexact. No decimal approximation is needed to distinguish a tie from a value on either side of it.

The returned word, `0x3f800000`, contains no record of the small increment. Its decoded value is exactly one, just as it would be after adding zero. The `inexact` flag comes from comparing the rounded result with the exact intermediate $1 + y$, so it preserves information that the result word alone cannot supply. In the real-valued model, $\mathrm{round}(1 + y) = 1$ and the absolute rounding error is $y$, less than half the spacing. The bit result, the discarded dyadic part, and the error bound describe distinct stages of this computation.

## The reference operations: decode, compute exactly, round once

Every arithmetic operation on `Model fmt` has a reference definition in the `Model.Spec` namespace. These definitions expose the exact intermediate that determines the rounded result. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add]] decodes both operands with `toDyadic?`; if both succeed it adds the dyadics exactly with `addDyadic` and rounds once with [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]]; otherwise it follows the descriptor's NaN and infinity rules.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul]] multiplies significands and adds exponents. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma]] forms the exact product, adds the third operand exactly, and rounds once, which is what makes it fused.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div]] cannot stay inside the dyadics, since a quotient of dyadics is a general rational, so it rounds a scaled rational with `roundRatScaled`. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt]] handles the sign and zero cases and delegates a positive finite input to the exact square-root routine.

Lean's core library ships a logical model of IEEE floats, `Float.Model.UnpackedFloat`, an inductive with a zero, an infinity, a NaN, and a finite case carrying a sign, a mantissa, and an exponent, together with its own rounding function. For an IEEE descriptor and a positive finite input, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt_eq_model]] identifies FloatLib's square root with the repacked result of that model. Its hypotheses require finiteness, a nonzero input, and a clear sign bit. This theorem does not cover zero or exceptional inputs. Agreement with Lean's logical float model is also distinct from agreement with host instructions.

The dispatched operations, [[FloatLib.Floats.Formats.BinaryInterchange.Model.add]] and its siblings, select a kernel by descriptor and are proved equal to these definitions for every `FloatFormat`, with no IEEE assumption: [[FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.add_eq_spec]] is `add x y = Spec.add x y`. One level up, [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] rewrites `x + y` on a configured type to [[FloatLib.Floats.ExecFloat.Spec.add]], and for a binary format that reference operation is `Model.Spec.add` applied after the stored word is converted to a `Model`. These equalities let a proof replace a dispatched operation with its reference definition, whichever backend the planner picked. On the executable type `Binary32`, a single lemma rewrites `+`:

```lean
open FloatLib.Floats in
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

open FloatLib.Floats in
example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

## The rounding contract as a statement about reals

To relate an operation to rounding on $\mathbb{R}$, we use Boldo and Melquiond's Flocq description of a grid [@boldoMelquiond2011]. The real numbers a format can hold exactly form isolated points on the real line. They are evenly spaced between one power of two and the next, with the spacing doubling at each power of two in the normal range; we call this set the format's grid. Flocq describes the spacing through an exponent function: for a real $x$ with $2^{e-1} \le |x| < 2^{e}$, $\mathrm{fexp}(e)$ is the exponent of the spacing around $x$. For a descriptor `fmt`, [[FloatLib.Floats.Formats.BinaryInterchange.Model.fexpOf]] is [[FloatLib.Floats.Formats.Flocq.fltExp]] applied to the least subnormal exponent and the precision $p + 1$ (the $p$ stored fraction bits plus the hidden leading one), that is

$$\mathrm{fexp}(e) = \max\bigl(e - (p + 1),\; e_{\min}\bigr),$$

so in the normal range the spacing is $2^{e - (p + 1)}$ and $p + 1$ significant bits are kept, while below the normal range the spacing stops shrinking and stays at $2^{e_{\min}}$, which is gradual underflow. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] is Flocq's [[FloatLib.Floats.Formats.Flocq.round]] on that grid with the [[FloatLib.Floats.Formats.Flocq.nearestEven]] integer rounding rule. It is defined on all of $\mathbb{R}$, and its grid has no largest element: `roundAt` never overflows, because a real-valued function has no infinity to return. The executable operation does overflow. The equality between these two computations therefore requires the executable result to be finite.

Two theorems tie the grid to the words. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_genericFormat_of_isFinite]] says that every finite word decodes to a point of the descriptor's grid, in the sense of Flocq's [[FloatLib.Floats.Formats.Flocq.genericFormat]], for every descriptor including custom biases and finite-only encodings. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_toReal_eq]] then says that rounding a finite word's value returns it unchanged. [Chapter 07](#/chapter/the-mathematics-of-rounding) develops the grid theory behind the half-ulp bound [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]], which reads $|\mathrm{roundAt}_f(x) - x| \le \varepsilon_f(x)$, where $\varepsilon_f(x)$, the format's [[FloatLib.Floats.Formats.BinaryInterchange.Model.epsilonAt]], is half the grid spacing at $x$. The same theory gives monotonicity, `roundAt_mono`.

The central refinement theorem is [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]]. For `x y : Model fmt` it states

$$\operatorname{toReal}(\operatorname{add}(x, y)) = \operatorname{roundAt}_{f}\bigl(\operatorname{toReal}(x) + \operatorname{toReal}(y)\bigr)$$

under four hypotheses: `fmt.isIEEE = true`, `isFinite x = true`, `isFinite y = true`, and `isFinite (add x y) = true`. This is an equality of real numbers, not a bound. Its proof walks the chain just described: `add_eq_spec` replaces the dispatched `add` by `Spec.add`; since `x` and `y` are finite, `toDyadic?` succeeds on both, say with `dx` and `dy`, and `Spec.add` unfolds to `roundDyadic fmt (addDyadic dx dy)`; [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]] identifies the executable rounder with `roundAt` on the dyadic's real value; and the exactness of dyadic addition finishes it. The same theorem exists for subtraction ([[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_roundAt]]), multiplication ([[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_mul_eq_roundAt]]), division by a nonzero finite operand ([[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]]), fused multiply-add ([[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]]), and casts between IEEE formats ([[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]]). Square root is the one operation whose result cannot overflow, so for a finite input that is nonnegative or a signed zero, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sqrt_eq_roundAt]] needs no hypothesis on the output; [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_sqrt_of_isFinite]] proves finiteness under the same domain condition instead of assuming it.

For `one32` and `tiny32`, the exact sum lies between adjacent binary32 values near $1$. In [Figure 6.2](#/chapter/the-numerical-models/figure-ch06-one-rounding), the shorter distance is back to $1$, so both the reference rounder and the executable addition return that grid point.

![The refinement theorem on one32 and tiny32: the exact real sum 1 + 11258999 · 2^-50 lies about 0.084 of a gap above 1 on the binary32 grid, and one rounding by roundAt takes it back to 1, the value of the word that add returns](assets/ch06-one-rounding.png "The exact sum lies less than half a binary32 gap above one. The executable addition and the real rounder both return one.")

Let's apply the theorem to words we already know. For concrete words every hypothesis is decidable, so after `apply` leaves the four side goals (`isIEEE`, finiteness of each input, and finiteness of the sum), `decide` closes each one by evaluating the boolean:

```lean
/-- The binary32 word for 2.0. -/
def two32 : Model FloatFormat.binary32 := Model.ofNatBits 0x40000000

example :
    Model.toReal (Model.add one32 two32) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal one32 + Model.toReal two32) := by
  apply Model.toReal_add_eq_roundAt <;> decide
```

For symbolic words the hypotheses become assumptions, and the `numerics` tactic, which knows the registered refinement theorems and discharges the `isIEEE` side condition for named formats, closes the generic statement:

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal x + Model.toReal y) := by
  numerics
```

We can now rewrite the executable result using this equality and apply the rounding error bound. [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_toReal_add_sub_le]] does this for one addition: its proof applies `toReal_add_eq_roundAt` followed by `abs_roundAt_sub_le`.

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    |Model.toReal (Model.add x y) - (Model.toReal x + Model.toReal y)| ≤
      Model.epsilonAt FloatFormat.binary32 (Model.toReal x + Model.toReal y) :=
  Model.abs_toReal_add_sub_le x y FloatFormat.isIEEE_binary32 hx hy hout
```

Notice the argument to `epsilonAt` in the bound: it is the exact sum of the decoded operands. For `one32` and `tiny32`, that sum lies in the binade from one to two, whose spacing is $2^{-23}$, so the bound is $2^{-24}$. The actual error is $11258999 \cdot 2^{-50}$, and the integer comparison above proves it is smaller. In a symbolic proof we must keep the bound at the exact expression until we have justified its magnitude; substituting the rounded output as its argument can change the spacing when rounding crosses a power of two.

<a id="the-finiteness-hypotheses-and-how-to-discharge-them"></a>

## Proving inputs and results are finite

Each finiteness hypothesis excludes a case where the equality would fail. The input hypotheses are needed because `toReal` returns a placeholder for nonfinite values: without them, `toReal x` could be the $0$ that stands in for a NaN, and the theorem would assert that adding a NaN behaves like adding zero. The output hypothesis excludes overflow. If $x$ and $y$ are both the largest finite binary32 value, the executable sum is $+\infty$, `toReal` of it is $0$, and the right-hand side is the ordinary real $\mathrm{roundAt}_f(2 \cdot \mathrm{maxFinite})$, near $6.8 \times 10^{38}$. An infinity cannot be identified with the finite real value on the right.

For known words, computing the result decides its finiteness. For symbolic inputs, magnitude bounds can establish finiteness before the result is computed. [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite_add_of_abs_add_le_posMaxFinite]] says that if $|x| + |y|$ is at most the value of [[FloatLib.Floats.Formats.BinaryInterchange.Model.posMaxFinite]], the executable sum is finite, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite]] combines it with the refinement so that the output hypothesis never appears. Subtraction, multiplication, division, and fused multiply-add have the same pair of lemmas with the corresponding triangle, product, quotient, or product-plus-addend bound; division also keeps its nonzero-divisor hypothesis. For binary32, `posMaxFinite` decodes to $16777215 \cdot 2^{104}$, about $3.4 \times 10^{38}$.

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hbound : |Model.toReal x| + |Model.toReal y| ≤
      Model.toReal (Model.posMaxFinite FloatFormat.binary32)) :
    Model.toReal (Model.add x y) =
      Model.roundAt FloatFormat.binary32
        (Model.toReal x + Model.toReal y) :=
  Model.toReal_add_eq_roundAt_of_abs_add_le_posMaxFinite x y
    FloatFormat.isIEEE_binary32 hx hy hbound
```

The triangle bound is convenient when we have separate bounds on the operands, but it is only sufficient. If one operand is the largest finite value and the other its negation, their sum is exactly zero although the sum of their absolute values is twice the largest finite value. When cancellation matters, `isFinite_add_of_abs_toReal_add_le_posMaxFinite` instead takes a bound on the absolute value of the exact sum itself. The triangle-bound theorem is derived from this tighter criterion using the triangle inequality. Choosing between them depends on the information the application already has about its operands.

The hypothesis `fmt.isIEEE = true` restricts the real-valued refinement theorem to conventional IEEE descriptors. Exact decoding, the reference operations, and the `Spec` equalities hold for every descriptor, including FNUZ and finite-only encodings. The bridge to `roundAt` additionally goes through Lean's float model, because `roundDyadic` delegates its normalization to that model for IEEE descriptors, and the model is IEEE-shaped. `toDyadic?_ieee_eq_model` and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_eq_unpackedToReal_toModel]] identify the binary decoder with it exactly when the descriptor is conventionally IEEE. A non-IEEE format has exact dyadic semantics and executable arithmetic, but its operations do not yet have a `roundAt` theorem.

<a id="the-relational-form-and-the-general-interface"></a>

## A common interface for numerical formats

We can also state the addition theorem as a relation between an operation and the values it represents. `add_refines` says that `Model.add` satisfies [[FloatLib.Numerics.Operation.Finite2If]], with specification `fun x y => roundAt fmt (x + y)` and condition `isFinite result = true`. Whenever both inputs represent finite reals and the result is finite, the result represents the rounded exact sum. [[FloatLib.Numerics.Operation.Refines]] expresses this kind of contract as a relation in `Prop`, so it adds no runtime data. The theory can reason about $\mathbb{R}$ without manipulating bit patterns, while the executable operation uses only its stored values.

Posits, fixed point, logarithmic codes, and block-scaled values also have codes and numerical meanings. They share the interface [[FloatLib.Numerics.NumericalSystem]], a structure with a `Code` type, a `Scalar` type, and a `denote` function from codes to [[FloatLib.Numerics.NumericalValue]]. A numerical value is `finite x`, `infinity negative`, or `exceptional e`, where [[FloatLib.Numerics.ExceptionalValue]] covers a NaN with an optional payload, the posit `notAReal`, reserved words, and undefined results. A theorem stated over this interface can relate different families without referring to their bit layouts.

We give `Model fmt` two numerical systems, depending on what we want to prove. `numericalSystem` takes $\mathbb{R}$ as the scalar: `toNumericalValue` sends a NaN to `exceptional (nan (some payload))` with the fraction field as payload, an infinity to `infinity sign`, and everything else to `finite (toReal x)`. `exactNumericalSystem` takes `Numerics.Dyadic` as the scalar, so the sign of zero is not forgotten. The exact system is what a conformance test compares against; the real system is what an error analysis is stated in. Neither introduces a second floating-point type.

## Extended reals for directed rounding

The binary IEEE operation interface implements four rounding modes, discussed in [chapter 02](#/chapter/from-reals-to-machine-numbers). [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]] lists `nearestEven`, `towardZero`, `towardPositiveInfinity`, and `towardNegativeInfinity`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithRounding]] and its siblings execute all of them for every descriptor. Bounds for directed rounding must include infinite results if they are to remain valid through overflow.

The decoder [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal]] maps words into Mathlib's `EReal`. Finite words coerce from `toReal`, and the two infinities become $-\infty$ and $+\infty$ (written $\bot$ and $\top$ in Mathlib). The partial `toEReal?` returns `none` exactly for a NaN. The total `toEReal` instead sends a NaN to $0$, the same placeholder `toReal` uses, so the theorems still need to exclude NaNs.

The directed theorems are inequalities in `EReal` with no finiteness hypothesis on the output: [[FloatLib.Floats.Formats.BinaryInterchange.Model.toEReal_addDown_le]] bounds the downward-rounded sum by the exact real sum, [[FloatLib.Floats.Formats.BinaryInterchange.Model.le_toEReal_addUp]] bounds the exact sum by the upward-rounded one, and multiplication and division have the same pairs. The library's interval arithmetic, in the tradition of Moore [@moore1966], is built on these two directions: [[FloatLib.Floats.Formats.BinaryInterchange.Model.Interval.add_sound]] encloses the exact sum of two reals between the downward-rounded sum of the lower bounds and the upward-rounded sum of the upper bounds, and its proof is the two inequalities above applied to the endpoints.

We can check the endpoint directions for interval addition by writing the whole chain. If the finite endpoint values satisfy $a \le x \le b$ and $c \le y \le d$, monotonicity of real addition gives $a+c \le x+y \le b+d$. Downward rounding places the stored lower endpoint at or below $a+c$; upward rounding places the stored upper endpoint at or above $b+d$. Transitivity then encloses the exact sum. If an endpoint operation overflows outward, its infinite endpoint still makes sense in this order. The NaN exclusions are necessary because a NaN supplies no ordered bound to put into the chain.

## Status flags as data

A status-bearing operation returns its exception flags with its value. The caller can inspect that operation in isolation or combine its flags with earlier ones; the meaning of the call does not depend on a mutable status register. [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]] is a structure of five booleans, `invalid`, `divideByZero`, `overflow`, `underflow`, and `inexact`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]] pairs a result word with a status. The status-bearing operations, [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus]] and its siblings, compute the exact dyadic intermediate and the rounded value under the requested mode, then classify the pair with [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicRoundingStatus]]; division, whose exact intermediate is a rational rather than a dyadic, uses the rational counterpart of the same classifier. The flags are classified from the same intermediate and rounded result, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus_value]] proves that the value field is exactly the value-only operation.

Overflow follows IEEE 754-2019 Section 7.4 [@ieee754_2019] and the MPFR exception definition [@fousseMpfr2007]: the exact value is rounded to the destination precision with an unbounded exponent range, and the result overflows when that lands beyond the largest finite value. `dyadicRoundingOverflows` implements this per mode, so a magnitude just above the largest finite value overflows under a mode that increases magnitude but not under rounding toward zero.

Inexact compares the exact dyadic with the decoded result. Underflow follows Section 7.5 with tininess detected after rounding: the exact value is first rounded to the destination precision as if the exponent range were unbounded, and the result counts as tiny when that rounded magnitude is below the least normal number. [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicIsTinyAfterRounding]] decides this, and underflow is raised only when the result is tiny and inexact, so an exact subnormal raises nothing.

The theorems record the consequences: [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicRoundingStatus_overflow]] characterizes the overflow flag, `dyadicRoundingStatus_inexact_of_overflow` and `dyadicRoundingStatus_inexact_of_underflow` show that either range flag implies inexact, and `dyadicRoundingStatus_not_underflow_of_overflow` shows that the two range flags are exclusive. For exceptional operands, [[FloatLib.Floats.Formats.BinaryInterchange.Model.addWithStatus_invalid]] gives the complete condition for `invalid` on addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.divWithStatus_divideByZero]] says division raises `divideByZero` exactly for a nonzero finite numerator over a zero, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.sqrtWithStatus_invalid]] says square root raises `invalid` exactly for a signaling NaN or a negative nonzero input.

We can learn something from operations that return the same infinity: the flags tell us why each got there. Three exceptional cases let us compare the flags. Dividing one by positive zero returns positive infinity, `0x7f800000`, and raises only `divideByZero`. Doubling the largest finite value overflows to the same infinity and raises `overflow` together with `inexact`, as `dyadicRoundingStatus_inexact_of_overflow` requires. Subtracting infinity from itself is invalid, so the result is the canonical quiet NaN, `0x7fc00000`, and only `invalid` is raised.

```lean
#eval Model.divWithStatus one32 (Model.posZero FloatFormat.binary32)
-- { value := { bits := 0x7f800000#32 },
--   status := { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false } }

#eval Model.mulWithStatus (Model.posMaxFinite FloatFormat.binary32) two32
-- { value := { bits := 0x7f800000#32 },
--   status := { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true } }

#eval Model.subWithStatus (Model.posInf FloatFormat.binary32) (Model.posInf FloatFormat.binary32)
-- { value := { bits := 0x7fc00000#32 },
--   status := { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false } }
```

The underflow rule is easiest to see on the smallest numbers. Adding the least subnormal to itself is exact, so nothing is raised even though the result is subnormal; halving it falls below the grid, rounds to zero, and raises both `underflow` and `inexact`.

```lean
/-- The binary32 word for 0.5. -/
def half32 : Model FloatFormat.binary32 := Model.ofNatBits 0x3f000000

#eval Model.addWithStatus (Model.posMinSubnormal FloatFormat.binary32)
  (Model.posMinSubnormal FloatFormat.binary32)
-- { value := { bits := 0x00000002#32 },
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false } }

#eval Model.mulWithStatus (Model.posMinSubnormal FloatFormat.binary32) half32
-- { value := { bits := 0x00000000#32 },
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true } }
```

Flags accumulate with [[FloatLib.Numerics.IEEEStatus.union]] when a caller wants them to persist across a sequence of operations, the way a hardware status register does.

## Numerics: exact values and contracts

The same ideas apply beyond binary words. [[FloatLib.Numerics.NumericalValue]] describes a finite, infinite, or exceptional value without choosing a bit layout. [[FloatLib.Numerics.NumericalSystem]] pairs a code type with its denotation, and [[FloatLib.Numerics.NumericalSystem.Represents]] states that a code denotes a particular value. `EncodedFormat` and `FormatSemantics` separate the computable code type from its possibly noncomputable meaning: a program can manipulate the codes even when their semantics lives in $\mathbb{R}$. These are the common interfaces used by the exact-value types of [chapter 02](#/chapter/from-reals-to-machine-numbers).

An exact intermediate must preserve the information needed by the destination. [[FloatLib.Numerics.Dyadic]] stores $\pm m \cdot 2^e$; [[FloatLib.Numerics.Dyadic.toRat]] gives its rational value, and [[FloatLib.Numerics.Dyadic.add_toRat]] proves that addition preserves the exact sum. [[FloatLib.Numerics.SignedRat]] adds an IEEE sign bit to a rational, so a cast can carry $-0$ through exact arithmetic.

To state what an operation does with those values, [[FloatLib.Numerics.Operation.Refines]] relates executable inputs and outputs to a mathematical operation; [[FloatLib.Numerics.Operation.Finite2If]] specializes the relation to two finite inputs under a condition. Rounding choices remain explicit in [[FloatLib.Numerics.QuantizationPolicy]], including saturation and flush to zero. [[FloatLib.Numerics.Quantization.Spec]] describes the allowed rounded result, and [[FloatLib.Numerics.Quantization.Spec.Implements]] asserts that an executable rounder meets that description. At the integer level, [[FloatLib.Numerics.roundShiftRightEven]] makes the nearest-even choice when bits are discarded. A contract states an obligation; a proof of the contract establishes it for an implementation.

<a id="what-the-models-do-not-claim"></a>

## From one operation to a calculation

The `*_eq_spec` equalities carry these results from `Model fmt` to certified backends. Lean's native `Float` and `Float32` use a different execution path: `toDyadic?_ieee_eq_model` relates decoders, without proving the behavior of compiled processor instructions. [Chapter 15](#/chapter/performance/comparing-with-leans-native-floats) discusses that distinction. A separate issue arises even within the proved model: each arithmetic equality describes one operation.

To use these theorems in our own calculation, we need to carry the rounded intermediate into the next step. For a two-stage sum in an IEEE format, suppose the inputs and both results are finite. Write the decoded results as $s_1 = \mathrm{roundAt}_f(x+y)$ and $s_2 = \mathrm{roundAt}_f(s_1+z)$, with $x,y,z$ now denoting the finite input reals. The second application needs a finiteness argument for the addition involving the stored first result. Its local error is measured against $s_1+z$, whereas the total error is measured against $x+y+z$. Subtracting the latter gives the exact decomposition

$$
s_2-(x+y+z) = \bigl(s_2-(s_1+z)\bigr) + \bigl(s_1-(x+y)\bigr).
$$

Now we can apply the triangle inequality to combine the two local error bounds. A theorem for one rounded addition does not replace these two roundings by a single rounding of the three-input sum. For a longer computation, we need to establish the hypotheses at every step and account for each rounding; [chapter 07](#/chapter/the-mathematics-of-rounding) gives the relevant grid results and [chapter 01](#/chapter/using-the-library) applies the interfaces.
