---
number: "18"
slug: lean-native-floats
title: "Lean's native floats"
summary: "Follow finite rounding, NaN payloads, integer conversions, and explicit host calls through Lean's native float model."
phases: [trust]
---

## Lean's model and its compiled operations

We're glad to see Lean exposing more of its floating-point model for proofs.
Lean 4.33 introduced the logical models; **Lean 4.34** connects the signed integer
conversions to them and exposes integer constructors and named `nan` and `inf` constants
[@lean434Release]. We use them to connect ordinary signed casts to the rounding and conversion
specifications already used by FloatLib.

In Lean 4.34, `Float32` contains a `Float32.Model`, which holds a `UInt32`
word and a validity proof. Its NaN representation is canonical: different NaN payloads do not
remain distinct model values. `Float` has the corresponding structure over `UInt64`.

The logical definitions unpack sign, significand, and exponent, perform arithmetic, round to
nearest even, and pack a result. For example, addition is defined by applying model addition
and then `ofModel`. The runtime-facing definitions carry `@[extern]` attributes: compiled
`Float32.add` uses C floating-point addition, and `Float32.sqrt` uses `sqrtf`. The logical model
and the external implementation therefore have a boundary that a proof about the model alone
does not verify.

To compare the stored words ourselves, we'll print them in hexadecimal at both widths.
The three `rfl` examples expose the logical definitions of
addition, multiplication, and the bit cast without making a claim about generated machine code.
The last evaluation shows the canonical NaN returned by the native bit-conversion API.

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev Binary16 := ExecFloat.Binary (exponentBits := 5) (fractionBits := 10)
abbrev Binary32 := ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

/-- Print a 32-bit word as eight hexadecimal digits. -/
def hex32 (w : UInt32) : String :=
  let digits := String.ofList (Nat.toDigits 16 w.toNat)
  "0x" ++ "".pushn '0' (8 - digits.length) ++ digits

/-- Print a 64-bit word as sixteen hexadecimal digits. -/
def hex64 (w : UInt64) : String :=
  let digits := String.ofList (Nat.toDigits 16 w.toNat)
  "0x" ++ "".pushn '0' (16 - digits.length) ++ digits

example (a b : Float32) : a + b = Float32.ofModel (a.toModel + b.toModel) := rfl
example (a b : Float) : a * b = Float.ofModel (a.toModel * b.toModel) := rfl
example (bits : UInt32) :
    Float32.ofBits bits = Float32.ofModel (Float32.Model.ofBits bits) := rfl

#eval hex32 (Float32.ofBits 0x7f812345).toBits
-- "0x7fc00000"
```

FloatLib uses the same finite value sets for binary32 and binary64, while retaining additional
NaN distinctions. We can first compare some encoded results, then examine which model
identities have proofs.

<a id="the-same-finite-bits-including-rounding-effects"></a>

## Both implementations lose associativity

Binary32 addition is not associative. Take $x = 2^{25}$, $y = -2^{25}$, and $z = 1$. The exact sum
is 1 under either grouping. In binary32, $y + z$ lies halfway between two representable values;
nearest-even rounding returns $y$. Binary32 has 24 significant bits: on the side of $-2^{25}$
toward zero, consecutive values are 2 apart. The exact value $-33554431$ is halfway between
$-33554432$ and $-33554430$, and the first has an even final significand bit. Thus $x + (y + z)$
is 0, while $(x + y) + z$ is 1. Both the host and FloatLib produce those results.

```lean
def big : Float32 := Float32.ofBits 0x4c000000
def negBig : Float32 := Float32.ofBits 0xcc000000
def one : Float32 := Float32.ofBits 0x3f800000

#eval (big + negBig) + one
-- 1.000000
#eval big + (negBig + one)
-- 0.000000

def sBig : Binary32 := ExecFloat.Binary.ofBits32 0x4c000000
def sNegBig : Binary32 := ExecFloat.Binary.ofBits32 0xcc000000
def sOne : Binary32 := ExecFloat.Binary.ofBits32 0x3f800000

#eval (sBig + sNegBig) + sOne
-- 1
#eval sBig + (sNegBig + sOne)
-- 0
#eval hex32 ((big + negBig) + one).toBits == hex32 (ExecFloat.Binary.toBits32 ((sBig + sNegBig) + sOne))
-- true
#eval hex32 (big + (negBig + one)).toBits == hex32 (ExecFloat.Binary.toBits32 (sBig + (sNegBig + sOne)))
-- true
```

The final two evaluations compare encoded words because the ordinary display strings differ.
Both return `true`: the implementations agree on the rounding that loses the unit in the
second grouping.

The native comparisons extend this example to ties, cancellation, both signed zeros,
subnormals, normal boundaries, overflow, infinities, and NaNs. They compare ordinary
FloatLib operations with their software kernels, guarded host calls with software, and
bit conversions through Lean's native types. These checks passed with zero mismatches.
The [validation chapter](#/chapter/external-validation) explains the
external comparisons and their scope.

Subnormal inputs matter because an environment that flushes them to zero may disagree with
the software operation. These comparisons exercise the compiler, runtime, processor, and process settings together.
Passing on one machine does not establish agreement for every operand and environment.

<a id="nan-payloads-change-at-the-native-conversion-boundary"></a>

## Converting to native floats changes NaN payloads

A binary32 NaN has an all-ones exponent and a nonzero fraction field. That field also carries
payload bits and a quiet/signaling distinction. FloatLib keeps those distinctions in its raw
representation. Lean's `Float32.ofBits` canonicalizes them.

The signaling NaN `0x7f812345` becomes the canonical quiet NaN `0x7fc00000` when imported into
`Float32`. Its payload has been lost before any arithmetic runs. This affects a direct
comparison even when both implementations correctly return a NaN.

The fourteen pairs below include a tie at half an ulp, cancellation, subnormal arithmetic,
normal/subnormal boundaries, overflow, signed zeros, infinity, and two NaN operands.
`rawDisagreements32` applies a raw host operation and a software operation to the same pair of
input words. It compares output words and returns the input pairs that produced differences.
We'll keep the input words visible so that a reported difference tells us which pair to inspect:

```lean
/-- The fourteen binary32 operand pairs of `tests/FloatLibTests/Fixtures/NativeIEEE.lean`. -/
def pairs32 : List (UInt32 × UInt32) :=
  [ (0x3f800000, 0x40000000), (0x3f800000, 0x33800000), (0x3f800001, 0xbf800000)
  , (0xbf800000, 0x3f800000), (0x00000001, 0x00000002), (0x80000001, 0x00000001)
  , (0x00800000, 0x3f000000), (0x007fffff, 0x00000001), (0x007fffff, 0x00800000)
  , (0x7f7fffff, 0x7f7fffff), (0x00000000, 0x80000000), (0x7f800000, 0x3f800000)
  , (0x7fc12345, 0x3f800000), (0x7f812345, 0xff800000) ]

/-- Pairs on which a raw host operation and the proved kernel return different bits. -/
def rawDisagreements32 (host : Float32 → Float32 → Float32)
    (soft : Binary32 → Binary32 → Binary32) : List (String × String) :=
  pairs32.filterMap fun (a, b) =>
    let hostBits := (host (Float32.ofBits a) (Float32.ofBits b)).toBits
    let softBits :=
      ExecFloat.Binary.toBits32 (soft (ExecFloat.Binary.ofBits32 a) (ExecFloat.Binary.ofBits32 b))
    if hostBits == softBits then none else some (hex32 a, hex32 b)

#eval rawDisagreements32 (· + ·) (· + ·)
-- [("0x7fc12345", "0x3f800000"), ("0x7f812345", "0xff800000")]
#eval (rawDisagreements32 (· - ·) (· - ·)).length
-- 2
#eval (rawDisagreements32 (· * ·) (· * ·)).length
-- 2
#eval (rawDisagreements32 (· / ·) (· / ·)).length
-- 2

#eval hex32 (Float32.ofBits 0x7fc12345 + Float32.ofBits 0x3f800000).toBits
-- "0x7fc00000"
#eval hex32 (ExecFloat.Binary.toBits32
  (ExecFloat.Binary.ofBits32 0x7fc12345 + ExecFloat.Binary.ofBits32 0x3f800000))
-- "0x7fc12345"
```

Addition, subtraction, multiplication, and division each differ on the two NaN pairs.
The other twelve pairs agree, including subnormal sums, overflow to infinity, and signed zeros.
We can locate the payload change by following the quiet-NaN addition through `rawDisagreements32`.
The two paths receive the input words `0x7fc12345` and `0x3f800000`. The host branch first applies
`Float32.ofBits`, turning the first word into `0x7fc00000`; the second word represents 1.
The software branch imports `0x7fc12345` unchanged. Addition then propagates a NaN on each
branch, and `toBits` exposes their different payloads. The comparison returns the original
operand pair, which tells us how to reproduce the discrepancy; it is not returning the two
result words.

Comparing only the result class would hide this payload difference. The
[guarded host example](#/chapter/lean-native-floats/opting-into-guarded-host-operations)
uses the same `pairs32` list and keeps these NaN operands in software.

<a id="the-proved-conversion-and-arithmetic-bridges"></a>

## Proofs relating FloatLib to Lean's float model

[[FloatLib.Floats.ExecFloat.Binary.ofFloat32]] imports a native value's `toBits` word through
`ofBits32`. [[FloatLib.Floats.ExecFloat.Binary.toFloat32]] exports the FloatLib word through
`Float32.ofBits`. The binary64 functions `ofFloat` and `toFloat` follow the same pattern.
The native conversion proofs show that importing a native value keeps its stored word,
and exporting it again recovers the value:

```lean
example (x : Float32) :
    ExecFloat.Binary.toBits32 (ExecFloat.Binary.ofFloat32 x) = x.toBits :=
  ExecFloat.Binary.toBits32_ofFloat32 x

example (x : Float) :
    ExecFloat.Binary.toBits64 (ExecFloat.Binary.ofFloat x) = x.toBits :=
  ExecFloat.Binary.toBits64_ofFloat x

example (x : Float32) :
    ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofFloat32 x) = x :=
  ExecFloat.Binary.toFloat32_ofFloat32 x

example (x : Float) :
    ExecFloat.Binary.toFloat (ExecFloat.Binary.ofFloat x) = x :=
  ExecFloat.Binary.toFloat_ofFloat x

example (v : Binary32) :
    ExecFloat.Binary.ofBits32 (ExecFloat.Binary.toBits32 v) = v :=
  ExecFloat.Binary.ofBits32_toBits32 v

#eval ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofBits32 0x3fc00000)
-- 1.500000
#eval hex32 (ExecFloat.Binary.toBits32 (ExecFloat.Binary.ofBits32 0x7f812345))
-- "0x7f812345"
#eval hex32 (ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofBits32 0x7f812345)).toBits
-- "0x7fc00000"
```

[[FloatLib.Floats.ExecFloat.Binary.toFloat32_ofFloat32]] covers every native value, including
both signed zeros, infinities, and Lean's canonical NaN. Its proof uses the shared packing
invariant: unpacking and repacking a valid word recovers that word. We prove this once for
arbitrary exponent and fraction widths, then specialize it to binary32 and binary64.

Starting from a FloatLib word is different. The last theorem keeps every bit through
`ofBits32` and `toBits32`, including a NaN payload. Exporting the signaling word `0x7f812345`
through `toFloat32` instead produces the canonical quiet NaN `0x7fc00000`, as specified by
[[FloatLib.Floats.ExecFloat.Binary.ofFloat32_toFloat32]]. The finite word `0x3fc00000` exports
as 1.5 without changing its bits.

### Integer conversions in Lean 4.34

The newly exposed integer constructors round once to nearest-even. We connect their shared
model operation to FloatLib's existing conversion specification, including the result word
and rounding status. That argument applies to every conventional IEEE descriptor; the
native `Int8`, `Int16`, `Int32`, `Int64`, and `ISize` casts specialize it to the two host widths.
For example, an `Int64` may need rounding when converted to binary32:

```lean
open FloatLib.Numerics.Representations in
example (n : Int64) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat32 n.toFloat32) =
      ExecDType.intToFloat FloatFormat.binary32
        (⟨n.toBitVec⟩ : FixedInt 64) .nearestEven :=
  ExecFloat.Binary.toModel_ofFloat32_int64ToFloat32 n

example (n : Int) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat n.toFloat) =
      Model.roundDyadic FloatFormat.binary64 (FloatLib.Numerics.Dyadic.ofScaledInt n 0) :=
  ExecFloat.Binary.toModel_ofFloat_intToFloat n

example :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat32 Float32.nan) =
      Model.canonicalNaN FloatFormat.binary32 :=
  ExecFloat.Binary.toModel_ofFloat32_nan
```

The exposed `Float.ofNat` and `Float.ofInt` constructors, their binary32 counterparts, and
the new `Int.toFloat` and `Int.toFloat32` names accept unbounded integers. Their bridge proofs
cover both the small-literal path and general integer rounding, so an input larger than a
machine word retains its full magnitude until the final rounding.

Conversion back to a signed integer has a different rule: truncate toward zero, then
saturate to the destination's range. Lean maps NaN to zero and each infinity to the signed
endpoint. The range check therefore concerns the truncated integer: `127.75` still converts
to `Int8` value 127.

```lean
example : (Float32.ofBits 0xbfe00000).toInt8 = (-1 : Int8) := by decide
example : (Float32.ofBits 0x42ff8000).toInt8 = (127 : Int8) := by decide
example : Float32.nan.toInt8 = (0 : Int8) := by decide
example : Float32.inf.toInt8 = (127 : Int8) := by decide
```

FloatLib's `ExecDType.floatToIntSaturating` follows that native policy using the existing
exact decoder and integral rounder. Its agreement theorems also connect it to the checked
`ExecDType.floatToInt`: both return the same integer when the truncated value fits.
The checked operation returns an error for overflow, infinity, or NaN, which is useful
when a caller wants to handle those inputs explicitly.

### Arithmetic through the same model

The arithmetic bridge is broader than the two host widths. Lean's `UnpackedFloat` algorithms
take a format argument, so FloatLib can relate them to every descriptor satisfying its IEEE
format conditions. The decoder theorem
[[FloatLib.Floats.Formats.BinaryInterchange.Model.ieeeToDyadic?_eq_unpackedToDyadic?_toModel]]
identifies the exact dyadic value read by the two models.
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_eq_unpackedToReal_toModel]] lifts that
agreement to real values.

Addition and subtraction agree on the complete result word whenever both operands are
finite. These hypotheses allow signed zeros, and the result may be zero, subnormal, or
infinite. We can apply the addition theorem directly to ordinary Lean expressions:

```lean
example (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ExecFloat.Binary.ofFloat32 (x + y) =
      ExecFloat.Binary.ofFloat32 x + ExecFloat.Binary.ofFloat32 y :=
  ExecFloat.Binary.ofFloat32_add_of_isFinite x y hx hy
```

[[FloatLib.Floats.ExecFloat.Binary.ofFloat32_add_of_isFinite]] connects the native expression
on the left to the configured software addition on the right. The corresponding subtraction
and binary64 theorems have the same finite-input conditions. Unlike equality of decoded real
values, this word equality distinguishes positive and negative zero.

The real-valued addition theorem
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_ofModel_add_finite_eq_roundAt]]
provides a complementary conclusion: under its nonzero finite-input and finite-result
hypotheses, Lean's rounded sum has value
$\operatorname{roundAt}_{\mathrm{fmt}}(\operatorname{value}(x)+\operatorname{value}(y))$.
In our earlier cancellation example, adding $y=-2^{25}$ and $z=1$ therefore rounds the exact
sum $-33554431$ to $-33554432$.

Square root agrees for **every input**, including negative zero, negative arguments,
infinities, and NaNs. We can perform the certified software operation and then export the
result, or export first and take Lean's logical square root:

```lean
example (x : Binary32) :
    ExecFloat.Binary.toFloat32 (ExecFloat.sqrt x) =
      (ExecFloat.Binary.toFloat32 x).sqrt :=
  ExecFloat.Binary.toFloat32_sqrt x
```

[[FloatLib.Floats.ExecFloat.Binary.toFloat32_sqrt]] and its binary64 counterpart follow from
one theorem for every conventional IEEE descriptor. The native boundary canonicalizes NaNs;
all other result bits, including the sign of zero, agree.
[[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeModelSqrt.unpackedSqrt_eq_sqrt]] also
lets the compiler evaluate Lean's model square root through FloatLib's proved integer kernel.

The [multiplication and division comparisons](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/LeanModel.lean)
have narrower hypotheses. Multiplication requires a provisional exponent satisfying Lean's
`roundWithAccuracy` precondition. Division also requires a nonzero provisional quotient from
`divCore`. Their real-valued conclusions apply once those conditions and the stated finite
conditions have been established.

All these proofs concern Lean's logical definitions. Compiled native calls still use external
runtime functions and hardware instructions. The optional guarded host operations below retain
that trust boundary.

## Formats, rounding directions, and status

Lean's native types expose binary32 and binary64. FloatLib's descriptor also supports smaller,
wider, and custom layouts, with the same configured interface. Binary16, for example, rounds
one third differently:

```lean
#eval (1 : Float32) / 3
-- 0.333333
#eval (1 : Binary32) / 3
-- 11184811 * 2^-25
#eval (1 : Binary16) / 3
-- 0.333251953125
#eval (1 : Binary64) / 3
-- 6004799503160661 * 2^-54
#eval hex64 ((1 : Float) / 3).toBits == hex64 (ExecFloat.Binary.toBits64 ((1 : Binary64) / 3))
-- true
```

The host's six-decimal display of one third does not expose the full stored value. FloatLib
prints the exact binary16 quotient as `0.333251953125`, and the exact binary32 and binary64
quotients as a significand times a power of two. Its formatter uses a plain integer or decimal
when the remaining normalized power of two lies between $2^{-18}$ and $2^{18}$, and a dyadic
expression outside that range.

The last evaluation confirms that the host and FloatLib binary64 quotients have identical
words. The binary16 quotient illustrates the effect of choosing a smaller precision.

FloatLib also takes the rounding direction as an argument. The named operations
[[FloatLib.Floats.ExecFloat.Binary.addWithRounding]], `subWithRounding`, `mulWithRounding`, [[FloatLib.Floats.ExecFloat.Binary.divWithRounding]],
`fmaWithRounding`, and `sqrtWithRounding` accept
[[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. It provides nearest-even,
toward zero, toward positive infinity, and toward negative infinity. Ordinary operators use
nearest-even. For one third, the two directed binary32 results are adjacent words:

```lean
#eval hex32 (ExecFloat.Binary.toBits32
  (ExecFloat.Binary.divWithRounding (1 : Binary32) 3 (rounding := .towardPositiveInfinity)))
-- "0x3eaaaaab"
#eval hex32 (ExecFloat.Binary.toBits32
  (ExecFloat.Binary.divWithRounding (1 : Binary32) 3 (rounding := .towardNegativeInfinity)))
-- "0x3eaaaaaa"
#eval hex32 ((1 : Float32) / 3).toBits
-- "0x3eaaaaab"
```

The host result is the upper word, `0x3eaaaaab`, because it is closer to the exact value of one
third. Directed rounding also exposes the lower neighbour, `0x3eaaaaaa`, without changing process
state. Together the two values can bound the exact quotient for interval arithmetic.

The stored values let us check the choice without relying on decimal formatting. The lower
word is $11184810\cdot2^{-25}$ and the upper is $11184811\cdot2^{-25}$. Subtracting each
from the exact quotient in the appropriate direction gives

$$
\begin{aligned}
\frac13-11184810\cdot2^{-25}&=\frac{2}{3\cdot2^{25}},\\
11184811\cdot2^{-25}-\frac13&=\frac{1}{3\cdot2^{25}}.
\end{aligned}
$$

The upper neighbour is half as far from $1/3$, so nearest-even chooses it without needing
the tie-breaking rule. Rounding downward chooses the lower word because it must remain
below the exact quotient. These directed results can serve as interval endpoints.
Lean's native logical model uses nearest-even; passing a mode to a proved FloatLib function
keeps that choice explicit and leaves the process's hardware rounding register alone.

Status-bearing operations return an
[[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEStatus]] alongside the value. Its five
flags are invalid, division by zero, overflow, underflow, and inexact. Watch the flags as well
as the printed value in these calls:

```lean
#eval (1 : Float32) / 0
-- inf
#eval (0 : Float32) / 0
-- NaN
#eval ExecFloat.Binary.divWithStatus (1 : Binary32) 0 (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.divWithStatus (0 : Binary32) 0 (rounding := .nearestEven)
-- (nan, { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false })
#eval ExecFloat.Binary.mulWithStatus (ExecFloat.Binary.ofBits32 0x7f7fffff) (2 : Binary32)
  (rounding := .nearestEven)
-- (inf, { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true })
#eval ExecFloat.Binary.divWithStatus (ExecFloat.Binary.ofBits32 0x00000001) (2 : Binary32)
  (rounding := .nearestEven)
-- (0, { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true })
```

The native evaluations show infinity for $1/0$ and NaN for $0/0$. The status-bearing calls add
the reason: division by zero in the first case and invalid operation in the second. The product
of the largest finite binary32 word, `0x7f7fffff`, by two overflows to infinity and sets both
`overflow` and `inexact`.

The last call halves the smallest positive subnormal, `0x00000001`. Its exact value is halfway
between zero and that smallest subnormal. Nearest-even rounding returns zero, losing the
nonzero exact value, so both `underflow` and `inexact` are set. A subnormal result alone is not
enough to set underflow: FloatLib detects tininess after rounding and requires inexactness.

The value alone cannot distinguish all exception histories. FloatLib computes flags from the
operands, exact arithmetic, and delivered result, rather than reading the host's status register.
[Chapter 08](#/chapter/ieee-binary-formats) develops the status and rounding contracts.

The refinement theorem is available on the ordinary expression used by a program:

```lean
example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

example (x y : Binary32) : x + y = Configured.Backend.wordAdd x y := rfl

example (x y : Binary32) :
    Configured.Backend.wordAdd x y = Configured.Spec.add x y :=
  Configured.Backend.wordAdd_eq_spec x y

#float_info Float32
-- Float information: Lean native Float32
--   standard: IEEE 754 binary32 runtime format through Lean's native float API
```

Here we use [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Backend.wordAdd_eq_spec]] at
binary32; the same certificate covers other configured formats and carriers. It certifies the
software word kernel, not the processor's floating-point addition.

The `#float_info Float32` query collects the native conversion and logical-model theorems,
with their input conditions, alongside the configured software certificates. It also records
which operations depend on the compiler and host runtime, so we can distinguish the theorem
we are applying from the implementation that executes a native call.

## Opting into guarded host operations

The [unchecked host module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean) must be imported
explicitly; `import FloatLib` does not reach it. It exposes ten arithmetic functions:
[[FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked.add32]], `sub32`,
`mul32`, `div32`, and `sqrt32`, with corresponding `64` functions. They take and return the
ordinary configured binary32 or binary64 values. They do not carry refinement certificates.

The guard decides whether to use a host operation or the proved software fallback:

| Operation | Inputs that use the host operation |
| --- | --- |
| Addition, subtraction, multiplication | Both operands finite |
| Division | Both operands finite and the divisor nonzero |
| Square root | A finite nonnegative operand, or negative zero |

NaNs, infinities, zero divisors, and negative nonzero square-root inputs therefore use the
software path. Square root accepts negative zero so it can return the required negative-zero
result; other negative inputs use software. There is no unchecked FMA: multiplying and then
adding through Lean's primitives would introduce two roundings and would not implement a fused
operation.

The addition guard is short enough to inspect directly. This transcription uses the public
bit conversions and writes the fallback as `left + right`, which the refinement examples above
identify with the certified software entry point. It reuses the fourteen `pairs32` inputs from
the raw comparison:

```lean
/-- Whether a binary32 word is finite: the exponent field is not all ones. -/
def binary32Finite (bits : UInt32) : Bool :=
  ((bits >>> 23) &&& 0xff) != 0xff

/-- A transcription of `NativeFPU.Unchecked.add32`: host addition on finite operands, software otherwise. -/
def guardedHostAdd32 (left right : Binary32) : Binary32 :=
  let l := ExecFloat.Binary.toBits32 left
  let r := ExecFloat.Binary.toBits32 right
  if binary32Finite l && binary32Finite r then
    ExecFloat.Binary.ofBits32 (Float32.ofBits l + Float32.ofBits r).toBits
  else
    left + right

#eval pairs32.countP fun (a, b) =>
  ExecFloat.Binary.toBits32 (guardedHostAdd32 (ExecFloat.Binary.ofBits32 a) (ExecFloat.Binary.ofBits32 b)) !=
    ExecFloat.Binary.toBits32 (ExecFloat.Binary.ofBits32 a + ExecFloat.Binary.ofBits32 b)
-- 0
```

`binary32Finite` checks that the exponent field is not all ones. Finite operand pairs reach
`Float32` addition; a NaN or infinity causes the function to call the software operation instead.
The final evaluation counts output-word disagreements against FloatLib addition and returns
zero. The raw comparison returned two for addition because its NaN pairs always crossed into
Lean's canonicalizing representation. The guard keeps those pairs in software, preserving the
FloatLib payload result.

The branch order is essential. The function inspects the exponent in the FloatLib word before
calling `Float32.ofBits`. For the NaN word `0x7fc12345`, that exponent is all ones, so the
fallback still has the original payload available. For the ordinary pair 1 and 2, both
exponents are finite and the function takes the host branch. Inspecting the words only after
native conversion would be too late to preserve the NaN payload.

All fourteen pairs agree with software under nearest-even rounding on this machine.
That shows how the guard handles these examples; we have no theorem covering every host call.
The division and square-root guards also keep the invalid operations listed in the table
in software.

Compiled host calls require **round-to-nearest, ties-to-even and gradual underflow**. Changing the
rounding register, enabling flush-to-zero, or enabling denormals-are-zero can make a host
call disagree with the software specification. The guard checks operands; it does not certify
the process's floating-point environment.

These functions are explicit calls. They are not `@[implemented_by]` substitutions behind the
certified operations, and the planner cannot select them. The fixed-format candidates and
[[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.selectCertified_binary32AddCandidates]]
keep certified binary32 selection on proved software.

Use `Float` or `Float32` for host arithmetic when their formats and runtime assumptions fit the
application. Use `ExecFloat.Binary` when a computation needs its refinement theorem, explicit
rounding direction, returned status, payload-preserving words, or a different layout. The
unchecked module offers an explicit host call on FloatLib values when the application accepts
the remaining runtime assumptions. Its performance still needs measurement in that application;
the [native C measurements](#/chapter/performance/host-arithmetic-as-a-reference)
use a different calling interface.
