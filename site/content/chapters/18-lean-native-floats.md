---
number: "18"
slug: lean-native-floats
title: "Lean's native floats"
summary: "Follow finite rounding, NaN payloads, integer conversions, and explicit host calls through Lean's native float model."
phases: [trust]
---

## Lean's model and its compiled operations

We're glad to see Lean exposing more of its floating-point model for proofs. Lean 4.33 introduced the logical models; Lean 4.34 connects the signed integer conversions to them and exposes integer constructors and named `nan` and `inf` constants [@lean434Release]. We use those definitions to connect ordinary signed casts to FloatLib's rounding and conversion specifications.

In the logical model, a `Float32` contains a `Float32.Model`: a `UInt32` word with a validity proof. NaNs are canonical, so importing different NaN payloads produces the same model value. `Float` has the corresponding structure over `UInt64`.

The logical arithmetic definitions unpack sign, significand, and exponent, perform arithmetic, round to nearest even, and pack a result. Addition applies model addition and then `ofModel`. The runtime-facing definitions carry `@[extern]` attributes: compiled `Float32.add` uses C floating-point addition and compiled `Float32.sqrt` calls `sqrtf`. A theorem about the logical definition doesn't by itself verify that external runtime operation.

The block below prints stored words in hexadecimal at both widths. Its three `rfl` examples expose the logical definitions of addition, multiplication, and the bit cast without making a claim about generated machine code. The last evaluation shows the canonical NaN that the native bit-conversion API returns.

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

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

FloatLib represents the same finite binary32 and binary64 values while keeping NaN signs, payloads,
and signaling distinctions. The last line above already exposes a difference: the conversion to
Lean's native type has discarded the payload before any arithmetic runs.

## Both implementations lose associativity

Binary32 addition isn't associative. Take $x = 2^{25}$, $y = -2^{25}$, and $z = 1$, whose exact sum
is 1 under either grouping. In binary32, $y + z$ lies halfway between two representable values, and
nearest-even rounding returns $y$. Binary32 has 24 significant bits, so on the side of $-2^{25}$
toward zero consecutive values are 2 apart. The exact value $-33554431$ sits halfway between
$-33554432$ and $-33554430$, and the first of those has an even final significand bit. So
$x + (y + z)$ is 0, while $(x + y) + z$ is 1. Both the host and FloatLib give those results.

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

We compare encoded words in the last two evaluations because the ordinary display strings differ.
Both return `true`, so the implementations agree on the rounding that loses the unit in the second
grouping.

Our native comparisons extend this example to ties, cancellation, both signed zeros,
subnormals, normal boundaries, overflow, infinities, and NaNs. They compare ordinary FloatLib
operations with their software kernels, guarded host calls with software, and bit conversions
through Lean's native types, and all of them passed with zero mismatches. The [validation
chapter](#/chapter/external-validation) explains the external comparisons and their scope.

Subnormal
inputs matter here, since an environment that flushes them to zero may disagree with the software
operation. These comparisons exercise the compiler, runtime, processor, and process settings all at
once, so passing on one machine doesn't establish agreement for every operand and environment.

## Converting to native floats changes NaN payloads

A binary32 NaN has an all-ones exponent and a nonzero fraction field, and that field also carries
payload bits and a quiet/signaling distinction. FloatLib keeps those distinctions in its raw
representation, but Lean's `Float32.ofBits` canonicalizes them. Say we import the signaling NaN
`0x7f812345` into `Float32`. It becomes the canonical quiet NaN `0x7fc00000`, and its payload is
gone before any arithmetic runs. That shows up in a word-for-word comparison even when both
implementations correctly return a NaN, so two correct answers can still disagree :) The comparison
below uses fourteen pairs, covering a tie at half an ulp, cancellation, subnormal arithmetic,
normal/subnormal boundaries, overflow, signed zeros, infinity, and two NaN operands.
`rawDisagreements32` applies a raw host operation and a software operation to the same pair of input
words, compares the output words, and returns the input pairs that produced differences, so the
returned input words identify each disagreement:

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

Addition, subtraction, multiplication, and division each differ on the two NaN pairs, and the other
twelve pairs agree, including subnormal sums, overflow to infinity, and signed zeros.

To find where
the payload changes, let's follow the quiet-NaN addition through `rawDisagreements32`. Both paths
receive the input words `0x7fc12345` and `0x3f800000`, and the second word represents 1. On the host
branch, `Float32.ofBits` comes first and turns the first word into `0x7fc00000`, while on the
software branch `0x7fc12345` comes in unchanged. Addition then propagates a NaN on each branch, and
`toBits` exposes the two different payloads. What comes back from the comparison is the original
operand pair, which is what you need to reproduce the discrepancy, and not the two result words. If
we compared only the result class, this payload difference would be invisible. Later, the [guarded
host example](#/chapter/lean-native-floats/opting-into-guarded-host-operations) reuses the same
`pairs32` list and keeps these NaN operands in software.

## Proofs relating FloatLib to Lean's float model

[[FloatLib.Floats.ExecFloat.Binary.ofFloat32]] imports a native value into a `Binary32` as its
`toBits` word, which is the word `ofBits32` takes. [[FloatLib.Floats.ExecFloat.Binary.toFloat32]]
exports the FloatLib word through `Float32.ofBits`. For binary64, `ofFloat` and `toFloat` follow the
same pattern with `Binary64`. All four functions accept every other configured format too, casting
through binary32 or binary64 with `Model.cast` and rounding once in their `mode` option when the
destination can't hold the value. You pick the format with the expected type:

```lean
#eval ExecFloat.Binary.toFloat (0.1 : BFloat16)
-- 0.100098
#eval ExecFloat.Binary.toNatBits (ExecFloat.Binary.ofFloat 0.1 : BFloat16)
-- 15821
#eval ExecFloat.Binary.toNatBits (ExecFloat.Binary.ofFloat 0.1 (mode := .down) : BFloat16)
-- 15820
```

The nearest bfloat16 value sits slightly above one tenth, so rounding down gives the word just below
it. For `Binary32` and `Binary64`, the native conversion proofs show that importing a native value
keeps its stored word and that exporting it again gives back the value:

```lean
example (x : Float32) :
    ExecFloat.Binary.toBits32 (ExecFloat.Binary.ofFloat32 x) = x.toBits :=
  ExecFloat.Binary.toBits32_ofFloat32 x

example (x : Float) :
    ExecFloat.Binary.toBits64 (ExecFloat.Binary.ofFloat x) = x.toBits :=
  ExecFloat.Binary.toBits64_ofFloat x

example (x : Float32) :
    ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofFloat32 x : Binary32) = x :=
  ExecFloat.Binary.toFloat32_ofFloat32 x

example (x : Float) :
    ExecFloat.Binary.toFloat (ExecFloat.Binary.ofFloat x : Binary64) = x :=
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

[[FloatLib.Floats.ExecFloat.Binary.toFloat32_ofFloat32]] covers every native value, both signed
zeros, the infinities, and Lean's canonical NaN included. Its proof rests on the shared packing
invariant, which says that unpacking and repacking a valid word gives back that word, and we prove
it once for arbitrary exponent and fraction widths and then specialize it to binary32 and binary64.

Starting from a FloatLib word is different. In the block above, the last theorem keeps every bit
through `ofBits32` and `toBits32`, NaN payload included. But export the signaling word `0x7f812345`
through `toFloat32` and you get the canonical quiet NaN `0x7fc00000`, as
[[FloatLib.Floats.ExecFloat.Binary.ofFloat32_toFloat32]] specifies. Exporting the finite word
`0x3fc00000` gives 1.5, and its bits don't change.

### Integer conversions

Lean's integer constructors round once to nearest-even, and we connect their shared model operation
to FloatLib's existing conversion specification, result word and rounding status included. That
argument works for every conventional IEEE descriptor, and the native `Int8`, `Int16`, `Int32`,
`Int64`, and `ISize` casts specialize it to the two host widths. An `Int64`, for example, may need
rounding when converted to binary32:

```lean
open FloatLib.Numerics.Representations in
example (n : Int64) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat32 n.toFloat32 : Binary32) =
      ExecDType.intToFloat FloatFormat.binary32
        (⟨n.toBitVec⟩ : FixedInt 64) (mode := .nearest) :=
  ExecFloat.Binary.toModel_ofFloat32_int64ToFloat32 n

example (n : Int) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat n.toFloat : Binary64) =
      Model.roundDyadic FloatFormat.binary64 (FloatLib.Numerics.Dyadic.ofScaledInt n 0) :=
  ExecFloat.Binary.toModel_ofFloat_intToFloat n

example :
    ExecFloat.Binary.toModel (ExecFloat.Binary.ofFloat32 Float32.nan : Binary32) =
      Model.canonicalNaN FloatFormat.binary32 :=
  ExecFloat.Binary.toModel_ofFloat32_nan
```

All of these accept unbounded integers: the exposed `Float.ofNat` and `Float.ofInt` constructors,
their binary32 counterparts, and the `Int.toFloat` and `Int.toFloat32` names. Their bridge proofs
cover both the small-literal path and general integer rounding, so an input bigger than a machine
word keeps its full magnitude until the final rounding.

Going back to a signed integer follows a
different rule. Lean truncates toward zero and then saturates to the destination's range, mapping
NaN to zero and each infinity to the signed endpoint. So the range check applies to the truncated
integer, and `127.75` still converts to the `Int8` value 127.

```lean
example : (Float32.ofBits 0xbfe00000).toInt8 = (-1 : Int8) := by decide
example : (Float32.ofBits 0x42ff8000).toInt8 = (127 : Int8) := by decide
example : Float32.nan.toInt8 = (0 : Int8) := by decide
example : Float32.inf.toInt8 = (127 : Int8) := by decide
```

FloatLib's `ExecDType.floatToIntSaturating` follows that native policy, built from the existing
exact decoder and integral rounder. Its agreement theorems also tie it to the checked
`ExecDType.floatToInt`, and both return the same integer whenever the truncated value fits. For
overflow, infinity, or NaN the checked operation returns an error instead, which helps when a caller
wants to handle those inputs itself.

### Arithmetic through the same model

For arithmetic the bridge goes beyond the two host widths. Lean's `UnpackedFloat` algorithms take a
format argument, so FloatLib can relate them to every descriptor that satisfies its IEEE format
conditions. A decoder theorem,
[[FloatLib.Floats.Formats.BinaryInterchange.Model.ieeeToDyadic?_eq_unpackedToDyadic?_toModel]],
shows that the two models read the same exact dyadic value, and
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_eq_unpackedToReal_toModel]] lifts that
agreement to real values. Addition and subtraction agree on the complete result word whenever both
operands are finite, signed zeros included, and the result may be zero, subnormal, or infinite. You
can apply the addition theorem to ordinary Lean expressions:

```lean
example (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ExecFloat.Binary.ofFloat32 (x + y) : Binary32) =
      ExecFloat.Binary.ofFloat32 x + ExecFloat.Binary.ofFloat32 y :=
  ExecFloat.Binary.ofFloat32_add_of_isFinite x y hx hy
```

[[FloatLib.Floats.ExecFloat.Binary.ofFloat32_add_of_isFinite]] connects the native expression on the
left to the configured software addition on the right. Because it's an equality of words, it tells
positive and negative zero apart, which an equality of decoded real values can't do. The subtraction
and binary64 theorems have the same finite-input conditions. A real-valued addition theorem,
[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_ofModel_add_finite_eq_roundAt]], gives the
complementary conclusion. Under its nonzero finite-input and finite-result hypotheses, Lean's
rounded sum has value
$\operatorname{roundAt}_{\mathrm{fmt}}(\operatorname{value}(x)+\operatorname{value}(y))$. So in our
earlier cancellation example, adding $y=-2^{25}$ and $z=1$ rounds the exact sum $-33554431$ to
$-33554432$.

Square root goes further. It agrees for **every input**, including negative zero,
negative arguments, infinities, and NaNs. You can run the certified software operation and then
export the result, or export first and take Lean's logical square root:

```lean
example (x : Binary32) :
    ExecFloat.Binary.toFloat32 (ExecFloat.sqrt x) =
      (ExecFloat.Binary.toFloat32 x).sqrt :=
  ExecFloat.Binary.toFloat32_sqrt x
```

[[FloatLib.Floats.ExecFloat.Binary.toFloat32_sqrt]] and its binary64 counterpart both follow from
one theorem for every conventional IEEE descriptor. NaNs get canonicalized at the native boundary,
but every other result bit agrees, sign of zero included. And
[[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeModelSqrt.unpackedSqrt_eq_sqrt]] lets the
compiler evaluate Lean's model square root through FloatLib's proved integer kernel.

[Multiplication
and
division](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/LeanModel.lean)
come with narrower hypotheses. Multiplication needs a provisional exponent that satisfies Lean's
`roundWithAccuracy` precondition, and division also needs a nonzero provisional quotient from
`divCore`. Once those conditions and the stated finite conditions hold, the real-valued conclusions
apply.

For operands unpacked from format words, though, the exponent condition always holds, and
division doesn't need a nonzero provisional quotient. So for a conventional IEEE descriptor the
[format-word
theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/LeanModel/MulDiv.lean)
need only a finite result, and a finite divisor for division. They conclude
$\operatorname{roundAt}_{\mathrm{fmt}}(\operatorname{value}(x)\cdot\operatorname{value}(y))$ and
$\operatorname{roundAt}_{\mathrm{fmt}}(\operatorname{value}(x)/\operatorname{value}(y))$. When
`divCore` returns a zero provisional quotient, the sign, the selected exponent, and the remainder
accuracy still decide whether the result rounds to a signed zero or a signed least subnormal. Let's
check the smallest case with the kernel. The least positive subnormal divided by `1.5` rounds back
to itself, even though its provisional quotient is zero.

```lean
example : Float.ofBits 0x0000000000000001 / 1.5 = Float.ofBits 0x0000000000000001 := rfl

example :
    (Float.ofBits 0x0000000000000001).toModel.unpack = .finite .positive 1 (-1074) (by decide) ∧
    (1.5 : Float).toModel.unpack = .finite .positive (3 * 2 ^ 51) (-52) (by decide) ∧
    (Float.Model.UnpackedFloat.divCore Float.Model.Format.binary64
      1 (-1074) (3 * 2 ^ 51) (-52)).1 = 0 :=
  ⟨rfl, rfl, by decide⟩
```

All of these proofs are about Lean's logical definitions. Compiled native calls still go through
external runtime functions and hardware instructions, and the optional guarded host operations
below keep that trust boundary.

## Formats, rounding directions, and status

Lean's native types give you binary32 and binary64, and FloatLib's descriptor also covers smaller,
wider, and custom layouts through the same configured interface. The quotient one third makes the
precision difference visible:

```lean
#eval (1 : Float32) / 3
-- 0.333333
#eval (1 : Binary32) / 3
-- 0.33333334
#eval (1 : Binary16) / 3
-- 0.3333
#eval (1 : Binary64) / 3
-- 0.3333333333333333
#eval hex64 ((1 : Float) / 3).toBits == hex64 (ExecFloat.Binary.toBits64 ((1 : Binary64) / 3))
-- true
```

The host's six-decimal display of one third hides which binary value it stored. FloatLib prints
the shortest decimal that reads back as the stored quotient, which is four digits for binary16,
eight for binary32, and sixteen for binary64. The exact binary16 quotient is $0.333251953125$, and
to see every digit you can use `ExecFloat.Binary.format` with `(style := .exact)`. In the last
evaluation, the host and FloatLib binary64 quotients turn out to be the same word, and binary16
shows what a smaller precision does.

FloatLib also takes the rounding direction as an argument. The
named operations [[FloatLib.Floats.ExecFloat.Binary.add]], `sub`, `mul`,
[[FloatLib.Floats.ExecFloat.Binary.div]], `fma`, and `sqrt` accept a `mode` option of type
[[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. It offers nearest-even,
nearest with ties away from zero, toward zero, toward positive infinity, toward negative infinity,
and MPFR's rounding away from zero. Ordinary operators use nearest-even. For one third, the two
directed binary32 results are adjacent words:

```lean
#eval hex32 (ExecFloat.Binary.toBits32
  (ExecFloat.Binary.div (1 : Binary32) 3 (mode := .up)))
-- "0x3eaaaaab"
#eval hex32 (ExecFloat.Binary.toBits32
  (ExecFloat.Binary.div (1 : Binary32) 3 (mode := .down)))
-- "0x3eaaaaaa"
#eval hex32 ((1 : Float32) / 3).toBits
-- "0x3eaaaaab"
```

On the host you get the upper word, `0x3eaaaaab`, because it's closer to the exact value of one
third. Directed rounding also gives you the lower neighbour, `0x3eaaaaaa`, without touching process
state, and together the two words can bound the exact quotient for interval arithmetic. We can check
the host's choice from the stored values, with no decimal formatting involved. Written exactly, the
lower word is $11184810\cdot2^{-25}$ and the upper is $11184811\cdot2^{-25}$, and subtracting each
from the exact quotient in the appropriate direction gives

$$
\begin{aligned}
\frac13-11184810\cdot2^{-25}&=\frac{2}{3\cdot2^{25}},\\
11184811\cdot2^{-25}-\frac13&=\frac{1}{3\cdot2^{25}}.
\end{aligned}
$$

The upper neighbour is half as far from $1/3$, so nearest-even picks it without ever needing the
tie-breaking rule. Rounding downward picks the lower word because the result has to stay below the
exact quotient. Lean's native logical model uses nearest-even. When you pass a mode to a proved
FloatLib function, the choice is written right there in the call, and the process's hardware
rounding register is left alone.

Exception flags are just as explicit. With `(status := true)` an
operation returns an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]], which holds
the value, an [[FloatLib.Numerics.IEEEStatus]], and the ternary value of [Chapter
07](#/chapter/the-mathematics-of-rounding). The five flags are invalid, division by zero, overflow,
underflow, and inexact, and here are a few calls with the values and flags they return:

```lean
#eval (1 : Float32) / 0
-- inf
#eval (0 : Float32) / 0
-- NaN
#eval ExecFloat.Binary.div (1 : Binary32) 0 (status := true)
-- { value := inf,
--   status := { invalid := false, divideByZero := true, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }
#eval ExecFloat.Binary.div (0 : Binary32) 0 (status := true)
-- { value := nan,
--   status := { invalid := true, divideByZero := false, overflow := false, underflow := false, inexact := false },
--   ternary := Ordering.eq }
#eval ExecFloat.Binary.mul (ExecFloat.Binary.ofBits32 0x7f7fffff) (2 : Binary32) (status := true)
-- { value := inf,
--   status := { invalid := false, divideByZero := false, overflow := true, underflow := false, inexact := true },
--   ternary := Ordering.gt }
#eval ExecFloat.Binary.div (ExecFloat.Binary.ofBits32 0x00000001) (2 : Binary32) (status := true)
-- { value := 0,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := true, inexact := true },
--   ternary := Ordering.lt }
```

Lean's native evaluations show infinity for $1/0$ and NaN for $0/0$, and the status-bearing calls
add the reason, division by zero in the first case and invalid operation in the second. Multiplying
the largest finite binary32 word, `0x7f7fffff`, by two overflows to infinity and sets both
`overflow` and `inexact`. In the last call we halve the smallest positive subnormal, `0x00000001`,
so the exact value lies halfway between zero and that subnormal. Nearest-even rounding returns zero
and loses the nonzero exact value, which sets both `underflow` and `inexact`. A subnormal result by
itself isn't enough to set underflow, because FloatLib detects tininess after rounding and also
requires inexactness.

You can't tell every exception history apart from the value alone. FloatLib
computes the flags from the operands, the exact arithmetic, and the delivered result, and it doesn't
read the host's status register. [Chapter 08](#/chapter/ieee-binary-formats) develops the status and
rounding contracts. For plain addition, you get the refinement theorem on the ordinary expression a
program uses:

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
binary32, but the same certificate covers other configured formats and carriers. What it certifies
is the software word kernel, and it says nothing about the processor's floating-point addition.
`#float_info Float32` collects the native conversion and logical-model theorems, with their input
conditions, next to the configured software certificates. It also records which operations depend on
the compiler and host runtime, so you can tell the theorem you're applying apart from the
implementation that runs a native call.

## Opting into guarded host operations

You have to import the [unchecked host
module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean)
yourself, because `import FloatLib` doesn't reach it. It exposes ten arithmetic functions,
[[FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked.add32]], `sub32`,
`mul32`, `div32`, and `sqrt32` plus the corresponding `64` functions. All of them take and return
the ordinary configured binary32 or binary64 values without carrying a refinement certificate, and a
guard decides whether to use a host operation or the proved software fallback:

| Operation | Inputs that use the host operation |
| --- | --- |
| Addition, subtraction, multiplication | Both operands finite |
| Division | Both operands finite and the divisor nonzero |
| Square root | A finite nonnegative operand, or negative zero |

So NaNs, infinities, zero divisors, and negative nonzero square-root inputs take the software path.
Square root accepts negative zero so that it can return the required negative-zero result, and other
negative inputs go to software. There's no unchecked FMA, because multiplying and then adding
through Lean's primitives would round twice and wouldn't be a fused operation. The addition guard is
short enough to read in full. Our transcription uses the public bit conversions and writes the
fallback as `left + right`, which the refinement examples above identify with the certified software
entry point, and it reuses the fourteen `pairs32` inputs from the raw comparison:

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

`binary32Finite` checks that the exponent field isn't all ones. Finite operand pairs reach `Float32`
addition, and a NaN or infinity sends the function to the software operation. At the end we count
output-word disagreements against FloatLib addition and get zero. For addition the raw comparison
returned two, because its NaN pairs always crossed into Lean's canonicalizing representation. With
the guard, those pairs stay in software and the FloatLib payload result survives.

Branch order is
what makes this work. Before it calls `Float32.ofBits`, the function inspects the exponent in the
FloatLib word. The NaN word `0x7fc12345` has an all-ones exponent, so the fallback still has the
original payload, while for the ordinary pair 1 and 2, both exponents are finite, and the function
takes the host branch. Looking at the words only after native conversion would be too late to save
the NaN payload.

On this machine all fourteen pairs agree with software under nearest-even rounding. That tells us
how the guard handles these examples, but we have no theorem covering every host call. Division and
square root have guards too, and they keep the invalid operations listed in the table in software.

Compiled host calls require **round-to-nearest, ties-to-even and gradual underflow**. If you change
the rounding register or enable flush-to-zero or denormals-are-zero, a host call can disagree with
the software specification, because the guard checks operands and doesn't certify the process's
floating-point environment.

You only get these functions by calling them. They aren't
`@[implemented_by]` substitutions behind the certified operations, and the planner can't select
them. The fixed-format candidates and
[[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.selectCertified_binary32AddCandidates]]
keep certified binary32 selection on proved software.

So use `Float` or `Float32` for host
arithmetic when their formats and runtime assumptions fit your application, and use
`ExecFloat.Binary` when a computation needs its refinement theorem, a chosen rounding direction,
returned status, payload-preserving words, or a different layout. If your application accepts the
remaining runtime assumptions, the unchecked module lets you opt into a host call on FloatLib
values. You'd still have to measure its performance in that application, because the [native C
measurements](#/chapter/performance/host-arithmetic-as-a-reference) use a different calling
interface.
