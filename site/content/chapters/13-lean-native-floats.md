---
number: "13"
slug: lean-native-floats
title: "Lean's native floats"
summary: "How Lean's own Float and Float32 relate to FloatLib, how to convert between them, and what is proved and what is trusted about them and the processor."
phases: [trust]
---

Lean has two float types built in, `Float32` for binary32 numbers and `Float` for binary64. Each stores a number as a word, a raw pattern of 32 or 64 bits that we'll print in hexadecimal, and FloatLib's `Binary32` and `Binary64` hold the same finite values.

Let's start with a surprise. A NaN ("not a number") is the special value you get from something like $0/0$, and its spare bits, its payload, can carry extra information. Hand `Float32` the NaN word `0x7f812345`, read the bits straight back, and you get `0x7fc00000`. The payload is gone, and no arithmetic ran. Lean's model of a float keeps one canonical NaN, a single standard NaN word, and FloatLib keeps NaN payloads, so the two part ways right at the conversion.

## What are Float and Float32?

So what does Lean actually do when you add two `Float32`s? It depends on who's asking, a proof or the compiled program. A proof checked by Lean's kernel, its small trusted proof checker, sees a logical model, the definitions Lean's logic reasons about. The logical models arrived in Lean 4.33, and 4.34 connects the signed integer conversions to them [@lean434Release]. In that model a `Float32` contains a `Float32.Model`, a `UInt32` word with a validity proof, and `Float` has the same structure over `UInt64`. Lean's logical arithmetic unpacks, computes, rounds to nearest even (to the closest float, breaking ties toward an even last bit) and repacks.

The compiled program goes somewhere else. Definitions that run carry `@[extern]`, a forwarding address to external code, so compiled `Float32.add` uses C floating-point addition and compiled `Float32.sqrt` calls `sqrtf`. The work then happens on the host, the machine your program runs on. That split matters, because a theorem about the logical definition doesn't by itself verify what actually runs.

Let's look at some examples. Two helpers print words in hexadecimal, and the `rfl` examples (`rfl` is short for reflexivity) hold by unfolding the logical definitions, so they say nothing about machine code. The last line is our NaN:

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

## Do Lean and FloatLib give the same answers?

Let's give both the same sum, one where the parentheses matter. Binary32 addition isn't associative: $(x + y) + z$ and $x + (y + z)$ can differ, because each step rounds. Take $x = 2^{25}$, $y = -2^{25}$ and $z = 1$. Binary32 values just toward zero from $-2^{25}$ are 2 apart, so $y + z = -33554431$ ties between $-33554432$ and $-33554430$, and nearest-even rounds it back to $y$. So $x + (y + z)$ is 0 while $(x + y) + z$ is 1. If you run both orders on both sides,

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

you get the same 1 and 0 from both. The printouts differ, so the last two lines compare encoded words, and both are `true`.

That's one sum. Our native comparisons cover the corners: ties, cancellation, signed zeros, subnormals (tiny numbers below the normal range), normal boundaries, overflow, infinities and NaNs. They check ordinary FloatLib operations against their software kernels (the integer routines behind each operation), the guarded host calls at the end of this chapter against software, and bit conversions through Lean's native types, and all passed with zero mismatches. But they're tests, and they exercise the compiler, runtime, processor and process settings at once, so passing on one machine doesn't show agreement for every operand and environment. The [validation chapter](#/chapter/external-validation) explains their scope.

## Why do NaNs come out different?

NaNs are another story, and they're where a word-by-word test can fail even though both sides returned a NaN. A binary32 NaN's fraction field, the low bits of its word, carries payload bits and the quiet/signaling distinction (a quiet NaN passes through arithmetic, a signaling one flags an invalid operation when used), and `Float32.ofBits` canonicalizes it, so two correct answers can disagree :) `rawDisagreements32` runs a raw host operation and a software operation on fourteen input pairs, two of them with NaN operands, and returns the pairs whose output words differ:

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

All four operations differ on the two NaN pairs and agree on the other twelve, subnormal sums, overflow and signed zeros included. Think about the quiet-NaN addition. On the host branch `Float32.ofBits` turns `0x7fc12345` into `0x7fc00000` before anything else happens, while the software branch takes it unchanged, so each propagates a NaN with a different payload.

## How to convert between Lean's floats and FloatLib

Tests only answer for the inputs they tried, so now let's prove things relating FloatLib to Lean's logical model, not the compiled code, starting with the functions that carry a value across the border. For `Binary32`, [[FloatLib.Floats.ExecFloat.Binary.ofFloat32]] imports a native value as its `toBits` word and [[FloatLib.Floats.ExecFloat.Binary.toFloat32]] exports through `Float32.ofBits`. For `Binary64`, `ofFloat` and `toFloat` do the same. All four take FloatLib's other configured binary formats too, casting with `Model.cast` and, when the destination can't hold the value, rounding once in their `mode` option. The type Lean expects at each spot picks the format. Start with one tenth in `BFloat16`, a small machine-learning format, and you get

```lean
#eval ExecFloat.Binary.toFloat (0.1 : BFloat16)
-- 0.100098
#eval ExecFloat.Binary.toNatBits (ExecFloat.Binary.ofFloat 0.1 : BFloat16)
-- 15821
#eval ExecFloat.Binary.toNatBits (ExecFloat.Binary.ofFloat 0.1 (mode := .down) : BFloat16)
-- 15820
```

The nearest bfloat16 value is a little above one tenth, so rounding down gives the word below it, 15820. For `Binary32` and `Binary64` we prove that importing keeps the stored word and exporting gives the value back:

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

From the native side, nothing is lost: [[FloatLib.Floats.ExecFloat.Binary.toFloat32_ofFloat32]] covers every value, signed zeros, infinities and Lean's canonical NaN included. From a FloatLib word, though, a NaN loses its payload at the border. The last theorem keeps every bit through `ofBits32` and `toBits32`, but exporting the signaling word `0x7f812345` through `toFloat32` gives the canonical quiet NaN `0x7fc00000`, as [[FloatLib.Floats.ExecFloat.Binary.ofFloat32_toFloat32]] specifies, while the finite `0x3fc00000` comes out as 1.5.

## How to convert integers to floats and back

Integers cross the border too, in both directions. The theorems here are stated for descriptors, FloatLib's records of a format's layout, and a conventional IEEE descriptor has the standard's encoding and exponent bias. Going into a float, Lean's integer constructors round once to nearest-even, and they share one model operation, so that's what we connect to FloatLib's conversion specification, for every conventional IEEE descriptor, result word and rounding status included. The native `Int8`, `Int16`, `Int32`, `Int64` and `ISize` casts specialize it to the two host widths. The unbounded constructors, `Float.ofNat`, `Float.ofInt`, their binary32 counterparts, `Int.toFloat` and `Int.toFloat32`, get the same treatment, with bridge proofs for small literals and general rounding.

That's the nice part: even an input bigger than a machine word keeps its full magnitude until the final rounding. Here are three of the theorems. An `Int64` may need rounding into binary32, as in the first, and the next two take any `Int` and Lean's NaN:

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

Going back to a signed integer, Lean truncates toward zero and saturates (clamps) to the destination's range, a needle pinned at the end of its dial, mapping NaN to zero and each infinity to the matching endpoint. The range check applies to the truncated integer, so `127.75` converts to the `Int8` value 127. Here `by decide` checks each case by computing it:

```lean
example : (Float32.ofBits 0xbfe00000).toInt8 = (-1 : Int8) := by decide
example : (Float32.ofBits 0x42ff8000).toInt8 = (127 : Int8) := by decide
example : Float32.nan.toInt8 = (0 : Int8) := by decide
example : Float32.inf.toInt8 = (127 : Int8) := by decide
```

FloatLib's `ExecDType.floatToIntSaturating` follows that policy, and its agreement theorems tie it to the checked `ExecDType.floatToInt`, which returns the same integer whenever the truncated value fits and an error on overflow, infinity or NaN.

## What is proved about Lean's arithmetic?

Now for arithmetic, where each side computes its own answer. Lean's `UnpackedFloat` algorithms, named for floats unpacked into their pieces, take a format argument, so the arithmetic bridge reaches past the two host widths to every descriptor that satisfies FloatLib's IEEE format conditions. Underneath, [[FloatLib.Floats.Formats.BinaryInterchange.Model.ieeeToDyadic?_eq_unpackedToDyadic?_toModel]] shows the two models read the same exact dyadic value, a number of the form $m \cdot 2^e$ with integers $m$ and $e$, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_eq_unpackedToReal_toModel]] lifts that to real values. Addition and subtraction agree on the complete result word whenever both operands are finite, even when the result is zero, subnormal or infinite, and the addition theorem applies to ordinary Lean expressions:

```lean
example (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ExecFloat.Binary.ofFloat32 (x + y) : Binary32) =
      ExecFloat.Binary.ofFloat32 x + ExecFloat.Binary.ofFloat32 y :=
  ExecFloat.Binary.ofFloat32_add_of_isFinite x y hx hy
```

On the left is the native expression, on the right FloatLib's software addition, and [[FloatLib.Floats.ExecFloat.Binary.ofFloat32_add_of_isFinite]] says they're equal as words, so it tells positive and negative zero apart. The subtraction and binary64 theorems have the same finite-input conditions, and so do the word-level product and quotient bridges `ExecFloat.Binary.ofFloat32_mul_of_isFinite` and `ExecFloat.Binary.ofFloat32_div_of_isFinite`, the second covering division by zero and `0 / 0` too. In real values, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_ofModel_add_finite_eq_roundAt]] says that for finite nonzero inputs and a finite result, Lean's rounded sum has value $\operatorname{roundAt}_{\mathrm{fmt}}(\operatorname{value}(x)+\operatorname{value}(y))$, the exact sum rounded once in the format.

### What about square root?

Square root agrees for **every input**, negative zero, negative arguments, infinities and NaNs included. Taking FloatLib's certified square root before exporting, or Lean's logical one after, gives the same value:

```lean
example (x : Binary32) :
    ExecFloat.Binary.toFloat32 (ExecFloat.sqrt x) =
      (ExecFloat.Binary.toFloat32 x).sqrt :=
  ExecFloat.Binary.toFloat32_sqrt x
```

We get [[FloatLib.Floats.ExecFloat.Binary.toFloat32_sqrt]] and its binary64 counterpart from one theorem for every conventional IEEE descriptor. NaNs get canonicalized at the native boundary, and every other result bit agrees, sign of zero included. The compiler can also evaluate Lean's model square root through FloatLib's proved integer kernel, thanks to [[FloatLib.Floats.Formats.BinaryInterchange.Model.NativeModelSqrt.unpackedSqrt_eq_sqrt]].

### What about multiplication and division?

For [multiplication and division](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/LeanModel.lean) the real-valued conclusions are fussier. They need a provisional exponent, from the result Lean computes before rounding, that meets Lean's `roundWithAccuracy` precondition and, for division, a nonzero provisional quotient from `divCore`. Operands unpacked from format words always meet the first, and division doesn't need the second. So for a conventional IEEE descriptor the [format-word theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/LeanModel/MulDiv.lean) need only a finite result, plus a finite divisor for division, and conclude $\operatorname{roundAt}_{\mathrm{fmt}}(\operatorname{value}(x)\cdot\operatorname{value}(y))$ and $\operatorname{roundAt}_{\mathrm{fmt}}(\operatorname{value}(x)/\operatorname{value}(y))$. The smallest positive binary64 number, a subnormal, divided by `1.5` rounds back to itself, even though its provisional quotient is zero:

```lean
example : Float.ofBits 0x0000000000000001 / 1.5 = Float.ofBits 0x0000000000000001 := rfl

example :
    (Float.ofBits 0x0000000000000001).toModel.unpack = .finite .positive 1 (-1074) (by decide) ∧
    (1.5 : Float).toModel.unpack = .finite .positive (3 * 2 ^ 51) (-52) (by decide) ∧
    (Float.Model.UnpackedFloat.divCore Float.Model.Format.binary64
      1 (-1074) (3 * 2 ^ 51) (-52)).1 = 0 :=
  ⟨rfl, rfl, by decide⟩
```

**Note:** All of these proofs are about Lean's logical definitions, not the external runtime functions and hardware instructions that compiled native calls reach.

## What does FloatLib add to Float and Float32?

What else does FloatLib give you that `Float` and `Float32` don't? More formats, a choice of rounding direction, exception flags and a refinement theorem. Let's take them one at a time.

### How to use other formats

Lean's native types give you binary32 and binary64, and FloatLib's descriptor also covers smaller, wider and custom layouts. If you divide one by three in a few of them,

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

you can see the precision of each. The host prints six decimals, which doesn't say which value it stored, while FloatLib prints the shortest decimal that reads back as the stored quotient. To see the exact value, try `((1 : Binary16) / 3).format (style := .exact)` yourself, which prints $0.333251953125$. In the last line the host and FloatLib binary64 quotients are the same word.

### How to choose a rounding direction

FloatLib also takes the rounding direction as an argument, right there in the call. Its named operations [[FloatLib.Floats.ExecFloat.Binary.add]], `sub`, `mul`, [[FloatLib.Floats.ExecFloat.Binary.div]], `fma` (fused multiply-add, $x \cdot y + z$ as one step with one rounding) and `sqrt` accept a `mode` of type [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]], while ordinary operators use nearest-even. With `.up` you round toward $+\infty$ and with `.down` toward $-\infty$. For one third the two directed binary32 results are neighbouring words:

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

The host gives you the upper word, `0x3eaaaaab`, and directed rounding also hands you the lower `0x3eaaaaaa` without touching process state, the floating-point settings your program shares, so the two words can bound the exact quotient for interval arithmetic. Written exactly, the lower word is $11184810\cdot2^{-25}$ and the upper is $11184811\cdot2^{-25}$, and their distances from one third are

$$
\begin{aligned}
\frac13-11184810\cdot2^{-25}&=\frac{2}{3\cdot2^{25}},\\
11184811\cdot2^{-25}-\frac13&=\frac{1}{3\cdot2^{25}}.
\end{aligned}
$$

The upper neighbour is half as far away, so nearest-even picks it without needing its tie rule.

### How to see the exception flags

Exception flags are something you ask for too. Think of them as a receipt that comes with the result. With `(status := true)` an operation returns an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]] holding the value, an [[FloatLib.Numerics.IEEEStatus]] with the five IEEE flags, and the ternary (three-way) value of the [rounding chapter](#/chapter/the-mathematics-of-rounding), which says whether the result was rounded up, down or not at all:

```lean
#eval (1 : Float32) / 0
-- inf
#eval (0 : Float32) / 0
-- NaN
#eval ExecFloat.Binary.div (1 : Binary32) 0 (status := true)
-- { value := inf, status := { divideByZero := true }, ternary := Ordering.eq }
#eval ExecFloat.Binary.div (0 : Binary32) 0 (status := true)
-- { value := nan, status := { invalid := true }, ternary := Ordering.eq }
#eval ExecFloat.Binary.mul (ExecFloat.Binary.ofBits32 0x7f7fffff) (2 : Binary32) (status := true)
-- { value := inf, status := { overflow := true, inexact := true }, ternary := Ordering.gt }
#eval ExecFloat.Binary.div (ExecFloat.Binary.ofBits32 0x00000001) (2 : Binary32) (status := true)
-- { value := 0, status := { underflow := true, inexact := true }, ternary := Ordering.lt }
```

Lean's native $1/0$ and $0/0$ just give you values, and the receipts add why, division by zero and invalid operation. Doubling the largest finite word overflows with `inexact`. The last line is subtler. Halving the smallest positive subnormal ties between zero and it, and nearest-even returns zero, which sets `underflow` and `inexact`. A subnormal result alone isn't enough for underflow, because FloatLib detects tininess (a result below the normal range) after rounding and also requires inexactness. FloatLib writes the receipt from the operands, the exact arithmetic and the delivered result, and doesn't read the host's status register. For more on the status and rounding contracts, see the [IEEE binary formats chapter](#/chapter/ieee-binary-formats).

### What the refinement theorem gives you

Then there's the refinement theorem, which no `#eval` can show you. It says the code that runs refines the specification, which means it computes exactly what the specification says, and for plain addition it applies to the ordinary expression a program uses:

```lean
example (x y : Binary32) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y

example (x y : Binary32) : x + y = Configured.Backend.wordAdd x y := rfl

example (x y : Binary32) :
    Configured.Backend.wordAdd x y = Configured.Spec.add x y :=
  Configured.Backend.wordAdd_eq_spec x y

#float_info Float32
-- Float information: Float32
--   family: Lean native Float32
--   standard: IEEE 754 binary32 runtime format through Lean's native float API
```

Here [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Backend.wordAdd_eq_spec]] is used at binary32, and the same certificate covers other configured formats and carriers, the runtime representations a value can be stored in. It certifies the software word kernel and says nothing about the processor's floating-point addition. `#float_info Float32` lists the native conversion and logical-model theorems with their input conditions next to the configured software certificates, and records which operations depend on the compiler and host runtime.

## How to use the processor's own arithmetic

All of FloatLib's arithmetic in this chapter has run in software. Want the processor's own arithmetic on FloatLib values instead? You have to ask for it, because `import FloatLib` doesn't reach the [unchecked host module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean). Its ten functions, [[FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked.add32]], `sub32`, `mul32`, `div32` and `sqrt32` and the matching `64` ones, take and return configured binary32 or binary64 values without a refinement certificate, which is what unchecked means here. A guard, a check on the operands, decides whether each call uses a host operation or the proved software fallback:

| Operation | Inputs that use the host operation |
| --- | --- |
| Addition, subtraction, multiplication | Both operands finite |
| Division | Both operands finite and the divisor nonzero |
| Square root | A finite nonnegative operand, or negative zero |

Everything else takes the software path, and negative zero reaches the host square root so it can return negative zero. There's no unchecked FMA, because multiplying and then adding through Lean's primitives would round twice. Here's the addition guard, transcribed with the public bit conversions and falling back to the certified `left + right`, on the fourteen `pairs32` inputs:

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

Not one output word disagrees with FloatLib addition, where the raw comparison gave two, and the difference is one check. The guard inspects the exponent in the FloatLib word before it calls `Float32.ofBits`, so the NaN word `0x7fc12345` reaches the fallback with its payload, while the pair 1 and 2 takes the host branch.

### What the guard doesn't check

Don't read too much into that zero, though. It covers these fourteen examples on this machine under nearest-even rounding, and we have no theorem covering every host call. Compiled host calls require **round-to-nearest, ties-to-even and gradual underflow**, which keeps subnormal results. Change the rounding register, or enable flush-to-zero or denormals-are-zero (denormal is an older name for subnormal), processor modes that replace subnormal results or inputs with zero, and a host call can disagree with the software specification, because the guard checks operands and doesn't certify the process's floating-point environment.

You only get these functions by calling them. They aren't `@[implemented_by]` substitutions hiding host code behind the certified operations, and the planner, which picks the implementation each operation runs, can't select them. The fixed-format candidates and [[FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.selectCertified_binary32AddCandidates]] make sure certified binary32 selection picks proved software.

## Which should you use?

Reach for `Float` or `Float32` when their formats and runtime assumptions fit, and for `ExecFloat.Binary` when you want a refinement theorem, a chosen rounding direction, returned status, payload-preserving words or another layout. The unchecked module opts you into host calls on FloatLib values if you accept the remaining runtime assumptions, but measure them in your application, because the [native C measurements](#/chapter/performance/host-arithmetic-as-a-reference) use a different calling interface.
