/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook
public import FloatLib.Floats.Formats.FixedPoint
public import FloatLib.Floats.Formats.Logarithmic
public import FloatLib.Floats.Formats.OCP.MX
public import FloatLib.Floats.Formats.P3109
public import FloatLib.Floats.Formats.Posit
public import FloatLib.Tactic.FloatDecide
public import FloatLib.Tactic.KernelEval

/-!
# Kernel forms and kernel paths of the formats that are not binary interchange formats

Exact fixed point, logarithmic values, the bipolar codebook and the P3109 formats mark their
capabilities with `KernelPath.DirectReference`, so `float_decide` rewrites a public operation to
the reference operation and Lean's kernel does not run the planner's selection. Posits register
their direct dyadic arithmetic as the kernel form (`KernelPath.KernelForm`), and the OCP MX
element conversion has a tagged rule that finds the code by bisection on natural numbers. These
tests check,
for each family, that the tagged rule rewrites the operation and its notation, and that
`float_decide` decides closed statements with it.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.KernelPaths

open FloatLib.Floats FloatLib.Numerics FloatLib.Floats.ExecFloat FloatLib.Floats.Formats

/-! ## Exact fixed point -/

/-- Binary fixed point with eight fractional bits. -/
abbrev Q8 := ExecFloat.FixedPoint binaryRadix 8

/-- The rule rewrites a sum and a difference to the reference operation, for every operand. -/
example (x y : Q8) : x + y = ExecFloat.Spec.add x y ∧ x - y = ExecFloat.Spec.sub x y := by
  simp only [kernel_optimize, and_self]

example (x y : Q8) : ExecFloat.add x y = ExecFloat.Spec.add x y := by
  simp only [kernel_optimize]

/-- The reference sum and difference are the values of the sum and the difference of the
coefficients, with the kernel arithmetic of `Int`. -/
example (x y : Q8) :
    x + y = ExecFloat.FixedPoint.ofCoefficient (Kernel.Z.add x.coefficient y.coefficient) ∧
      x - y = ExecFloat.FixedPoint.ofCoefficient (Kernel.Z.sub x.coefficient y.coefficient) := by
  simp only [kernel_optimize, and_self]

example :
    ((ExecFloat.FixedPoint.ofCoefficient 12345 : Q8) + ExecFloat.FixedPoint.ofCoefficient (-777)
      - ExecFloat.FixedPoint.ofCoefficient 68).coefficient = 11500 := by
  float_decide

/-- Decimal fixed point: `0.25 + 0.50 = 0.75`, with nothing rounded. -/
example : ((0.25 : ExecFloat.FixedPoint decimalRadix 2) + 0.50).coefficient = 75 := by
  float_decide

/-! ## Logarithmic values -/

/-- Powers of ten with a sign. -/
abbrev L10 := ExecFloat.Logarithmic decimalRadix

example (x y : L10) : x * y = ExecFloat.Spec.mul x y := by
  simp only [kernel_optimize]

example :
    ((.ofExponent 2 : L10) * .ofExponent (-1) (negative := true)).toCode = .value true 1 := by
  float_decide

/-- An equation between the code of a product and a code is the test `sameCode` on the product
of the codes in its kernel shape. -/
example (x y : L10) (code : Logarithmic.Code decimalRadix) :
    ((x * y).toCode = code) =
      (ExecFloat.Logarithmic.sameCode (Logarithmic.Code.mul.kernel x.toCode y.toCode) code =
        true) := by
  simp only [kernel_optimize]

/-- A product with zero, a product of two negative powers of ten, one of them negated, and a
product that is not the stated code. -/
example :
    ((ExecFloat.Logarithmic.zero : L10) * .ofExponent 5).toCode = .zero ∧
      ((.ofExponent (-3) : L10) * .ofExponent (-4) (negative := true)).toCode =
        .value true (-7) ∧
      ((.ofExponent 2 : L10) * .ofExponent 3).toCode ≠ .value true 5 := by
  float_decide

/-! ## P3109 -/

/-- The report's Binary8p4se. -/
abbrev B8P4 := ExecFloat.P3109 .binary8p4se

example (x y : B8P4) :
    x + y = ExecFloat.Spec.add x y ∧ x * y = ExecFloat.Spec.mul x y ∧
      x / y = ExecFloat.Spec.div x y ∧ ExecFloat.sqrt x = ExecFloat.Spec.sqrt x := by
  simp only [kernel_optimize, and_self]

/-- `1.5 + 2.25 = 3.75`, `1.5 * 2.25 = 3.375` and `2.25 / 1.5 = 1.5`, on encodings. -/
example :
    ((1.5 : B8P4) + 2.25).toNatBits = (3.75 : B8P4).toNatBits ∧
      ((1.5 : B8P4) * 2.25).toNatBits = (3.375 : B8P4).toNatBits ∧
      ((2.25 : B8P4) / 1.5).toNatBits = (1.5 : B8P4).toNatBits := by
  float_decide

-- A value of a binary interchange format converts into a P3109 format on its encoding: 1.7
-- in binary32 to the nearest code of Binary8p4se, -2.3e-5 in binary64 rounded up into a format
-- of sixteen bits, and the negative zero, the two infinities and a NaN of binary32.
example :
    (P3109.Arithmetic.Mixed.Convert (P3109.Arithmetic.Destination.p3109 .binary8p4se)
        (BinaryInterchange.Model.ofNatBits 0x3FD9999A :
          BinaryInterchange.Model .binary32)).toNatBits = 70 ∧
      (P3109.Arithmetic.Mixed.Convert
        (P3109.Arithmetic.Destination.p3109 (P3109.Format.signed 16 8 .extended))
        (BinaryInterchange.Model.ofNatBits 0xBEF81E03F705857B :
          BinaryInterchange.Model .binary64) .up .finite).toNatBits = 47168 ∧
      [0x80000000, 0x7F800000, 0xFF800000, 0x7FC00000].map (fun word =>
        (P3109.Arithmetic.Mixed.Convert (P3109.Arithmetic.Destination.p3109 .binary8p4se)
          (BinaryInterchange.Model.ofNatBits word :
            BinaryInterchange.Model .binary32)).toNatBits) = [0, 127, 255, 128] := by
  float_decide

/-- The destination Binary8p4se of the mixed operations below. -/
private abbrev mixedTarget := P3109.Arithmetic.Destination.p3109 .binary8p4se

/-- The code 68 of Binary8p4se. -/
private abbrev mixedCode : B8P4 := ExecFloat.P3109.ofNatBits 68

/-- `1.7` in binary32. -/
private abbrev mixedSingle : BinaryInterchange.Model .binary32 :=
  BinaryInterchange.Model.ofNatBits 0x3FD9999A

/-- `-2.5` in binary32. -/
private abbrev mixedNegative : BinaryInterchange.Model .binary32 :=
  BinaryInterchange.Model.ofNatBits 0xC0200000

/-- `-2.3e-5` in binary64. -/
private abbrev mixedDouble : BinaryInterchange.Model .binary64 :=
  BinaryInterchange.Model.ofNatBits 0xBEF81E03F705857B

-- Mixed arithmetic on operands of different kinds is one projection of a class, a sign and a
-- ratio computed from the encodings: values of Binary8p4se, of binary32 and of binary64, and
-- rationals, in each operation of the report. The expected codes are those of the compiled
-- reference operations.
example :
    (P3109.Arithmetic.Mixed.Add mixedTarget mixedSingle mixedCode).toNatBits = 77 ∧
      (P3109.Arithmetic.Mixed.Subtract mixedTarget mixedCode mixedDouble).toNatBits = 68 ∧
      (P3109.Arithmetic.Mixed.Multiply mixedTarget mixedSingle mixedNegative).toNatBits = 209 ∧
      (P3109.Arithmetic.Mixed.Divide mixedTarget mixedCode mixedNegative .up
        .finite).toNatBits = 185 ∧
      (P3109.Arithmetic.Mixed.Recip mixedTarget mixedNegative).toNatBits = 181 ∧
      (P3109.Arithmetic.Mixed.FMA mixedTarget mixedSingle mixedCode mixedNegative).toNatBits =
        29 ∧
      (P3109.Arithmetic.Mixed.FAA mixedTarget mixedSingle mixedCode mixedDouble).toNatBits =
        77 := by
  float_decide

example :
    (P3109.Arithmetic.Mixed.Add mixedTarget mixedSingle (1 : Rat)).toNatBits = 75 ∧
      (P3109.Arithmetic.Mixed.Multiply mixedTarget mixedCode (3 / 4 : Rat)).toNatBits = 65 ∧
      (P3109.Arithmetic.Mixed.Convert mixedTarget (-5 / 3 : Rat)).toNatBits = 197 ∧
      (P3109.Arithmetic.Mixed.Add mixedTarget mixedCode
        (ExecFloat.P3109.ofNatBits 70 : B8P4)).toNatBits = 77 ∧
      (P3109.Arithmetic.Mixed.Divide mixedTarget mixedSingle (0 : Rat)).toNatBits = 128 := by
  float_decide

/-- Prepared P3109 stages preserve NaN precedence, zero divisors and signed root branches. -/
example :
    (ExecFloat.P3109.Divide (ExecFloat.P3109.ofNatBits 127 : B8P4) (0 : B8P4)).toNatBits = 128 ∧
      (ExecFloat.P3109.FMA (ExecFloat.P3109.ofNatBits 127 : B8P4)
        (0 : B8P4) (1 : B8P4)).toNatBits = 128 ∧
      (ExecFloat.P3109.Sqrt (ExecFloat.P3109.ofNatBits 192 : B8P4)).toNatBits = 128 ∧
      (ExecFloat.P3109.Sqrt (ExecFloat.P3109.ofNatBits 128 : B8P4)).toNatBits = 128 ∧
      (ExecFloat.P3109.RSqrt (0 : B8P4)).toNatBits = 128 ∧
      (ExecFloat.P3109.RSqrt (ExecFloat.P3109.ofNatBits 127 : B8P4)).toNatBits = 0 ∧
      (ExecFloat.P3109.Hypot (ExecFloat.P3109.ofNatBits 128 : B8P4)
        (ExecFloat.P3109.ofNatBits 127 : B8P4)).toNatBits = 128 := by
  float_decide

/-- Independent descriptors and saturation policies use the same prepared stages. -/
example :
    (ExecFloat.P3109.Add (1.5 : B8P4)
        (2.5 : ExecFloat.P3109 .binary8p3se)
        (target := P3109.Format.unsigned 16 5 .finite)).toNatBits =
      (4 : ExecFloat.P3109 (P3109.Format.unsigned 16 5 .finite)).toNatBits ∧
      (ExecFloat.P3109.Subtract (0 : B8P4) (1 : B8P4)
        (target := P3109.Format.unsigned 8 4 .extended)).toNatBits = 255 ∧
      (ExecFloat.P3109.Subtract (0 : B8P4) (1 : B8P4)
        (target := P3109.Format.unsigned 8 4 .extended)
        (saturation := .finite)).toNatBits = 0 ∧
      (ExecFloat.P3109.Add (ExecFloat.P3109.ofNatBits 127 : B8P4) (0 : B8P4)
        (saturation := .finite)).toNatBits = 126 ∧
      (ExecFloat.P3109.Add (ExecFloat.P3109.ofNatBits 127 : B8P4) (0 : B8P4)
        (saturation := .propagate)).toNatBits = 127 := by
  float_decide

/-- A supplied random word selects the same side of a midpoint after preparation. -/
example :
    (ExecFloat.P3109.Add (2 : B8P4) (0.125 : B8P4)).toNatBits = (2 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Add (2 : B8P4) (0.125 : B8P4)
        (mode := .up)).toNatBits = (2.25 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Add (2 : B8P4) (0.125 : B8P4)
        (mode := .stochasticA (.ofNat 1 0))).toNatBits = (2 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Add (2 : B8P4) (0.125 : B8P4)
        (mode := .stochasticA (.ofNat 1 1))).toNatBits = (2.25 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Add (2 : B8P4) (0.125 : B8P4)
        (mode := .stochasticB (.ofNat 1 1))).toNatBits = (2.25 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Add (2 : B8P4) (0.125 : B8P4)
        (mode := .stochasticC (.ofNat 1 0))).toNatBits = (2 : B8P4).toNatBits := by
  float_decide

/-- `x + y` and its siblings reach the flat operations on encodings (`P3109.KernelPath.Flat`)
through the reference operation and the public operation with the default policy. -/
example (x y z : B8P4) :
    x + y = ExecFloat.P3109.Add x y ∧ x - y = ExecFloat.P3109.Subtract x y ∧
      x * y = ExecFloat.P3109.Multiply x y ∧ x / y = ExecFloat.P3109.Divide x y ∧
      ExecFloat.fma x y z = ExecFloat.P3109.FMA x y z := by
  simp only [kernel_optimize, and_self]

/-- Negation, the absolute value, the fused multiply-add, the conversion between two descriptors
and a natural-number literal run on encodings. -/
example :
    (ExecFloat.P3109.Abs (ExecFloat.P3109.Negate (1.5 : B8P4))).toNatBits =
        (1.5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Negate (ExecFloat.P3109.Negate (1.5 : B8P4))).toNatBits =
        (1.5 : B8P4).toNatBits ∧
      ExecFloat.P3109.toNatBits (ExecFloat.fma (1.5 : B8P4) 2 0.25) = (3.25 : B8P4).toNatBits ∧
      (ExecFloat.P3109.projectRat (format := .binary8p3se) (1.5 : B8P4).toClosedRat).toNatBits =
        (1.5 : ExecFloat.P3109 .binary8p3se).toNatBits ∧
      ((3 : B8P4) - 1.75).toNatBits = (1.25 : B8P4).toNatBits := by
  float_decide

/-- The reciprocal, the fused add-add, the copy of a sign and the three square roots run on
encodings, in every rounding mode. -/
example :
    (ExecFloat.P3109.Recip (4 : B8P4)).toNatBits = (0.25 : B8P4).toNatBits ∧
      (ExecFloat.P3109.FAA (1.5 : B8P4) (2 : B8P4) (0.25 : B8P4)).toNatBits =
        (3.75 : B8P4).toNatBits ∧
      (ExecFloat.P3109.CopySign (1.5 : B8P4) (ExecFloat.P3109.Negate (2 : B8P4))).toNatBits =
        (ExecFloat.P3109.Negate (1.5 : B8P4)).toNatBits ∧
      (ExecFloat.P3109.Sqrt (2.25 : B8P4)).toNatBits = (1.5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Sqrt (2 : B8P4)).toNatBits = (1.375 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Sqrt (2 : B8P4) (mode := .up)).toNatBits = (1.5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Sqrt (2 : B8P4) (mode := .stochasticA (.ofNat 2 3))).toNatBits =
        (1.5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.RSqrt (4 : B8P4)).toNatBits = (0.5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Hypot (3 : B8P4) (4 : B8P4)).toNatBits = (5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.square (1.5 : B8P4)).toNatBits = (2.25 : B8P4).toNatBits := by
  float_decide

/-- The comparisons, the extrema and the clamp run on encodings: NaN is unordered, a number
variant ignores one NaN, a finite variant prefers a finite value to an infinity, and reversed
bounds give NaN. -/
example :
    ExecFloat.P3109.CompareLess (1.5 : B8P4) (2 : B8P4) = true ∧
      ExecFloat.P3109.CompareEqual (ExecFloat.P3109.ofNatBits 128 : B8P4)
        (ExecFloat.P3109.ofNatBits 128 : B8P4) = false ∧
      ExecFloat.P3109.CompareLessEqual (2 : B8P4) (2 : ExecFloat.P3109 .binary8p3se) = true ∧
      ExecFloat.P3109.CompareGreater (2 : B8P4) (1.5 : B8P4) = true ∧
      ExecFloat.P3109.CompareGreaterEqual (1.5 : B8P4) (2 : B8P4) = false ∧
      ExecFloat.P3109.compare (1.5 : B8P4) (2 : B8P4) = some .lt ∧
      (ExecFloat.P3109.Minimum (1.5 : B8P4) (2 : B8P4)).toNatBits = (1.5 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Maximum (ExecFloat.P3109.ofNatBits 128 : B8P4) (2 : B8P4)).toNatBits =
        128 ∧
      (ExecFloat.P3109.MaximumNumber (ExecFloat.P3109.ofNatBits 128 : B8P4)
        (2 : B8P4)).toNatBits = (2 : B8P4).toNatBits ∧
      (ExecFloat.P3109.MinimumMagnitude (ExecFloat.P3109.Negate (2 : B8P4))
        (2 : B8P4)).toNatBits = (ExecFloat.P3109.Negate (2 : B8P4)).toNatBits ∧
      (ExecFloat.P3109.MaximumMagnitudeNumber (ExecFloat.P3109.Negate (2 : B8P4))
        (2 : B8P4)).toNatBits = (2 : B8P4).toNatBits ∧
      (ExecFloat.P3109.MaximumFinite (ExecFloat.P3109.ofNatBits 127 : B8P4)
        (2 : B8P4)).toNatBits = (2 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Clamp (5 : B8P4) (1 : B8P4) (2 : B8P4)).toNatBits =
        (2 : B8P4).toNatBits ∧
      (ExecFloat.P3109.Clamp (5 : B8P4) (2 : B8P4) (1 : B8P4)).toNatBits = 128 := by
  float_decide

/-- The classification queries and the neighbours run on encodings. -/
example :
    ExecFloat.P3109.IsOne (1 : B8P4) = true ∧ ExecFloat.P3109.IsZero (0 : B8P4) = true ∧
      ExecFloat.P3109.IsNaN (ExecFloat.P3109.ofNatBits 128 : B8P4) = true ∧
      ExecFloat.P3109.IsInfinite (ExecFloat.P3109.ofNatBits 127 : B8P4) = true ∧
      ExecFloat.P3109.IsFinite (1.5 : B8P4) = true ∧
      ExecFloat.P3109.IsSignMinus (ExecFloat.P3109.Negate (1.5 : B8P4)) = true ∧
      ExecFloat.P3109.IsNormal (1.5 : B8P4) = true ∧
      ExecFloat.P3109.IsSubnormal (ExecFloat.P3109.ofNatBits 1 : B8P4) = true ∧
      (ExecFloat.P3109.NextGreaterThan (ExecFloat.P3109.ofNatBits 126 : B8P4)).toNatBits =
        127 ∧
      (ExecFloat.P3109.NextLessThan (0 : B8P4)).toNatBits = 129 := by
  float_decide

/-! ## The bipolar codebook -/

example (x y : ExecFloat.Codebook Formats.Codebook.Catalog.bipolar1) :
    x * y = ExecFloat.Spec.mul x y := by
  simp only [kernel_optimize]

/-! ## Posits -/

/-- The rules rewrite every posit operation to the direct dyadic form, at every built-in width. -/
example (x y z : Posit16) :
    x + y = Posit.Configured.Backend.dyadicAdd x y ∧
        x - y = Posit.Configured.Backend.dyadicSub x y ∧
      x * y = Posit.Configured.Backend.dyadicMul x y ∧
          x / y = Posit.Configured.Backend.dyadicDiv x y ∧
      ExecFloat.sqrt x = Posit.Configured.Backend.dyadicSqrt x ∧
      ExecFloat.fma x y z = Posit.Configured.Backend.dyadicFma x y z := by
  simp only [kernel_optimize, and_self]

example (x y : Posit8) : x + y = Posit.Configured.Backend.dyadicAdd x y := by
  simp only [kernel_optimize]

example (x y : Posit64) : ExecFloat.mul x y = Posit.Configured.Backend.dyadicMul x y := by
  simp only [kernel_optimize]

/-- A posit of a width without a packed carrier: the wide plan. -/
example (x y : ExecFloat.Posit (bits := 200)) : x / y = Posit.Configured.Backend.dyadicDiv x y := by
  simp only [kernel_optimize]

/-- `3 + 5 = 8` and `3 * 5 = 15` in posit8, on encodings. -/
example :
    ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C : Posit8) +
      ExecFloat.Posit.ofNatBits 0x52) = 0x58 ∧
    ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C : Posit8) *
      ExecFloat.Posit.ofNatBits 0x52) = 0x5F := by
  float_decide

/-- Prepared posit kernels preserve NaR even with zero operands, and exact cancellation. -/
example :
    ExecFloat.Posit.toNatBits
        ((ExecFloat.Posit.ofNatBits 0x80 : Posit8) + ExecFloat.Posit.ofNatBits 0) = 0x80 ∧
      ExecFloat.Posit.toNatBits
        ((ExecFloat.Posit.ofNatBits 0x80 : Posit8) * ExecFloat.Posit.ofNatBits 0) = 0x80 ∧
      ExecFloat.Posit.toNatBits
        ((ExecFloat.Posit.ofNatBits 0x4C : Posit8) - ExecFloat.Posit.ofNatBits 0x4C) = 0 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.fma (ExecFloat.Posit.ofNatBits 0x4C : Posit8)
          (ExecFloat.Posit.ofNatBits 0x52) (ExecFloat.Posit.ofNatBits 0xA1)) = 0 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.fma (ExecFloat.Posit.ofNatBits 0x80 : Posit8)
          (ExecFloat.Posit.ofNatBits 0) (ExecFloat.Posit.ofNatBits 0x4C)) = 0x80 := by
  float_decide

/-- Prepared quotient and root paths preserve their exceptional branches and finite signs. -/
example :
    ExecFloat.Posit.toNatBits
        ((ExecFloat.Posit.ofNatBits 0 : Posit8) / ExecFloat.Posit.ofNatBits 0) = 0x80 ∧
      ExecFloat.Posit.toNatBits
        ((ExecFloat.Posit.ofNatBits 0x80 : Posit8) / ExecFloat.Posit.ofNatBits 0x4C) = 0x80 ∧
      ExecFloat.Posit.toNatBits
        ((ExecFloat.Posit.ofNatBits 0xB4 : Posit8) / ExecFloat.Posit.ofNatBits 0x4C) = 0xC0 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.sqrt (ExecFloat.Posit.ofNatBits 0xB0 : Posit8)) = 0x80 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.sqrt (ExecFloat.Posit.ofNatBits 0x80 : Posit8)) = 0x80 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.sqrt (ExecFloat.Posit.ofNatBits 0 : Posit8)) = 0 := by
  float_decide

/-- `3 / 5`, `sqrt 4 = 2` and `3 * 5 + 1 = 16` in posit32, and NaR from a zero divisor. -/
example :
    ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C000000 : Posit32) /
      ExecFloat.Posit.ofNatBits 0x52000000) = 966367642 ∧
    ExecFloat.Posit.toNatBits (ExecFloat.sqrt (ExecFloat.Posit.ofNatBits 0x50000000 : Posit32)) =
      0x48000000 ∧
    ExecFloat.Posit.toNatBits (ExecFloat.fma (ExecFloat.Posit.ofNatBits 0x4C000000 : Posit32)
      (ExecFloat.Posit.ofNatBits 0x52000000) (ExecFloat.Posit.ofNatBits 0x40000000)) =
      0x60000000 ∧
    ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C000000 : Posit32) /
      ExecFloat.Posit.ofNatBits 0) = 0x80000000 := by
  float_decide

/-- Literals are rounded by the direct quotient kernel: `1.5 + 2.25 = 3.75`, a literal that is
not a dyadic number, and a natural literal. -/
example :
    ExecFloat.Posit.toNatBits ((1.5 : Posit16) + 2.25) =
        ExecFloat.Posit.toNatBits (3.75 : Posit16) ∧
      ExecFloat.Posit.toNatBits (0.1 : Posit32) = 617401549 ∧
      ExecFloat.Posit.toNatBits (3 : Posit16) = 19456 ∧
      ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofRat (1 / 3) : Posit8) = 51 := by
  float_decide

/-- A signed integer of 32 bits. -/
abbrev signed (value : Int) : Representations.FixedInt 32 :=
  Representations.FixedInt.ofInt value

/-- Posit Standard (2022), §6.4: integers of 32 bits are rounded by the flat ratio rounding of
their magnitude: a positive and a negative signed integer, the reserved word, which gives NaR,
an unsigned word and the reserved unsigned word. -/
example :
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofFixedInt (signed 12345) : Posit16) = 31106 ∧
      ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofFixedInt (signed (-7)) : Posit16) = 43520 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.Posit.ofFixedInt (signed (-2 ^ 31)) : Posit16) = 0x8000 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.Posit.ofUnsigned (BitVec.ofNat 32 12345) : Posit32) = 2038548480 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.Posit.ofUnsigned (BitVec.ofNat 32 (2 ^ 31)) : Posit32) = 0x80000000 := by
  float_decide

-- The compiled conversions give the same words.
#guard ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofFixedInt (signed 12345) : Posit16) == 31106
#guard ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofFixedInt (signed (-7)) : Posit16) == 43520
#guard ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofFixedInt (signed (-2 ^ 31)) : Posit16) ==
  0x8000
#guard ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofUnsigned (BitVec.ofNat 32 12345) : Posit32) ==
  2038548480

/-- The conversion of a signed integer is rewritten to the flat rounding of its word, for
every posit format and every positive width. -/
example (value : Representations.FixedInt 24) :
    Posit.Model.ofFixedInt (ExecFloat.Posit.descriptor 32) value =
      Posit.Model.ofNatBits
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat)
            (Posit.KernelPath.Flat.ofRatio (ExecFloat.Posit.descriptor 32).payloadBits 2 0
              value.toNatBits 1)
            (Posit.KernelPath.Flat.ofRatio (ExecFloat.Posit.descriptor 32).payloadBits 2 1
              (Nat.sub (Nat.pow 2 24) value.toNatBits) 1)
            (Nat.ble (Nat.pow 2 (Nat.sub 24 1)) value.toNatBits))
          (Posit.KernelPath.nar (ExecFloat.Posit.descriptor 32).payloadBits)
          (Nat.beq value.toNatBits (Nat.pow 2 (Nat.sub 24 1)))) := by
  simp only [kernel_optimize]

/-- Posit Standard (2022), §6.4: posits rounded to integers on the kernel path. The ties `1.5`
and `-2.5` go to the even integers `2` and `-2`, one half rounds to zero, the largest posit16
and NaR give the reserved word of eight bits, three converts to three, and a negative value
has no unsigned integer. -/
example :
    (ExecFloat.Posit.toFixedInt 8 (ExecFloat.Posit.ofNatBits 0x4400 : Posit16)).toNatBits = 2 ∧
      (ExecFloat.Posit.toFixedInt 8 (ExecFloat.Posit.ofNatBits 0xB600 : Posit16)).toNatBits =
        254 ∧
      (ExecFloat.Posit.toFixedInt 8 (ExecFloat.Posit.ofNatBits 0x3000 : Posit16)).toNatBits = 0 ∧
      (ExecFloat.Posit.toFixedInt 8 (ExecFloat.Posit.ofNatBits 0x7FFF : Posit16)).toNatBits =
        128 ∧
      (ExecFloat.Posit.toFixedInt 8 (ExecFloat.Posit.ofNatBits 0x8000 : Posit16)).toNatBits =
        128 ∧
      (ExecFloat.Posit.toFixedInt 32 (ExecFloat.Posit.ofNatBits 0x4C00 : Posit16)).toNatBits =
        3 ∧
      (ExecFloat.Posit.toUnsigned 8 (ExecFloat.Posit.ofNatBits 0xBC00 : Posit16)).toNat = 128 ∧
      (ExecFloat.Posit.toUnsigned 32 (ExecFloat.Posit.ofNatBits 0x4C000000 : Posit32)).toNat =
        3 := by
  float_decide

-- The compiled conversions give the same words.
#guard (ExecFloat.Posit.toFixedInt 8 (ExecFloat.Posit.ofNatBits 0x4400 : Posit16)).toNatBits == 2
#guard (ExecFloat.Posit.toFixedInt 8 (ExecFloat.Posit.ofNatBits 0xB600 : Posit16)).toNatBits ==
  254
#guard (ExecFloat.Posit.toFixedInt 8 (ExecFloat.Posit.ofNatBits 0x7FFF : Posit16)).toNatBits ==
  128
#guard (ExecFloat.Posit.toUnsigned 8 (ExecFloat.Posit.ofNatBits 0xBC00 : Posit16)).toNat == 128

-- On every word of posit8 and every integer width up to ten bits, the conversions on encodings
-- give the words of the compiled conversions.
#guard (List.range 256).all fun word =>
  (List.range 10).all fun k =>
    if h : 0 < k + 1 then
      (ExecFloat.Posit.toFixedInt (k + 1) (ExecFloat.Posit.ofNatBits word : Posit8) h).toNatBits ==
          Posit.KernelPath.toSigned 7 2 (k + 1) word &&
        (ExecFloat.Posit.toUnsigned (k + 1) (ExecFloat.Posit.ofNatBits word : Posit8) h).toNat ==
          Posit.KernelPath.toUnsigned 7 2 (k + 1) word
    else true

/-- The conversions to integers are rewritten to the flat conversions of the word, for every
posit format and every positive width. -/
example (x : Posit.Model (ExecFloat.Posit.descriptor 16)) :
    Posit.Model.toFixedInt 12 x =
        Representations.FixedInt.ofNatBits
          (Posit.KernelPath.Flat.toSigned (ExecFloat.Posit.descriptor 16).payloadBits 2 12
            x.toNatBits) ∧
      Posit.Model.toUnsigned 12 x =
        BitVec.ofNat 12
          (Posit.KernelPath.Flat.toUnsigned (ExecFloat.Posit.descriptor 16).payloadBits 2 12
            x.toNatBits) := by
  simp only [kernel_optimize, and_self]

/-- A rational is rounded by the flat ratio rounding on its numerator and denominator. -/
example (value : Rat) :
    (ExecFloat.Posit.ofRat value : Posit32) =
      ExecFloat.Posit.ofModel (Posit.Model.ofNatBits
        (Posit.KernelPath.Flat.ofRatio (ExecFloat.Posit.descriptor 32).payloadBits 2
          (Int.casesOn (motive := fun _ => Nat) value.num (fun _ => 0) (fun _ => 1))
          value.num.natAbs value.den)) := by
  simp only [kernel_optimize]

/-- Comparisons, negation, the absolute value and the neighbouring words on encodings. -/
example :
    ExecFloat.Posit.compareLess (ExecFloat.Posit.ofNatBits 0x4C : Posit8)
        (ExecFloat.Posit.ofNatBits 0x52) = true ∧
      ExecFloat.Posit.compareLess (ExecFloat.Posit.ofNatBits 0x80 : Posit8)
        (ExecFloat.Posit.ofNatBits 0xB4) = true ∧
      ExecFloat.Posit.compareLessEqual (ExecFloat.Posit.ofNatBits 0x52 : Posit8)
        (ExecFloat.Posit.ofNatBits 0x4C) = false ∧
      ExecFloat.Posit.compareGreaterEqual (ExecFloat.Posit.ofNatBits 0x52 : Posit8)
        (ExecFloat.Posit.ofNatBits 0x52) = true ∧
      ExecFloat.Posit.compareEqual (ExecFloat.Posit.ofNatBits 0x80 : Posit8)
        (ExecFloat.Posit.ofNatBits 0x80) = true ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.Posit.negate (ExecFloat.Posit.ofNatBits 0x4C : Posit8)) = 0xB4 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.Posit.abs (ExecFloat.Posit.ofNatBits 0xB4 : Posit8)) = 0x4C ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.Posit.next (ExecFloat.Posit.ofNatBits 0xFF : Posit8)) = 0 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.Posit.prior (ExecFloat.Posit.ofNatBits 0 : Posit8)) = 0xFF := by
  float_decide

/-- The rounding of a quire is rewritten to the flat rounding of its word, for every posit
format. -/
example (q : Formats.Posit.Quire.Model (ExecFloat.Posit.descriptor 16)) :
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.Quire.qToP q : Posit16) =
      Nat.mod (Formats.Posit.KernelPath.Flat.quireRound
        (ExecFloat.Posit.descriptor 16).payloadBits q.toNatBits) (Nat.pow 2 16) := by
  simp only [kernel_optimize]

/-- Three in posit16. -/
abbrev three : Posit16 := ExecFloat.Posit.ofNatBits 0x4C00

/-- Five in posit16. -/
abbrev five : Posit16 := ExecFloat.Posit.ofNatBits 0x5200

/-- `3 + 3 * 5 = 18` accumulated in the quire of posit16 and rounded once. -/
example :
    ExecFloat.Posit.toNatBits
        (ExecFloat.Posit.Quire.qToP
          (ExecFloat.Posit.Quire.qMulAdd (ExecFloat.Posit.Quire.pToQ three) three five) :
            Posit16) =
      24704 := by
  float_decide

/-! ## OCP MX element conversion -/

section MX

open FloatLib.Floats.Formats.OCP.MX Standard

/-- The rule rewrites nearest-even element rounding to the bisection, for every profile and
input. -/
example (profile : Profile) (input : SignedRat) :
    Element.quantizeFinite profile input =
      BitVec.ofNat profile.width (Element.roundCode profile input) := by
  simp only [kernel_optimize]

/-- The bisection and the scan of all codes give the same entry: a tie between two codes, an
input below the smallest magnitude, a negative input, and an input beyond the largest finite
magnitude of E5M2. -/
example :
    Element.scan .e4m3 0 0 464 1 256 = some (Element.nearestAll .e4m3 0 0 464 1) ∧
      Element.scan .e2m3 0 0 1 1000 64 = some (Element.nearestAll .e2m3 0 0 1 1000) ∧
      Element.scan .e2m1 1 1 7 3 16 = some (Element.nearestAll .e2m1 1 1 7 3) ∧
      Element.scan .e5m2 0 0 100000 1 256 = some (Element.nearestAll .e5m2 0 0 100000 1) := by
  decide +kernel

/-- The same for INT8: a negative input, an input below the smallest magnitude, the two ends of
the range, and a negative zero. -/
example :
    Element.scan .int8 1 1 7 3 256 = some (Element.nearestAll .int8 1 1 7 3) ∧
      Element.scan .int8 1 1 1 1000 256 = some (Element.nearestAll .int8 1 1 1 1000) ∧
      Element.scan .int8 1 1 1000 1 256 = some (Element.nearestAll .int8 1 1 1000 1) ∧
      Element.scan .int8 0 0 1000 1 256 = some (Element.nearestAll .int8 0 0 1000 1) ∧
      Element.scan .int8 0 1 0 1 256 = some (Element.nearestAll .int8 0 1 0 1) := by
  decide +kernel

/-- The guessed form gives the entry of the bisection: a tie between two codes, an input below
the smallest magnitude, a negative input, an input beyond the largest finite magnitude, and the
same for INT8 with the two ends of its range and a negative zero. -/
example :
    Element.nearestFast .e4m3 0 0 464 1 = Element.nearestAll .e4m3 0 0 464 1 ∧
      Element.nearestFast .e2m3 0 0 1 1000 = Element.nearestAll .e2m3 0 0 1 1000 ∧
      Element.nearestFast .e2m1 1 1 7 3 = Element.nearestAll .e2m1 1 1 7 3 ∧
      Element.nearestFast .e5m2 0 0 100000 1 = Element.nearestAll .e5m2 0 0 100000 1 ∧
      Element.nearestFast .e3m2 1 1 5 2 = Element.nearestAll .e3m2 1 1 5 2 ∧
      Element.nearestFast .int8 1 1 7 3 = Element.nearestAll .int8 1 1 7 3 ∧
      Element.nearestFast .int8 1 1 1000 1 = Element.nearestAll .int8 1 1 1000 1 ∧
      Element.nearestFast .int8 0 0 1000 1 = Element.nearestAll .int8 0 0 1000 1 ∧
      Element.nearestFast .int8 0 1 0 1 = Element.nearestAll .int8 0 1 0 1 := by
  decide +kernel

/-- The guess of the field is the field that the bisection finds, so the guessed form does not
run the bisection: on 1,200 inputs of E4M3 and of E5M2, from zero to beyond the largest
magnitude, on 240 inputs of E2M1, and on 1,200 inputs of INT8 with both signs. -/
example :
    ((List.range 300).all fun ap => (List.range 4).all fun k =>
        Nat.beq (Element.fieldGuess .e4m3 (ap * 512) (2 * k + 1))
            (Kernel.bisect (Element.below .e4m3 (ap * 512) (2 * k + 1)) 7 0) &&
          Nat.beq (Element.fieldGuess .e5m2 (ap * 65536) (2 * k + 1))
            (Kernel.bisect (Element.below .e5m2 (ap * 65536) (2 * k + 1)) 7 0)) = true ∧
      ((List.range 60).all fun ap => (List.range 4).all fun k =>
        Nat.beq (Element.fieldGuess .e2m1 (ap * 2) (2 * k + 1))
          (Kernel.bisect (Element.below .e2m1 (ap * 2) (2 * k + 1)) 3 0)) = true ∧
      ((List.range 150).all fun ap => (List.range 4).all fun k => (List.range 2).all fun sp =>
        Nat.beq (Element.int8Guess sp (ap * 64) (2 * k + 1))
          (Kernel.bisect (Element.int8Below sp (ap * 64) (2 * k + 1)) 8 0)) = true := by
  decide +kernel

/-- The rewrite turns the bisection form into the guessed form, for every profile and
input. -/
example (profile : Profile) (sp neg ap q : Nat) :
    Element.nearestAll profile sp neg ap q = Element.nearestFast profile sp neg ap q := by
  simp only [kernel_optimize]

/-- The kernel shape of the rounded code reads the sign bits by recursors and the numerator by
the kernel arithmetic of `Int`, and it is the rounded code: a positive, a negative and a zero
input in a sign-magnitude profile and in INT8. -/
example :
    Element.roundCode.kernel .e4m3 (SignedRat.ofRat (7 / 3)) =
        Element.roundCode .e4m3 (SignedRat.ofRat (7 / 3)) ∧
      Element.roundCode.kernel .e2m3 (SignedRat.ofRat (-5 / 8)) =
        Element.roundCode .e2m3 (SignedRat.ofRat (-5 / 8)) ∧
      Element.roundCode.kernel .int8 (SignedRat.ofRat (-7 / 3)) =
        Element.roundCode .int8 (SignedRat.ofRat (-7 / 3)) ∧
      Element.roundCode.kernel .e5m2 SignedRat.negZero =
        Element.roundCode .e5m2 SignedRat.negZero := by
  decide +kernel

/-- Under the saturating mode the rewrite leaves the rounded code and its width, without the
test of the overflow mode. -/
example (profile : Profile) (input : SignedRat) :
    (Element.quantize profile (.finite input) .saturate).toNat =
      Nat.mod (Element.roundCode.kernel profile input) (Nat.pow 2 profile.width) := by
  simp only [kernel_optimize]

/-- Quantize a rational scalar and read the element code. -/
abbrev scalar (profile : Profile) (overflow : OverflowMode) (value : Rat) : Nat :=
  (Element.quantize profile (.finite (SignedRat.ofRat value)) overflow).toNat

/-- Interior values: `7/3` rounds to `2.25` in E4M3 and to `2.5` in E5M2. -/
example : scalar .e4m3 .saturate (7 / 3) = 65 ∧ scalar .e5m2 .saturate (7 / 3) = 65 := by
  float_decide

/-- The E4M3 midpoint 464 rounds to the even finite 448, and 465 overflows in OVF mode. -/
example :
    scalar .e4m3 .native 464 = 126 ∧ scalar .e4m3 .native 465 = 127 ∧
      scalar .e4m3 .saturate 1000 = 126 ∧ scalar .e4m3 .native (-464) = 254 := by
  float_decide

/-- Saturation of the narrow profiles and the asymmetric INT8 range. -/
example :
    scalar .e2m1 .saturate 5 = 6 ∧ scalar .e2m1 .saturate 100 = 7 ∧
      scalar .e2m3 .saturate 100 = 31 ∧ scalar .e3m2 .saturate 100 = 31 ∧
      scalar .int8 .saturate (-2) = 128 ∧ scalar .int8 .saturate 2 = 127 := by
  float_decide

/-- A negative zero input keeps its sign in a floating profile. -/
example :
    (Element.quantize .e2m1 (.finite SignedRat.negZero) .saturate).toNat = 8 := by
  float_decide

/-- Four inputs that share one block. -/
def inputs : Fin 4 → SignedRat := fun i => SignedRat.ofRat (((i.val : Rat) + 1) * 7 / 3)

/-- A stored element of a quantized block is rewritten to the element conversion, for every
profile, grouping, policy and input. -/
example {ι γ : Type} (group : ι → γ) (profile : Profile) (selection : Block.Policy ι γ)
    (x : ι → SignedRat) (i : ι) :
    ((format group profile).quantize selection x).elements i =
      Element.quantize profile
        (.finite (x i * SignedRat.ofRat
          (1 / ((format group profile).toFormat selection).scale (fun j => (x j).value) i)))
        .saturate := by
  simp only [kernel_optimize]

/-- The third element of the block `7/3, 14/3, 7, 28/3` under the standard scale selection. -/
example :
    (((format (fun _ : Fin 4 => ()) .e4m3).quantize (policy (fun _ : Fin 4 => ()) .e4m3)
      inputs).elements 2).toNat = 118 ∧
    (((format (fun _ : Fin 4 => ()) .e2m1).quantize (policy (fun _ : Fin 4 => ()) .e2m1)
      inputs).elements 2).toNat = 6 := by
  float_decide

/-- The values that two positions store at the scale `1 / 32`, which the largest input `28 / 3`
selects: `7` is kept, and `7 / 3` is rounded to `72 / 32`. -/
example :
    ((format (fun _ : Fin 4 => ()) .e4m3).quantize (policy (fun _ : Fin 4 => ()) .e4m3)
      inputs).value 2 = 7 ∧
    ((format (fun _ : Fin 4 => ()) .e4m3).quantize (policy (fun _ : Fin 4 => ()) .e4m3)
      inputs).value 0 = 9 / 4 := by
  float_decide

/-- The largest magnitude of a group over `Fin n` is rewritten to the loop on natural numbers,
for every grouping and data. -/
example {n : Nat} {γ : Type} [DecidableEq γ] (group : Fin n → γ) (y : Fin n → ℚ) (g : γ) :
    Block.amax group y g =
      mkRat (Int.ofNat (Block.amaxLoop group y g n).1) (Block.amaxLoop group y g n).2 := by
  simp only [kernel_optimize]

/-- The largest magnitudes of one block of four, of two blocks of two, and of an empty group. -/
example :
    Block.amax (fun _ : Fin 4 => ()) (fun j => (inputs j).value) () = 28 / 3 ∧
      Block.amax (fun i : Fin 4 => i.val / 2) (fun j => (inputs j).value) 0 = 14 / 3 ∧
      Block.amax (fun i : Fin 4 => i.val / 2) (fun j => -(inputs j).value) 1 = 28 / 3 ∧
      Block.amax (fun i : Fin 4 => i.val / 2) (fun j => (inputs j).value) 7 = 0 := by
  float_decide

/-- The scale of a block under the standard policy is rewritten to the E8M0 rounding of its
largest magnitude, for every profile, grouping and data. -/
example {ι γ : Type} [Fintype ι] [DecidableEq γ] (group : ι → γ) (profile : Profile)
    (y : ι → ℚ) (i : ι) :
    ((format group profile).toFormat (policy group profile)).scale y i =
      E8M0.codec.rounding.round
        (if Block.amax group y (group i) = 0 then 1
          else Block.amax group y (group i) / 2 ^ profile.maxPowerExponent) := by
  simp only [kernel_optimize]

/-- Thirty-two inputs that share one block. -/
def block : Fin 32 → SignedRat := fun i => SignedRat.ofRat (((i.val : Rat) + 1) * 7 / 3)

/-- A statement about all 32 positions of a standard block: the sum of the stored E4M3 codes.
The rewritten scale does not mention the position, so the kernel evaluates it once. -/
example :
    Nat.rec (motive := fun _ => Nat) 0
      (fun i sum =>
        if h : i < 32 then
          sum + (((format (fun _ : Fin 32 => ()) .e4m3).quantize
            (policy (fun _ : Fin 32 => ()) .e4m3) block).elements ⟨i, h⟩).toNat
        else sum) 32 = 3542 := by
  float_decide

/-- Dequantization: the rule rewrites the value of a decoded word to the value of its code, for
every profile and word, and the value of a position of a stored tensor with it. -/
example (profile : Profile) (word : Element profile) :
    Block.finiteValue (Element.decode word) = Element.codeValue profile word.toNat := by
  simp only [kernel_optimize]

example {ι γ : Type} {group : ι → γ} {profile : Profile}
    (t : Block.Tensor (format group profile)) (i : ι) :
    t.value i =
      Element.codeValue profile (BitVec.toNat (w := profile.width) (t.elements i)) *
        t.scale i := by
  simp only [kernel_optimize]

/-- The values of an E4M3 word, an E5M2 infinity (no finite value), a negative INT8 word and a
negative E2M1 zero. -/
example :
    Block.finiteValue (Element.decode (profile := .e4m3) (BitVec.ofNat 8 65)) = 9 / 4 ∧
      Block.finiteValue (Element.decode (profile := .e5m2) (BitVec.ofNat 8 124)) = 0 ∧
      Block.finiteValue (Element.decode (profile := .int8) (BitVec.ofNat 8 200)) = -7 / 8 ∧
      Block.finiteValue (Element.decode (profile := .e2m1) (BitVec.ofNat 4 8)) = 0 := by
  float_decide

end MX

end FloatLibTests.Conformance.Formats.KernelPaths
