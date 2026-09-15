/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Type
public import FloatLib.Floats.Formats.Posit.Quire.Arithmetic.Runtime
public import FloatLibTests.Accounting

/-!
# Posit quire conformance

These checks exercise the current Posit Standard's `16n`-bit quire independently of its configured
storage carrier. Conversion covers every posit word through eight bits; exact product accumulation
covers every operand pair through five bits.

The Boolean predicates serve two purposes without introducing two specifications. Closed theorems
reduce them in Lean's kernel, while the native validation executable reports the same predicates as
a fast regression suite.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 5, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

-- Keep lazy regression bodies out of module initialization, including closed subexpressions.
-- This affects native code generation only; elaboration and kernel checking are unchanged.
set_option compiler.extract_closed false

namespace FloatLibTests.Conformance.Posit.Quire

open FloatLib.Floats.Formats.Posit
open FloatLibTests.Accounting

/-! ## Exact conversion -/

/-- Check exact posit-to-quire-to-posit conversion for one encoded word. -/
def conversionRoundTripAt (format : Format) (bits : Nat) : Bool :=
  let value := Model.ofNatBits (format := format) bits
  Quire.Model.qToP (Quire.Model.pToQ value) == value

/-- Count conversion failures over every word of one closed posit descriptor. -/
def conversionRoundTripFailures (format : Format) : Nat :=
  countWhereFailures (List.range format.modulus)
    (conversionRoundTripAt format)

/--
Every posit word through eight bits converts exactly into its standard quire and back.

Zero and NaR use the same executable path as ordinary values.
-/
theorem posit2_all_quire_conversion_round_trips :
    conversionRoundTripFailures
      (FloatLib.Floats.ExecFloat.Posit.format 2) = 0 := by
  decide +kernel

/-- Every three-bit posit word converts exactly into its standard quire and back. -/
theorem posit3_all_quire_conversion_round_trips :
    conversionRoundTripFailures
      (FloatLib.Floats.ExecFloat.Posit.format 3) = 0 := by
  decide +kernel

/-- Every four-bit posit word converts exactly into its standard quire and back. -/
theorem posit4_all_quire_conversion_round_trips :
    conversionRoundTripFailures
      (FloatLib.Floats.ExecFloat.Posit.format 4) = 0 := by
  decide +kernel

/-- Every five-bit posit word converts exactly into its standard quire and back. -/
theorem posit5_all_quire_conversion_round_trips :
    conversionRoundTripFailures
      (FloatLib.Floats.ExecFloat.Posit.format 5) = 0 := by
  decide +kernel

/-- Every six-bit posit word converts exactly into its standard quire and back. -/
theorem posit6_all_quire_conversion_round_trips :
    conversionRoundTripFailures
      (FloatLib.Floats.ExecFloat.Posit.format 6) = 0 := by
  decide +kernel

/-- Every seven-bit posit word converts exactly into its standard quire and back. -/
theorem posit7_all_quire_conversion_round_trips :
    conversionRoundTripFailures
      (FloatLib.Floats.ExecFloat.Posit.format 7) = 0 := by
  decide +kernel

/-- Every eight-bit posit word converts exactly into its standard quire and back. -/
theorem posit8_all_quire_conversion_round_trips :
    conversionRoundTripFailures
      (FloatLib.Floats.ExecFloat.Posit.format 8) = 0 := by
  decide +kernel

/-! ## Exact product accumulation -/

/-- Check one exact quire product against certified ordinary posit multiplication. -/
def productRefinesAt
    (format : Format) (leftBits rightBits : Nat) : Bool :=
  let left := Model.ofNatBits (format := format) leftBits
  let right := Model.ofNatBits (format := format) rightBits
  Quire.Model.qToP
      (Quire.Model.qMulAdd (Quire.Model.zero format) left right) ==
    Model.DyadicArithmetic.mul left right

/-- Count product-refinement failures over every operand pair of one descriptor. -/
def productRefinementFailures (format : Format) : Nat :=
  let words := List.range format.modulus
  countPairFailures words words (productRefinesAt format)

/--
Every operand pair through five bits agrees between exact quire product accumulation followed by
one `qToP` rounding and the certified direct posit multiplication kernel.
-/
theorem posit2_all_quire_products_refine :
    productRefinementFailures
      (FloatLib.Floats.ExecFloat.Posit.format 2) = 0 := by
  decide +kernel

/-- Every three-bit operand pair agrees with certified direct posit multiplication. -/
theorem posit3_all_quire_products_refine :
    productRefinementFailures
      (FloatLib.Floats.ExecFloat.Posit.format 3) = 0 := by
  decide +kernel

/-- Every four-bit operand pair agrees with certified direct posit multiplication. -/
theorem posit4_all_quire_products_refine :
    productRefinementFailures
      (FloatLib.Floats.ExecFloat.Posit.format 4) = 0 := by
  decide +kernel

/-- Every five-bit operand pair agrees with certified direct posit multiplication. -/
theorem posit5_all_quire_products_refine :
    productRefinementFailures
      (FloatLib.Floats.ExecFloat.Posit.format 5) = 0 := by
  decide +kernel

/-! ## Standard posit8 boundaries -/

/-- Posit8 uses the standard 128-bit quire with least-significant-bit scale `2^-48`. -/
theorem posit8_quire_shape :
    let format := FloatLib.Floats.ExecFloat.Posit.format 8
    Quire.width format = 128 ∧
      Quire.scaleExponent format = -48 := by
  decide +kernel

/-- Exact accumulation retains `1.5 × 2.25 = 27/8` before final posit rounding. -/
theorem posit8_quire_exact_product :
    let format := FloatLib.Floats.ExecFloat.Posit.format 8
    let left := Model.roundRat format ((3 : Rat) / 2)
    let right := Model.roundRat format ((9 : Rat) / 4)
    (Quire.Model.qMulAdd (Quire.Model.zero format) left right).toRat? =
      some ((27 : Rat) / 8) := by
  decide +kernel

/--
Adding one least-significant quire unit to the greatest ordinary coefficient overflows to the
reserved quire NaR word.
-/
theorem posit8_quire_positive_overflow_is_nar :
    let format := FloatLib.Floats.ExecFloat.Posit.format 8
    let maximum :=
      Quire.Model.ofCoefficient format
        (FloatLib.Numerics.Representations.FixedInt.maxValue
          (Quire.width format))
    let one := Quire.Model.ofCoefficient format 1
    Quire.Model.qAddQ maximum one = Quire.Model.nar format := by
  decide +kernel

/-- NaR input propagates through exact fused accumulation and final rounding. -/
theorem posit8_quire_nar_propagation :
    let format := FloatLib.Floats.ExecFloat.Posit.format 8
    let one := Model.roundRat format 1
    Quire.Model.qMulAdd
        (Quire.Model.zero format) (Model.nar format) one =
        Quire.Model.nar format ∧
      Quire.Model.qToP (Quire.Model.nar format) =
        Model.nar format := by
  decide +kernel

/-- Count failures in the four posit8 boundary checks proved above. -/
def boundaryFailures : Thunk Nat := ⟨fun _ =>
  let format := FloatLib.Floats.ExecFloat.Posit.format 8
  let one := Model.roundRat format 1
  let left := Model.roundRat format ((3 : Rat) / 2)
  let right := Model.roundRat format ((9 : Rat) / 4)
  let maximum :=
    Quire.Model.ofCoefficient format
      (FloatLib.Numerics.Representations.FixedInt.maxValue
        (Quire.width format))
  let unit := Quire.Model.ofCoefficient format 1
  countFailures
    [ Quire.width format == 128 && Quire.scaleExponent format == -48
    , (Quire.Model.qMulAdd (Quire.Model.zero format) left right).toRat? ==
        some ((27 : Rat) / 8)
    , Quire.Model.qAddQ maximum unit == Quire.Model.nar format
    , (Quire.Model.qMulAdd
          (Quire.Model.zero format) (Model.nar format) one ==
          Quire.Model.nar format) &&
        Quire.Model.qToP (Quire.Model.nar format) == Model.nar format
    ]⟩

/--
Total failures in the closed quire corpus used by the native kernel runner.

The individual properties remain kernel-checked above; this count is their executable view.
-/
def totalFailures : Thunk Nat := ⟨fun _ =>
  let conversionFormats : List Format :=
    [ FloatLib.Floats.ExecFloat.Posit.format 2
    , FloatLib.Floats.ExecFloat.Posit.format 3
    , FloatLib.Floats.ExecFloat.Posit.format 4
    , FloatLib.Floats.ExecFloat.Posit.format 5
    , FloatLib.Floats.ExecFloat.Posit.format 6
    , FloatLib.Floats.ExecFloat.Posit.format 7
    , FloatLib.Floats.ExecFloat.Posit.format 8
    ]
  let productFormats : List Format :=
    [ FloatLib.Floats.ExecFloat.Posit.format 2
    , FloatLib.Floats.ExecFloat.Posit.format 3
    , FloatLib.Floats.ExecFloat.Posit.format 4
    , FloatLib.Floats.ExecFloat.Posit.format 5
    ]
  let conversionFailures :=
    (conversionFormats.map conversionRoundTripFailures).sum
  let productFailures :=
    (productFormats.map productRefinementFailures).sum
  conversionFailures + productFailures + boundaryFailures.get⟩

end FloatLibTests.Conformance.Posit.Quire
