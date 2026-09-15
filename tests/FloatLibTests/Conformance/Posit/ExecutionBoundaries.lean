/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit

/-!
# Posit execution across storage boundaries

`ExecFloat.Posit n` is one arbitrary-width public family. The implementation chooses a byte,
native word, two-limb pair, or wide exact carrier from the static width; those carriers are not
separate numerical types.

These native conformance gates execute all six public arithmetic operations immediately below and
above every carrier boundary. They complement the refinement certificates by catching failures in
monomorphic specialization, carrier packing, and generated runtime code. The 4096-bit case also
exercises the same arbitrary-width backend used by every larger static width.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Posit.ExecutionBoundaries

open FloatLib.Floats

/--
Run representative exact arithmetic and exceptional cases at one ordinary posit width.

The chosen rational results are exactly representable from posit8 onward. Testing exact values
keeps this gate independent of a width-specific expected bit pattern.
-/
def arithmeticPasses
    (bits : Nat) (bits_ge_two : 2 ≤ bits) : Bool :=
  let six : ExecFloat.Posit bits bits_ge_two := 6
  let four : ExecFloat.Posit bits bits_ge_two := 4
  let two : ExecFloat.Posit bits bits_ge_two := 2
  let one : ExecFloat.Posit bits bits_ge_two := 1
  let zero : ExecFloat.Posit bits bits_ge_two := 0
  let nar : ExecFloat.Posit bits bits_ge_two := ExecFloat.Posit.nar
  ExecFloat.Posit.toRat? (ExecFloat.add six four) == some 10 &&
    ExecFloat.Posit.toRat? (ExecFloat.sub six four) == some 2 &&
    ExecFloat.Posit.toRat? (ExecFloat.mul six four) == some 24 &&
    ExecFloat.Posit.toRat? (ExecFloat.div six four) ==
      some ((3 : Rat) / 2) &&
    ExecFloat.Posit.toRat? (ExecFloat.sqrt four) == some 2 &&
    ExecFloat.Posit.toRat? (ExecFloat.fma two two one) == some 5 &&
    ExecFloat.Posit.isNaR (ExecFloat.div six zero) &&
    ExecFloat.Posit.isNaR (ExecFloat.sqrt (-one)) &&
    ExecFloat.Posit.isNaR (ExecFloat.fma nar four one)

/--
The smallest standard posit still executes every public operation through the common API.

Posit2 represents only zero, one, NaR, and negative one, so its expected results intentionally
express saturation rather than the wider-format arithmetic used below.
-/
theorem posit2_executes_all_operations :
    let one : ExecFloat.Posit 2 := 1
    let zero : ExecFloat.Posit 2 := 0
    ExecFloat.Posit.toRat? (ExecFloat.add one one) = some 1 ∧
      ExecFloat.Posit.toRat? (ExecFloat.sub one one) = some 0 ∧
      ExecFloat.Posit.toRat? (ExecFloat.mul one one) = some 1 ∧
      ExecFloat.Posit.toRat? (ExecFloat.div one one) = some 1 ∧
      ExecFloat.Posit.toRat? (ExecFloat.sqrt one) = some 1 ∧
      ExecFloat.Posit.toRat? (ExecFloat.fma one one one) = some 1 ∧
      ExecFloat.Posit.isNaR (ExecFloat.div one zero) = true := by
  native_decide

/-!
The paired widths straddle the byte, `UInt16`, `UInt32`, `UInt64`, and two-limb cutoffs. These
theorems call only `ExecFloat` operations; no test names or constructs an internal carrier.
-/

theorem posit8_execution : arithmeticPasses 8 (by decide) = true := by
  native_decide

theorem posit9_execution : arithmeticPasses 9 (by decide) = true := by
  native_decide

theorem posit16_execution : arithmeticPasses 16 (by decide) = true := by
  native_decide

/--
Two exact halfway-adjacent FMA cases found by the SoftPosit differential campaign.

FloatLib's public kernel and independent rational specification both choose the listed word.
Keeping the cases here means a later rounding or carrier change cannot turn an explained external
disagreement into an unnoticed regression.
-/
theorem posit16_softposit_fma_boundaries :
    let firstLeft : ExecFloat.Posit 16 := ExecFloat.Posit.ofNatBits 0x80ae
    let firstRight : ExecFloat.Posit 16 := ExecFloat.Posit.ofNatBits 0x3a00
    let firstAddend : ExecFloat.Posit 16 := ExecFloat.Posit.ofNatBits 0xfffd
    let secondLeft : ExecFloat.Posit 16 := ExecFloat.Posit.ofNatBits 0x7680
    let secondRight : ExecFloat.Posit 16 := ExecFloat.Posit.ofNatBits 0x6128
    let secondAddend : ExecFloat.Posit 16 := ExecFloat.Posit.ofNatBits 0x0001
    ExecFloat.Posit.toNatBits
        (ExecFloat.fma firstLeft firstRight firstAddend) = 0x80c1 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.fma secondLeft secondRight secondAddend) = 0x7b9d := by
  native_decide

theorem posit17_execution : arithmeticPasses 17 (by decide) = true := by
  native_decide

theorem posit32_execution : arithmeticPasses 32 (by decide) = true := by
  native_decide

/--
The generic SoftPosit `pX2(32)` path disagrees with both its named `p32` path and FloatLib's exact
specification on these adjacent-word cases. We retain the concrete public results while the raw
external campaign records every observed disagreement.
-/
theorem posit32_softposit_px2_boundaries :
    let tinyNegative : ExecFloat.Posit 32 :=
      ExecFloat.Posit.ofNatBits 0xfffffffd
    let smallerTinyNegative : ExecFloat.Posit 32 :=
      ExecFloat.Posit.ofNatBits 0xfffffffe
    let belowNegativeOne : ExecFloat.Posit 32 :=
      ExecFloat.Posit.ofNatBits 0xbfffffff
    ExecFloat.Posit.toNatBits
        (ExecFloat.add tinyNegative smallerTinyNegative) = 0xfffffffd ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.mul belowNegativeOne tinyNegative) = 0x00000003 ∧
      ExecFloat.Posit.toNatBits
        (ExecFloat.div belowNegativeOne tinyNegative) = 0x7ffffffd := by
  native_decide

theorem posit33_execution : arithmeticPasses 33 (by decide) = true := by
  native_decide

theorem posit64_execution : arithmeticPasses 64 (by decide) = true := by
  native_decide

theorem posit65_execution : arithmeticPasses 65 (by decide) = true := by
  native_decide

theorem posit128_execution : arithmeticPasses 128 (by decide) = true := by
  native_decide

theorem posit129_execution : arithmeticPasses 129 (by decide) = true := by
  native_decide

theorem posit4096_execution : arithmeticPasses 4096 (by decide) = true := by
  native_decide

end FloatLibTests.Conformance.Posit.ExecutionBoundaries
