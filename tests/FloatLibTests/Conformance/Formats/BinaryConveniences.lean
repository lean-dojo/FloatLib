/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib

/-!
# Configured binary conveniences

Checks for the configured binary API that a program reaches first: rounding a rational with
`ofRat`, reading an integer with `toInt?`, the format constants and `ulp`, the native `Float` and
`Float32` conversions at every width, status composition with `IEEEOutcome.bind`, and the real-value
adapters `toReal_add` through `abs_toReal_sqrt_sub_le`. Closed cases are decided by the kernel.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.BinaryConveniences

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

-- `ofRat` rounds once, in any direction. With `status := true` it reports inexactness and the
-- ternary value, and an exact rational stays exact.
example :
    (ExecFloat.Binary.ofRat (1 / 3) : Binary32).toNatBits = 0x3eaaaaab ∧
      (ExecFloat.Binary.ofRat (1 / 3) (mode := .down) : Binary32).toNatBits = 0x3eaaaaaa ∧
      (ExecFloat.Binary.ofRat (-1 / 3) (mode := .towardZero) : Binary32).toNatBits =
        0xbeaaaaaa ∧
      (ExecFloat.Binary.ofRat (3 / 2) : BFloat16).toNatBits = 0x3fc0 := by
  decide +kernel

example :
    let third := ExecFloat.Binary.ofRat (1 / 3) (mode := .up) (status := true)
    (third.value : Binary32).toNatBits = 0x3eaaaaab ∧ third.status.inexact = true ∧
      third.ternary = .gt := by
  decide +kernel

example :
    let half := ExecFloat.Binary.ofRat (1 / 2) (status := true)
    (half.value : Binary16).toNatBits = 0x3800 ∧ half.status = .clear ∧ half.ternary = .eq := by
  decide +kernel

-- Literals are `ofRat` to nearest.
example : (0.1 : Binary32) = ExecFloat.Binary.ofRat (1 / 10) := by decide +kernel

-- `toInt?` truncates by default, rounds in any direction, and has no value for NaN or infinity.
example :
    (2.5 : Binary32).toInt? = some 2 ∧ (2.5 : Binary32).toInt? (mode := .nearest) = some 2 ∧
      (3.5 : Binary32).toInt? (mode := .nearest) = some 4 ∧
      (-2.5 : Binary32).toInt? (mode := .down) = some (-3) ∧
      (-2.5 : Binary32).toInt? (mode := .up) = some (-2) ∧
      (1e30 : Binary32).toInt? = some 1000000015047466219876688855040 ∧
      (ExecFloat.Binary.canonicalNaN : Binary32).toInt? = none ∧
      (ExecFloat.Binary.infinity (sign := true) : Binary32).toInt? = none := by
  decide +kernel

example (x : Binary32) (hx : x.isFinite = false) : x.toInt? = none :=
  (ExecFloat.Binary.toInt?_eq_none_iff x .towardZero).2 hx

-- The special values are positive by default.
example :
    (ExecFloat.Binary.zero : Binary32).toNatBits = 0 ∧
      (ExecFloat.Binary.zero (sign := true) : Binary32).toNatBits = 0x80000000 ∧
      (ExecFloat.Binary.infinity : Binary32).toNatBits = 0x7f800000 ∧
      (ExecFloat.Binary.infinity? : Option Binary32).map ExecFloat.Binary.toNatBits =
        some 0x7f800000 ∧
      (ExecFloat.Binary.maxFinite : Binary32).toNatBits = 0x7f7fffff ∧
      (ExecFloat.Binary.maxFinite (sign := true) : Binary32).toNatBits = 0xff7fffff := by
  decide +kernel

-- The constants of binary32, binary16, bfloat16, the OCP E4M3FN layout (no infinity, a NaN at the
-- top word), and a format whose fraction is wider than its bias, where epsilon is subnormal.
example :
    (ExecFloat.Binary.minNormal : Binary32).toNatBits = 0x00800000 ∧
      (ExecFloat.Binary.minSubnormal : Binary32).toNatBits = 1 ∧
      (ExecFloat.Binary.minSubnormal (sign := true) : Binary32).toNatBits = 0x80000001 ∧
      (ExecFloat.Binary.epsilon : Binary32).toNatBits = 0x34000000 ∧
      (ExecFloat.Binary.epsilon : Binary16).toNatBits = 0x1400 ∧
      (ExecFloat.Binary.maxFinite : Binary16).toNatBits = 0x7bff ∧
      (ExecFloat.Binary.epsilon : BFloat16).toNatBits = 0x3c00 ∧
      (ExecFloat.Binary.maxFinite : ExecFloat.Binary 4 3 (encoding := .finiteMaxNaN)).toNatBits =
        0x7e ∧
      (ExecFloat.Binary.epsilon : ExecFloat.Binary 2 3).toNatBits = 1 := by
  decide +kernel

-- `ulp` is the spacing of the binade: the gap above one is epsilon, zero and subnormals have the
-- least subnormal, the largest finite value its own binade's spacing, and the exceptional values
-- give infinity and NaN.
example :
    ExecFloat.Binary.ulp (1 : Binary32) = ExecFloat.Binary.epsilon ∧
      ExecFloat.Binary.ulp (-1 : Binary32) = ExecFloat.Binary.epsilon ∧
      ExecFloat.Binary.ulp (0 : Binary32) = ExecFloat.Binary.minSubnormal ∧
      ExecFloat.Binary.ulp (ExecFloat.Binary.minSubnormal : Binary32) =
        ExecFloat.Binary.minSubnormal ∧
      (ExecFloat.Binary.ulp (ExecFloat.Binary.maxFinite : Binary32)).toNatBits = 0x73800000 ∧
      (ExecFloat.Binary.ulp (3 : Binary32)).toNatBits = 0x34800000 ∧
      (ExecFloat.Binary.ulp
        (ExecFloat.Binary.maxFinite : ExecFloat.Binary 4 3 (encoding := .finiteMaxNaN))).toNatBits =
        0x60 ∧
      (ExecFloat.Binary.ulp (ExecFloat.Binary.infinity : Binary32)).toNatBits = 0x7f800000 ∧
      (ExecFloat.Binary.ulp (ExecFloat.Binary.canonicalNaN : Binary32)).isNaN = true := by
  decide +kernel

-- The native conversions accept every width. Binary64 and binary32 cross as their interchange
-- words, and other formats cast once, in the `mode` option where the destination is narrower.
example :
    (ExecFloat.Binary.ofFloat 0.1 : BFloat16).toNatBits = 0x3dcd ∧
      (ExecFloat.Binary.ofFloat 0.1 (mode := .down) : BFloat16).toNatBits = 0x3dcc ∧
      (ExecFloat.Binary.toFloat32 (0.1 : Binary64)).toBits = 0x3dcccccd ∧
      (ExecFloat.Binary.toFloat32 (0.1 : Binary64) (mode := .down)).toBits = 0x3dcccccc ∧
      (ExecFloat.Binary.ofFloat32 (Float32.ofBits 0x3dcccccd) : Binary16).toNatBits = 0x2e66 ∧
      (ExecFloat.Binary.toFloat (0.5 : Binary16)).toBits = 0x3fe0000000000000 ∧
      (ExecFloat.Binary.toFloat (0.1 : Binary32)).toBits = 0x3fb99999a0000000 := by
  decide +kernel

example (x : Float) : ExecFloat.Binary.toBits64 (ExecFloat.Binary.ofFloat x) = x.toBits :=
  ExecFloat.Binary.toBits64_ofFloat x

-- `bind` keeps every flag and the last ternary value.
example :
    let product :=
      (ExecFloat.Binary.div (1 : Binary32) 3 (status := true)).bind fun third =>
        ExecFloat.Binary.mul third 3 (status := true)
    product.value.toNatBits = 0x3f800000 ∧ product.status.inexact = true ∧
      product.ternary = .lt := by
  decide +kernel

example (x y : Binary32) :
    ((ExecFloat.Binary.add x y (status := true)).bind fun z =>
        ExecFloat.Binary.sqrt z (status := true)).value =
      ExecFloat.Binary.sqrt (ExecFloat.Binary.add x y) := by
  simp

-- The real-value adapters apply to the notation on standard and limb-stored formats.
example (a b : Binary32) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hab : (a * b).isFinite = true) :
    (a * b).toReal = Model.roundAt FloatFormat.binary32 (a.toReal * b.toReal) ∧
      |(a * b).toReal - a.toReal * b.toReal| ≤
        Model.epsilonAt FloatFormat.binary32 (a.toReal * b.toReal) :=
  ⟨ExecFloat.Binary.toReal_mul (by decide) ha hb hab,
    ExecFloat.Binary.abs_toReal_mul_sub_le (by decide) ha hb hab⟩

example (a b : Binary128) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hb0 : b.isZero = false) (hab : (a / b).isFinite = true) :
    |(a / b).toReal - a.toReal / b.toReal| ≤
      Model.epsilonAt FloatFormat.binary128 (a.toReal / b.toReal) :=
  ExecFloat.Binary.abs_toReal_div_sub_le (by decide) ha hb hb0 hab

example (a b : Binary256) (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hab : (a - b).isFinite = true) :
    (a - b).toReal = Model.roundAt (ExecFloat.Binary.descriptor 19 236) (a.toReal - b.toReal) :=
  ExecFloat.Binary.toReal_sub (by decide) ha hb hab

example (a : Binary64) (ha : a.isFinite = true) (hpos : a.signBit = false) :
    |a.sqrt.toReal - Real.sqrt a.toReal| ≤
      Model.epsilonAt FloatFormat.binary64 (Real.sqrt a.toReal) :=
  ExecFloat.Binary.abs_toReal_sqrt_sub_le (by decide) ha (.inr hpos)

example (a : Binary32) (ha : a.isFinite = true) : a.toReal? = some a.toReal :=
  ExecFloat.Binary.toReal?_eq_some_toReal ha

example : (ExecFloat.Binary.ofRat (3 / 8) : Binary16).toReal = 3 / 8 := by
  rw [ExecFloat.Binary.toReal_of_toRat?_eq_some (q := 3 / 8) (by decide +kernel)]
  norm_num

end FloatLibTests.Conformance.Formats.BinaryConveniences
