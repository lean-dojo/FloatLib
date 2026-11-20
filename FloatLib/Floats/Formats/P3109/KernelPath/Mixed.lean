/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Binary
public import FloatLib.Floats.Formats.P3109.KernelPath.Arithmetic
public import FloatLib.Tactic.KernelOptimize

/-!
# The kernel P3109 mixed arithmetic

P3109 Interim Report v4.1 (14 September 2026), §§4.8 to 4.10, an unapproved draft. Mixed
arithmetic reads each operand through its exact value, whatever its type, applies the operation
of the report with no intermediate rounding, and projects once into a P3109 format.

`ClosedSource` says that the exact value of every operand of a type is the closed value of a
class, a sign bit and a ratio of natural numbers that are computed from the operand. The values
of a P3109 format, of a binary interchange format and the rationals are such types. For
operands of any such types, alike or not:

* `mixedConvert_eq`, `mixedRecip_eq`: the conversion and the reciprocal of §§4.9.1 and 4.10.8;
* `mixedAdd_eq`, `mixedSubtract_eq`, `mixedMultiply_eq`, `mixedDivide_eq`: the operations of
  two operands of §§4.10.3 to 4.10.5;
* `mixedFMA_eq`, `mixedFAA_eq`: the fused operations of three operands of §§4.10.6 and 4.10.7.

Each stores the flat projection (`projectInto`) of the class, the sign and the ratio that the
kernel functions of `P3109.KernelPath.Core` give for the result, for every destination
descriptor, every rounding mode with every random word and every saturation mode. They are
kernel rules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109
open FloatLib.Floats.ExecFloat (ExactDecoder ExactMap)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

/-! ## Operands with a closed value on natural numbers -/

/--
A type of operands of mixed arithmetic whose exact value is the closed value of a class, a sign
bit and a ratio of natural numbers computed from the operand.
-/
class ClosedSource (Source : Type) (SourceExact : outParam Type)
    [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat] where
  /-- The class: zero for a finite value, one and two for the infinities, three for a NaN. -/
  cls : Source → Nat
  /-- The sign bit. -/
  sgn : Source → Nat
  /-- The numerator of the magnitude. -/
  num : Source → Nat
  /-- The denominator of the magnitude. -/
  den : Source → Nat
  /-- The value that mixed arithmetic reads is the closed value of the four numbers. -/
  decode_eq : ∀ value, Arithmetic.Mixed.decode value =
    closed (cls value) (sgn value) (num value) (den value)
  /-- The sign is a bit. -/
  sgn_le : ∀ value, sgn value ≤ 1
  /-- The denominator is not zero. -/
  den_ne : ∀ value, den value ≠ 0

/-- A value of a binary interchange format, through the fields of its encoding. -/
instance binarySource {fmt : FloatFormat} : ClosedSource (Model fmt) SignedRat where
  cls value := binaryClass fmt value.toNatBits
  sgn value := binarySign fmt value.toNatBits
  num value := binaryNumerator fmt value.toNatBits
  den _ := binaryDenominator fmt
  decode_eq := decode_closed
  sgn_le := binarySign_le
  den_ne _ := binaryDenominator_ne_zero fmt

/-- The value that mixed arithmetic reads from a P3109 value is its closed value. -/
theorem decode_p3109 {format : Format} (value : ExecFloat.P3109 format) :
    Arithmetic.Mixed.decode value = ExecFloat.P3109.toClosedRat value := by
  change Arithmetic.canonical
      ((ExecFloat.P3109.Conversion.decodeRat value).map (ExactMap.map (Target := Rat))) =
    Arithmetic.toRat (ExecFloat.P3109.decode value)
  unfold ExecFloat.P3109.Conversion.decodeRat
  cases ExecFloat.P3109.decode value <;> rfl

/-- A value of a P3109 format, through its code. -/
instance p3109Source {format : Format} : ClosedSource (ExecFloat.P3109 format) Rat where
  cls value := classOf format.bitWidth (sgOf format) (exOf format) value.toNatBits
  sgn value := signOf format.bitWidth (sgOf format) value.toNatBits
  num value := numeratorOf format.bitWidth format.precision (sgOf format) value.toNatBits
  den value := denominatorOf format.bitWidth format.precision (sgOf format) value.toNatBits
  decode_eq value := (decode_p3109 value).trans (toClosedRat_eq value)
  sgn_le _ := signOf_le _ _ _
  den_ne _ := denominatorOf_ne_zero _ _ _ _

/-- A rational, through its sign, the magnitude of its numerator and its denominator. -/
instance ratSource : ClosedSource Rat Rat where
  cls _ := 0
  sgn q := if q.num < 0 then 1 else 0
  num q := q.num.natAbs
  den q := q.den
  decode_eq q := by
    change NumericalValue.finite q = closed 0 (if q.num < 0 then 1 else 0) q.num.natAbs q.den
    unfold closed
    rw [ite_eq_left rfl]
    congr 1
    by_cases hneg : q.num < 0
    · have habs : (q.num.natAbs : Rat) = -(q.num : Rat) := by
        rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg.le, Int.cast_neg]
      rw [ite_eq_left hneg, ite_eq_right Nat.one_ne_zero, habs, neg_neg, Rat.num_div_den]
    · have habs : (q.num.natAbs : Rat) = (q.num : Rat) := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg (not_lt.mp hneg)]
      rw [ite_eq_right hneg, ite_eq_left rfl, habs, Rat.num_div_den]
  sgn_le q := by split <;> omega
  den_ne q := q.den_nz

/-! ## The projection of a closed value -/

/-- The flat projection of the closed value of a class, a sign and a ratio into `target`. -/
noncomputable abbrev projectInto (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) (cls s n d : Nat) : Nat :=
  Flat.project target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
    (modeWidth mode) (modeRandom mode) (satIndex saturation) cls s n d

/-- The stored projection of a closed value is `projectInto` of its four numbers. -/
theorem projectRat_closed (target : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (cls s n d : Nat) (hs : s ≤ 1) (hd : cls = 0 → n ≠ 0 → d ≠ 0) :
    ExecFloat.P3109.projectRat (format := target) (closed cls s n d) mode saturation =
      ExecFloat.P3109.ofNatBits (projectInto target mode saturation cls s n d) := by
  rw [projectRat_eq target mode saturation cls s n d hs hd, projectInto, Flat.project_eq]

/-! ## The operations -/

variable {Source SourceExact Left LeftExact Right RightExact Third ThirdExact : Type}
variable [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
variable [ExactDecoder Left LeftExact] [ExactMap LeftExact Rat]
variable [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
variable [ExactDecoder Third ThirdExact] [ExactMap ThirdExact Rat]
variable [ClosedSource Source SourceExact] [ClosedSource Left LeftExact]
variable [ClosedSource Right RightExact] [ClosedSource Third ThirdExact]

open ClosedSource

/-- P3109 interim report v4.1, §4.9.1: the conversion of an operand of any type with a closed
value on natural numbers is the flat projection of that value. -/
@[kernel_optimize (cost := 450)] theorem mixedConvert_eq (x : Source) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.Convert (Arithmetic.Destination.p3109 target) x mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectInto target mode saturation (cls x) (sgn x) (num x) (den x)) := by
  change ExecFloat.P3109.projectRat (Arithmetic.Mixed.decode x) mode saturation = _
  rw [decode_eq x, projectRat_closed _ _ _ _ _ _ _ (sgn_le x) (fun _ _ => den_ne x)]

/-- P3109 interim report v4.1, §4.10.3: the mixed sum of two operands is the flat projection
of the sum of their closed values, with no intermediate rounding. -/
@[kernel_optimize (cost := 900)] theorem mixedAdd_eq (x : Left) (y : Right) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.Add (Arithmetic.Destination.p3109 target) x y mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectInto target mode saturation (addClass (cls x) (cls y))
          (addSign (sgn x) (sgn y) (num x * den y) (num y * den x))
          (addMagnitude (sgn x) (sgn y) (num x * den y) (num y * den x)) (den x * den y)) := by
  change ExecFloat.P3109.projectRat
    (Arithmetic.Add (Arithmetic.Mixed.decode x) (Arithmetic.Mixed.decode y)) mode saturation = _
  rw [decode_eq x, decode_eq y,
    add_closed _ _ _ _ _ _ _ _ (sgn_le x) (sgn_le y) (den_ne x) (den_ne y),
    projectRat_closed _ _ _ _ _ _ _ (addSign_le _ _ _ _ (sgn_le x) (sgn_le y))
      (fun _ _ => Nat.mul_ne_zero (den_ne x) (den_ne y))]

/-- P3109 interim report v4.1, §4.10.3: the mixed difference of two operands is the flat
projection of the difference of their closed values. -/
@[kernel_optimize (cost := 950)] theorem mixedSubtract_eq (x : Left) (y : Right)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.Subtract (Arithmetic.Destination.p3109 target) x y mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectInto target mode saturation (addClass (cls x) (negClass (cls y)))
          (addSign (sgn x) (1 - sgn y) (num x * den y) (num y * den x))
          (addMagnitude (sgn x) (1 - sgn y) (num x * den y) (num y * den x))
          (den x * den y)) := by
  change ExecFloat.P3109.projectRat
    (Arithmetic.Subtract (Arithmetic.Mixed.decode x) (Arithmetic.Mixed.decode y)) mode
      saturation = _
  unfold Arithmetic.Subtract
  rw [decode_eq x, decode_eq y, negate_closed _ _ _ _ (sgn_le y),
    add_closed _ _ _ _ _ _ _ _ (sgn_le x) (Nat.sub_le _ _) (den_ne x) (den_ne y),
    projectRat_closed _ _ _ _ _ _ _ (addSign_le _ _ _ _ (sgn_le x) (Nat.sub_le _ _))
      (fun _ _ => Nat.mul_ne_zero (den_ne x) (den_ne y))]

/-- P3109 interim report v4.1, §4.10.4: the mixed product of two operands is the flat
projection of the product of their closed values. -/
@[kernel_optimize (cost := 900)] theorem mixedMultiply_eq (x : Left) (y : Right)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.Multiply (Arithmetic.Destination.p3109 target) x y mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectInto target mode saturation
          (mulClass (cls x) (cls y) (sgn x) (sgn y) (num x) (num y))
          (Nat.xor (sgn x) (sgn y)) (num x * num y) (den x * den y)) := by
  change ExecFloat.P3109.projectRat
    (Arithmetic.Multiply (Arithmetic.Mixed.decode x) (Arithmetic.Mixed.decode y)) mode
      saturation = _
  rw [decode_eq x, decode_eq y,
    multiply_closed _ _ _ _ _ _ _ _ (sgn_le x) (sgn_le y) (den_ne x) (den_ne y),
    projectRat_closed _ _ _ _ _ _ _ (xor_le_one (sgn_le x) (sgn_le y))
      (fun _ _ => Nat.mul_ne_zero (den_ne x) (den_ne y))]

/-- The ratio of a quotient of class zero has a denominator other than zero. -/
theorem quotient_den_ne {ca cb sb nb da : Nat} (hda : da ≠ 0)
    (hcls : divClass ca cb sb nb = 0) : (if cb = 0 then da * nb else 1) ≠ 0 := by
  by_cases hcb : cb = 0
  · subst hcb
    rw [ite_eq_left rfl]
    exact Nat.mul_ne_zero hda (divClass_eq_zero hcls)
  · rw [ite_eq_right hcb]
    exact Nat.one_ne_zero

/-- P3109 interim report v4.1, §4.10.5: the mixed quotient of two operands is the flat
projection of the quotient of their closed values, NaN for every zero divisor. -/
@[kernel_optimize (cost := 900)] theorem mixedDivide_eq (x : Left) (y : Right)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.Divide (Arithmetic.Destination.p3109 target) x y mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectInto target mode saturation (divClass (cls x) (cls y) (sgn y) (num y))
          (Nat.xor (sgn x) (sgn y)) (if cls y = 0 then num x * den y else 0)
          (if cls y = 0 then den x * num y else 1)) := by
  change ExecFloat.P3109.projectRat
    (Arithmetic.Divide (Arithmetic.Mixed.decode x) (Arithmetic.Mixed.decode y)) mode
      saturation = _
  rw [decode_eq x, decode_eq y,
    divide_closed _ _ _ _ _ _ _ _ (sgn_le x) (sgn_le y) (den_ne y),
    projectRat_closed _ _ _ _ _ _ _ (xor_le_one (sgn_le x) (sgn_le y))
      (fun hcls _ => quotient_den_ne (den_ne x) hcls)]

/-- P3109 interim report v4.1, §4.10.8: the mixed reciprocal of an operand is the flat
projection of the quotient of one by its closed value, NaN for zero. -/
@[kernel_optimize (cost := 700)] theorem mixedRecip_eq (x : Source) (target : Format)
    (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.Recip (Arithmetic.Destination.p3109 target) x mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectInto target mode saturation (divClass 0 (cls x) (sgn x) (num x)) (sgn x)
          (if cls x = 0 then 1 * den x else 0) (if cls x = 0 then 1 * num x else 1)) := by
  change ExecFloat.P3109.projectRat (Arithmetic.Recip (Arithmetic.Mixed.decode x)) mode
    saturation = _
  unfold Arithmetic.Recip
  rw [decode_eq x, one_closed,
    divide_closed _ _ _ _ _ _ _ _ (Nat.zero_le 1) (sgn_le x) (den_ne x), zero_xor,
    projectRat_closed _ _ _ _ _ _ _ (sgn_le x)
      (fun hcls _ => quotient_den_ne Nat.one_ne_zero hcls)]

/-- P3109 interim report v4.1, §4.10.6: the mixed fused multiply-add of three operands is the
flat projection of the sum of the exact product of two closed values and a third. -/
@[kernel_optimize (cost := 1400)] theorem mixedFMA_eq (x : Left) (y : Right) (z : Third)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.FMA (Arithmetic.Destination.p3109 target) x y z mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectInto target mode saturation
          (addClass (mulClass (cls x) (cls y) (sgn x) (sgn y) (num x) (num y)) (cls z))
          (addSign (Nat.xor (sgn x) (sgn y)) (sgn z) (num x * num y * den z)
            (num z * (den x * den y)))
          (addMagnitude (Nat.xor (sgn x) (sgn y)) (sgn z) (num x * num y * den z)
            (num z * (den x * den y)))
          (den x * den y * den z)) := by
  change ExecFloat.P3109.projectRat
    (Arithmetic.FMA (Arithmetic.Mixed.decode x) (Arithmetic.Mixed.decode y)
      (Arithmetic.Mixed.decode z)) mode saturation = _
  unfold Arithmetic.FMA
  rw [decode_eq x, decode_eq y, decode_eq z,
    multiply_closed _ _ _ _ _ _ _ _ (sgn_le x) (sgn_le y) (den_ne x) (den_ne y),
    add_closed _ _ _ _ _ _ _ _ (xor_le_one (sgn_le x) (sgn_le y)) (sgn_le z)
      (Nat.mul_ne_zero (den_ne x) (den_ne y)) (den_ne z),
    projectRat_closed _ _ _ _ _ _ _
      (addSign_le _ _ _ _ (xor_le_one (sgn_le x) (sgn_le y)) (sgn_le z))
      (fun _ _ => Nat.mul_ne_zero (Nat.mul_ne_zero (den_ne x) (den_ne y)) (den_ne z))]

/-- P3109 interim report v4.1, §4.10.7: the mixed fused add-add of three operands is the flat
projection of the sum of their three closed values, with no intermediate rounding. -/
@[kernel_optimize (cost := 1400)] theorem mixedFAA_eq (x : Left) (y : Right) (z : Third)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Arithmetic.Mixed.FAA (Arithmetic.Destination.p3109 target) x y z mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectInto target mode saturation (addClass (addClass (cls x) (cls y)) (cls z))
          (addSign (addSign (sgn x) (sgn y) (num x * den y) (num y * den x)) (sgn z)
            (addMagnitude (sgn x) (sgn y) (num x * den y) (num y * den x) * den z)
            (num z * (den x * den y)))
          (addMagnitude (addSign (sgn x) (sgn y) (num x * den y) (num y * den x)) (sgn z)
            (addMagnitude (sgn x) (sgn y) (num x * den y) (num y * den x) * den z)
            (num z * (den x * den y)))
          (den x * den y * den z)) := by
  change ExecFloat.P3109.projectRat
    (Arithmetic.FAA (Arithmetic.Mixed.decode x) (Arithmetic.Mixed.decode y)
      (Arithmetic.Mixed.decode z)) mode saturation = _
  unfold Arithmetic.FAA
  rw [decode_eq x, decode_eq y, decode_eq z,
    add_closed _ _ _ _ _ _ _ _ (sgn_le x) (sgn_le y) (den_ne x) (den_ne y),
    add_closed _ _ _ _ _ _ _ _ (addSign_le _ _ _ _ (sgn_le x) (sgn_le y)) (sgn_le z)
      (Nat.mul_ne_zero (den_ne x) (den_ne y)) (den_ne z),
    projectRat_closed _ _ _ _ _ _ _
      (addSign_le _ _ _ _ (addSign_le _ _ _ _ (sgn_le x) (sgn_le y)) (sgn_le z))
      (fun _ _ => Nat.mul_ne_zero (Nat.mul_ne_zero (den_ne x) (den_ne y)) (den_ne z))]

end FloatLib.Floats.Formats.P3109.KernelPath
