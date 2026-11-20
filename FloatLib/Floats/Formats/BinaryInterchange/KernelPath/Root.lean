/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Compiled.Word.ModelSqrt.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.HypotProof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Literal
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Power
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value
public import FloatLib.Kernels.IntegerRoot.Proof
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Proof
public import FloatLib.Numerics.Kernel.RootProof
public import FloatLib.Numerics.Kernel.ZProof
public meta import FloatLib.Tactic.IeeeExtrema

/-!
# `rootn`, `rSqrt` and `hypot` on encodings

IEEE 754-2019 §9.2 `rootn` takes the root of integer degree of a value and `rSqrt` the reciprocal
of its square root, each with one rounding to nearest even. The references `Model.rootn` and
`Model.rSqrt` form the exact rational radicand and round its root with
`AlgebraicRounding.rootRat`: the binade of the root from the binary logarithm of the radicand,
the integer root of the radicand scaled to two bits below the rounding position, the place of
the root between that integer and the next, and one rounding of this certificate.

`rootRatio fmt sign num den degree reference` computes the encoding of that rounding from the
reduced fraction `num / den` with natural-number operations that Lean's kernel accelerates. The
binary logarithm is `ratioLog2`, the integer root is a Newton iteration whose result is checked
(`floorRoot`), the place of the root
is two more bits below the integer (`rootQuarter`), and `KernelPath.roundDyadic` rounds the
dyadic with those two bits once. `roundCertificate_eq_roundDyadic` proves this rounding equal
to the rounding of the certificate whenever the integer has the bits of a significand, for every
format descriptor. A root at the ends of the exponent range and a root with a shorter integer
part are `reference`, which the caller sets to the encoding of the reference result, so
`rootRatio_eq` holds for every positive rational and every nonzero degree.

`rootn fmt degree a` and `rSqrt fmt a` decode a finite nonzero word with `KernelPath.decode`,
reduce the fraction of its magnitude or of the reciprocal by one greatest common divisor
(`rootOf`), and call `rootRatio`. A zero, an infinity, a NaN, the degree zero and a root that
does not exist go to the reference. `rootn_eq_spec` and `rSqrt_eq_spec` prove them equal to
the encodings of `Model.rootn` and `Model.rSqrt`, for every format descriptor, every value and
every integer degree.

`hypot` of §9.2 is the square root of the exact sum of two squares, rounded once. The reference
`Model.hypot` forms the sum as a dyadic and takes its square root with
`FiniteSqrt.sqrtPositiveDyadic`, which in an IEEE layout is the square root of Lean's model of
IEEE arithmetic: the integer square root of the significand shifted to a target exponent, with
its remainder as the accuracy. `sqrtDyadic` computes that on natural numbers (`sqrtTarget`,
the checked root `Kernel.isqrt`, `sqrtQuarter`) and rounds once with `KernelPath.roundDyadic`,
and `hypot fmt a b` applies it to the exact sum of the squares of two decoded finite words
(`KernelPath.mulExact`, `KernelPath.addExact`). A NaN, an infinity, two zeros, a root with
fewer bits than a significand and a format that is not an IEEE layout go to the reference, and
`hypot_eq_spec` proves `hypot` equal to the encoding of `Model.hypot`, for every format
descriptor and every pair of values.

`Value.rootn`, `Value.rSqrt` and `Value.hypot` are the operations on stored values, with
`Value.rootn_eq_lift`, `Value.rSqrt_eq_lift`, `Value.hypot_eq_lift` and the rules
`Value.toNat_rootn`, `Value.toNat_rSqrt` and `Value.toNat_hypot`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open Float.Model Float.Model.UnpackedFloat
open FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

/-! ## The rounding of a certificate as the rounding of a dyadic -/

/-- A repeated map commutes with one more application of it. -/
private theorem repeat_apply {α : Type} (f : α → α) (n : Nat) (a : α) :
    Nat.repeat f n (f a) = f (Nat.repeat f n a) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f ih

/-- The accuracy of a certificate as two bits below its mantissa is at most three. -/
private theorem accuracyQuarter_lt (accuracy : Accuracy) : accuracyQuarter accuracy < 4 := by
  rcases accuracy with _ | (_ | _ | _) <;> decide

/--
Two more right shifts of a mantissa that carries its accuracy as two bits give the extended
mantissa of that accuracy.
-/
theorem shiftRight_quarter (m : Nat) (accuracy : Accuracy) (k : Nat) :
    (ExtendedMantissa.ofMantissaAndAccuracy (4 * m + accuracyQuarter accuracy) .exact) >>> (k + 2) =
      (ExtendedMantissa.ofMantissaAndAccuracy m accuracy) >>> k := by
  change Nat.repeat ExtendedMantissa.shiftRightOne (k + 2) _ =
    Nat.repeat ExtendedMantissa.shiftRightOne k _
  have hstep : ∀ a : ExtendedMantissa, Nat.repeat ExtendedMantissa.shiftRightOne (k + 2) a =
      Nat.repeat ExtendedMantissa.shiftRightOne k
        (ExtendedMantissa.shiftRightOne (ExtendedMantissa.shiftRightOne a)) := by
    intro a
    rw [repeat_apply, repeat_apply]
    rfl
  rw [hstep]
  congr 1
  rcases accuracy with _ | (_ | _ | _) <;>
    simp [ExtendedMantissa.ofMantissaAndAccuracy, ExtendedMantissa.shiftRightOne,
      accuracyQuarter] <;>
    omega

/-- Two more bits below a nonzero mantissa move its leading bit by two. -/
theorem log2_quarter (m q : Nat) (hm : m ≠ 0) (hq : q < 4) : (4 * m + q).log2 = m.log2 + 2 := by
  have hbounds := (Nat.log2_eq_iff hm).1 rfl
  rw [Nat.log2_eq_iff (by omega)]
  have : 2 ^ (m.log2 + 2) = 4 * 2 ^ m.log2 := by ring
  have : 2 ^ (m.log2 + 2 + 1) = 4 * 2 ^ (m.log2 + 1) := by ring
  constructor <;> omega

/--
A rounding with an accuracy is the rounding of the mantissa with the accuracy as two more bits,
when the mantissa is nonzero and its exponent is at most the exponent the format asks for.
-/
theorem roundWithAccuracy_eq_round (spec : Float.Model.Format) (sign : Sign) (m : Nat) (e : Int)
    (accuracy : Accuracy) (hm : m ≠ 0)
    (hguard : e ≤ spec.targetExponent (totalExponent m e)) :
    roundWithAccuracy spec sign m e accuracy =
      UnpackedFloat.round spec sign (4 * m + accuracyQuarter accuracy) (e - 2) := by
  have hq := accuracyQuarter_lt accuracy
  have htotal : totalExponent (4 * m + accuracyQuarter accuracy) (e - 2) = totalExponent m e := by
    unfold totalExponent
    rw [log2_quarter m _ hm hq]
    push_cast
    omega
  have hdecrease : decreaseExponent (4 * m + accuracyQuarter accuracy) (e - 2)
      (spec.targetExponent (totalExponent m e)) = (4 * m + accuracyQuarter accuracy, e - 2) := by
    unfold decreaseExponent
    have hzero : (e - 2 - spec.targetExponent (totalExponent m e)).toNat = 0 := by omega
    simp [hzero]
  have hshift : shiftToTargetExponent spec (4 * m + accuracyQuarter accuracy) (e - 2) .exact =
      shiftToTargetExponent spec m e accuracy := by
    unfold shiftToTargetExponent shiftToExponent
    rw [htotal]
    dsimp only
    have hk : (spec.targetExponent (totalExponent m e) - (e - 2)).toNat =
        (spec.targetExponent (totalExponent m e) - e).toNat + 2 := by omega
    rw [hk, shiftRight_quarter]
    congr 1
    push_cast
    omega
  unfold UnpackedFloat.round
  rw [htotal]
  simp only [hdecrease]
  unfold roundWithAccuracy
  rw [hshift]

/--
The rounding of a certificate is the reference rounding of the dyadic that carries the accuracy
as two more bits, when the mantissa of the certificate has the bits of a normal significand.
-/
theorem roundCertificate_eq_roundDyadic (fmt : FloatFormat) (sign : Bool) (c : Certificate)
    (hbits : 2 ^ fmt.fracWidth ≤ c.mantissa) :
    roundCertificate fmt sign c =
      Model.roundDyadic fmt
        ⟨sign, 4 * c.mantissa + accuracyQuarter c.accuracy, c.exponent - 2⟩ := by
  unfold roundCertificate
  by_cases hfmt : fmt.isIEEE = true
  · have hm : c.mantissa ≠ 0 := by
      have := Nat.two_pow_pos fmt.fracWidth
      omega
    have hlog : fmt.fracWidth ≤ c.mantissa.log2 := by
      rw [Nat.le_log2 hm]
      exact hbits
    have hguard : c.exponent ≤
        (FloatFormat.toModel fmt).targetExponent (totalExponent c.mantissa c.exponent) := by
      unfold Float.Model.Format.targetExponent totalExponent
      simp only [FloatFormat.toModel, Float.Model.Format.mantissaBits]
      omega
    rw [ite_eq_left hfmt, roundWithAccuracy_eq_round _ _ _ _ _ hm hguard]
    unfold Model.roundDyadic Model.ieeeRoundDyadic
    rw [ite_eq_left hfmt]
  · rw [ite_eq_right hfmt]


/-! ## The root of a reduced fraction -/

/--
The floor of the `k`-th root of `n` (`floorRoot_eq`): the Newton result when it passes the
check `r ^ k ≤ n < (r + 1) ^ k`, and the reference root otherwise.
-/
def floorRoot (k n : Nat) : Nat :=
  (fun r =>
    Bool.casesOn (motive := fun _ => Nat) (Kernel.isRoot k r n) (IntegerRoot.root k n) r)
    (Kernel.rootGuess k n)

/-- `floorRoot` is the reference integer root, for every degree and radicand. -/
theorem floorRoot_eq (k n : Nat) : floorRoot k n = IntegerRoot.root k n := by
  change Bool.casesOn (motive := fun _ => Nat) (Kernel.isRoot k (Kernel.rootGuess k n) n)
    (IntegerRoot.root k n) (Kernel.rootGuess k n) = _
  cases h : Kernel.isRoot k (Kernel.rootGuess k n) n
  · rfl
  · have hk : k ≠ 0 := by
      rintro rfl
      rw [Kernel.isRoot_zero] at h
      exact absurd h (by decide)
    rw [IntegerRoot.root_eq_nthRoot]
    exact (Kernel.isRoot_iff hk _ n).1 h

/--
The place of the `degree`-th root of `numerator / denominator` after its integer part
`mantissa`, as two bits (`rootQuarter_eq`): zero for an exact root, and one, two or three for a
root below, at or above `mantissa + 1/2`.
-/
def rootQuarter (numerator denominator degree mantissa : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Nat.beq numerator (Nat.mul (Nat.pow mantissa degree) denominator))
    ((fun left right =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.ble right left) 1
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq left right) 3 2))
      (Nat.shiftLeft numerator degree)
      (Nat.mul (Nat.pow (Nat.succ (Nat.mul 2 mantissa)) degree) denominator))
    0

/-- `rootQuarter` is the accuracy of the reference certificate as two bits. -/
theorem rootQuarter_eq (numerator denominator degree mantissa : Nat) :
    rootQuarter numerator denominator degree mantissa =
      accuracyQuarter (scaledRootAccuracy numerator denominator degree mantissa) := by
  unfold rootQuarter scaledRootAccuracy
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.shiftLeft_eq', Nat.succ_eq_add_one]
  generalize numerator <<< degree = left
  generalize (2 * mantissa + 1) ^ degree * denominator = right
  by_cases hexact : numerator = mantissa ^ degree * denominator
  · have hbeq : Nat.beq numerator (mantissa ^ degree * denominator) = true := by
      rw [Nat.beq_eq]
      exact hexact
    rw [ite_eq_left hexact, hbeq]
    rfl
  · have hbeq : Nat.beq numerator (mantissa ^ degree * denominator) = false := by
      cases h : Nat.beq numerator (mantissa ^ degree * denominator)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hexact
    rw [ite_eq_right hexact, hbeq]
    rcases Nat.lt_trichotomy left right with hlt | heq | hgt
    · have hble : Nat.ble right left = false := by
        cases h : Nat.ble right left
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true h) (by omega)
      rw [(cmp_eq_lt_iff _ _).2 hlt, hble]
      rfl
    · have hble : Nat.ble right left = true := Nat.ble_eq_true_of_le (by omega)
      have hbeq' : Nat.beq left right = true := by
        rw [Nat.beq_eq]
        exact heq
      rw [(cmp_eq_eq_iff _ _).2 heq, hble, hbeq']
      rfl
    · have hble : Nat.ble right left = true := Nat.ble_eq_true_of_le (by omega)
      have hbeq' : Nat.beq left right = false := by
        cases h : Nat.beq left right
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
      rw [(cmp_eq_gt_iff _ _).2 hgt, hble, hbeq']
      rfl

/-- A selection by `Bool.casesOn` whose two branches are the same value is that value. -/
private theorem casesOn_eq_of {α : Type} (c : Bool) (a b x : α) (hfalse : c = false → a = x)
    (htrue : c = true → b = x) : Bool.casesOn (motive := fun _ => α) c a b = x := by
  cases c
  · exact hfalse rfl
  · exact htrue rfl

/--
The binary logarithm of the quotient `num / den`, rounded down (`ratioLog2_eq`): the reference
`RationalBinary.floorLog2` in the integer arithmetic that the kernel evaluates directly.
-/
def ratioLog2 (num den : Nat) : Int :=
  (fun initial =>
    (fun lower =>
      (fun upper =>
        Bool.casesOn (motive := fun _ => Int)
          (RationalBinary.atLeastPowerOfTwo num den upper) lower upper)
        (Kernel.Z.add lower (Int.ofNat 1)))
      (Bool.casesOn (motive := fun _ => Int)
        (RationalBinary.lessThanPowerOfTwo num den initial)
        initial (Kernel.Z.sub initial (Int.ofNat 1))))
    (Kernel.Z.subNat (Kernel.log2 num) (Kernel.log2 den))

/-- A selection by the recursor of `Bool` is the `if` on its test. -/
private theorem rec_eq_ite {α : Type} (c : Bool) (e t : α) :
    Bool.rec (motive := fun _ => α) e t c = if c = true then t else e := by
  cases c <;> rfl

/-- `ratioLog2` is the reference logarithm of a quotient. -/
theorem ratioLog2_eq (num den : Nat) : ratioLog2 num den = RationalBinary.floorLog2 num den := by
  rw [RationalBinary.floorLog2_eq_log2]
  unfold ratioLog2
  simp only [Kernel.Z.add_eq, Kernel.Z.sub_eq, Kernel.Z.subNat_eq, Kernel.log2_eq,
    Int.ofNat_eq_natCast, Nat.cast_one, rec_eq_ite]

/--
Encoding of the `degree`-th root of the reduced fraction `num / den`, rounded to nearest even
with the sign `sign` (`rootRatio_eq`). The binade of the root is the quotient of the binary
logarithm of the fraction by the degree, the integer root of the fraction scaled to two bits
below the rounding position is checked, its place between two integers is two more bits, and
`roundDyadic` rounds once. A root whose binade is not strictly inside the exponent range of the
format, or whose integer part has fewer bits than a significand, is `reference`.
-/
def rootRatio (fmt : FloatFormat) (sign : Bool) (num den degree reference : Nat) : Nat :=
  (fun binade =>
    (fun exponent =>
      (fun scaled =>
        (fun mantissa =>
          Bool.casesOn (motive := fun _ => Nat)
            (Bool.and
              (Bool.and
                (Int.blt' (Kernel.Z.negOfNat (Nat.add fmt.exponentBias fmt.fracWidth)) binade)
                (Int.blt' binade
                  (Kernel.Z.subNat (Nat.succ fmt.maxFiniteExpField) fmt.exponentBias)))
              (Nat.ble (Nat.shiftLeft 1 fmt.fracWidth) mantissa))
            reference
            (roundDyadic fmt .nearest
              { negative := sign
                significand :=
                  Nat.add (Nat.mul 4 mantissa) (rootQuarter scaled.1 scaled.2 degree mantissa)
                exponent := Kernel.Z.sub exponent (Int.ofNat 2) }))
          (floorRoot degree (Nat.div scaled.1 scaled.2)))
        (RationalBinary.scaleByPowerOfTwo num den
          (Kernel.Z.neg (Kernel.Z.mul exponent (Int.ofNat degree)))))
      (Kernel.Z.max
        (Kernel.Z.negOfNat (Nat.succ (Nat.add fmt.exponentBias fmt.fracWidth)))
        (Kernel.Z.sub binade (Int.ofNat (Nat.add fmt.fracWidth 2)))))
    (Kernel.Z.floorDiv (ratioLog2 num den) degree)

/--
`rootRatio` computes the encoding of the reference root of a positive rational, for every
format descriptor and nonzero degree, when `reference` is that encoding.
-/
theorem rootRatio_eq (fmt : FloatFormat) (sign : Bool) (r : ℚ) (degree : Nat)
    (hdegree : degree ≠ 0) (hr : 0 < r) (reference : Nat)
    (href : reference = (rootRat fmt sign r degree).toNatBits) :
    rootRatio fmt sign r.num.natAbs r.den degree reference =
      (rootRat fmt sign r degree).toNatBits := by
  have hlower : (Kernel.Z.negOfNat (Nat.add fmt.exponentBias fmt.fracWidth)) =
      lowerExponent fmt := by
    rw [Kernel.Z.negOfNat_eq]
    simp only [lowerExponent, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Nat.add_eq, Int.ofNat_eq_natCast]
    push_cast
    omega
  have hupper : Kernel.Z.subNat (Nat.succ fmt.maxFiniteExpField) fmt.exponentBias =
      upperExponent fmt := by
    rw [Kernel.Z.subNat_eq]
    simp only [upperExponent, FloatFormat.maxNormalExponent, Nat.succ_eq_add_one,
      Int.ofNat_eq_natCast]
    push_cast
    omega
  have hexponent : ∀ binade : Int,
      Kernel.Z.max (Kernel.Z.negOfNat (Nat.succ (Nat.add fmt.exponentBias fmt.fracWidth)))
        (Kernel.Z.sub binade (Int.ofNat (Nat.add fmt.fracWidth 2))) =
      certificateExponent fmt binade := by
    intro binade
    rw [Kernel.Z.max_eq, Kernel.Z.negOfNat_eq, Kernel.Z.sub_eq]
    simp only [certificateExponent, FloatFormat.minSubnormalExponent,
      FloatFormat.minNormalExponent, Nat.add_eq, Nat.succ_eq_add_one, Int.ofNat_eq_natCast]
    push_cast
    congr 1 <;> omega
  have hdiv : ∀ a b : Nat, Nat.div a b = a / b := fun _ _ => rfl
  have hnot : ¬(degree = 0 ∨ r ≤ 0) := by
    rintro (h | h)
    · exact hdegree h
    · exact absurd hr (not_lt.mpr h)
  unfold rootRatio
  simp only [hlower, hupper, hexponent]
  simp only [ratioLog2_eq, Kernel.Z.floorDiv_eq, Kernel.Z.neg_eq, Kernel.Z.mul_eq,
    Kernel.Z.sub_eq, floorRoot_eq, rootQuarter_eq, hdiv, Nat.add_eq, Nat.mul_eq,
    Nat.shiftLeft_eq', Int.ofNat_eq_natCast]
  refine casesOn_eq_of _ _ _ _ (fun _ => href) (fun hguard => ?_)
  simp only [Bool.and_eq_true, Kernel.Z.blt'_iff, Nat.ble_eq] at hguard
  obtain ⟨⟨hlow, hup⟩, hbits⟩ := hguard
  rw [Nat.shiftLeft_eq, Nat.one_mul] at hbits
  have hlow' : lowerExponent fmt < rootBinade r degree := hlow
  have hup' : rootBinade r degree < upperExponent fmt := hup
  have hroot : rootRat fmt sign r degree =
      roundCertificate fmt sign
        (rootCertificateAt fmt r degree (certificateExponent fmt (rootBinade r degree))) := by
    unfold rootRat
    rw [ite_eq_right hnot]
    dsimp only
    rw [ite_eq_right (not_lt.mpr hlow'.le), ite_eq_right (not_le.mpr hup'),
      ite_eq_right (fun h => absurd h.1 (ne_of_gt hlow'))]
  rw [hroot, roundCertificate_eq_roundDyadic fmt sign _ (by
    simpa only [rootCertificateAt, rootScale, rootBinade, hdegree, ↓reduceIte] using hbits),
    roundDyadic_nearest_eq]
  simp only [rootCertificateAt, rootScale, rootBinade, hdegree, ↓reduceIte, Nat.cast_ofNat]


/-! ## The root of a dyadic and of its reciprocal -/

/-- The reduced fraction of a quotient of natural numbers, by their greatest common divisor. -/
theorem reduced_of_ratio (q : ℚ) (N D : Nat) (hD : D ≠ 0) (hq : q = (N : ℚ) / (D : ℚ)) :
    N / Nat.gcd N D = q.num.natAbs ∧ D / Nat.gcd N D = q.den := by
  obtain ⟨g, hg, hN, hDg, -⟩ := exists_common_factor q N D hD hq
  have hgcd : Nat.gcd N D = g := by
    rw [hN, hDg, Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one q.reduced, Nat.one_mul]
  rw [hgcd]
  constructor
  · rw [hN]
    exact Nat.mul_div_cancel _ hg
  · rw [hDg]
    exact Nat.mul_div_cancel _ hg

/-- The magnitude of a dyadic as a quotient of two natural numbers. -/
theorem abs_toRat_eq_div (d : Numerics.Dyadic) :
    |d.toRat| = ((d.significand <<< d.exponent.toNat : Nat) : ℚ) /
      ((1 <<< (-d.exponent).toNat : Nat) : ℚ) := by
  rw [abs_toRat]
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  push_cast
  rw [mul_div_assoc]
  congr 1
  rw [← zpow_natCast (2 : ℚ) d.exponent.toNat, ← zpow_natCast (2 : ℚ) (-d.exponent).toNat,
    ← zpow_sub₀ (by norm_num)]
  congr 1
  omega

/--
Encoding of the `degree`-th root of the magnitude of the dyadic `d`, or of the reciprocal of
that magnitude, rounded to nearest even with the sign `sign` (`rootOf_eq`): `rootRatio` on the
reduced fraction of the magnitude, whose two terms are divided by their greatest common divisor.
-/
def rootOf (fmt : FloatFormat) (sign : Bool) (d : Numerics.Dyadic) (reciprocal : Bool)
    (degree reference : Nat) : Nat :=
  (fun N D =>
    (fun g =>
      Bool.casesOn (motive := fun _ => Nat) reciprocal
        (rootRatio fmt sign (Nat.div N g) (Nat.div D g) degree reference)
        (rootRatio fmt sign (Nat.div D g) (Nat.div N g) degree reference))
      (Nat.gcd N D))
    (Nat.shiftLeft d.significand (Kernel.Z.toNat d.exponent))
    (Nat.shiftLeft 1 (Kernel.Z.toNat (Kernel.Z.neg d.exponent)))

/--
`rootOf` computes the encoding of the reference root of the magnitude of a nonzero dyadic, or
of its reciprocal, for every format descriptor and nonzero degree, when `reference` is that
encoding.
-/
theorem rootOf_eq (fmt : FloatFormat) (sign : Bool) (d : Numerics.Dyadic)
    (hd : d.significand ≠ 0) (reciprocal : Bool) (degree : Nat) (hdegree : degree ≠ 0)
    (reference : Nat)
    (href : reference =
      (rootRat fmt sign (if reciprocal = true then |d.toRat|⁻¹ else |d.toRat|) degree).toNatBits) :
    rootOf fmt sign d reciprocal degree reference =
      (rootRat fmt sign (if reciprocal = true then |d.toRat|⁻¹ else |d.toRat|)
        degree).toNatBits := by
  have hdiv : ∀ a b : Nat, Nat.div a b = a / b := fun _ _ => rfl
  have hratio := abs_toRat_eq_div d
  have hN : d.significand <<< d.exponent.toNat ≠ 0 := by
    simp [Nat.shiftLeft_eq, hd]
  have hD : 1 <<< (-d.exponent).toNat ≠ 0 := by
    simp [Nat.shiftLeft_eq]
  have hpos : 0 < |d.toRat| := by
    rw [hratio]
    have h1 : (0 : ℚ) < ((d.significand <<< d.exponent.toNat : Nat) : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    have h2 : (0 : ℚ) < ((1 <<< (-d.exponent).toNat : Nat) : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hD
    exact div_pos h1 h2
  unfold rootOf
  simp only [Kernel.Z.toNat_eq, Kernel.Z.neg_eq, hdiv, Nat.shiftLeft_eq']
  cases reciprocal
  · obtain ⟨hnum, hden⟩ := reduced_of_ratio _ _ _ hD hratio
    rw [hnum, hden]
    exact rootRatio_eq fmt sign _ degree hdegree hpos reference href
  · have hinv : |d.toRat|⁻¹ = ((1 <<< (-d.exponent).toNat : Nat) : ℚ) /
        ((d.significand <<< d.exponent.toNat : Nat) : ℚ) := by
      rw [hratio, inv_div]
    obtain ⟨hnum, hden⟩ := reduced_of_ratio _ _ _ hN hinv
    rw [Nat.gcd_comm, hnum, hden]
    exact rootRatio_eq fmt sign _ degree hdegree (inv_pos.mpr hpos) reference href

/-- The parity of an integer is the parity of its magnitude. -/
private theorem emod_two_ne_zero (n : Int) : (n % 2 != 0) = Nat.beq (n.natAbs % 2) 1 := by
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · have hnat : n.natAbs % 2 = 0 := by omega
    rw [h, hnat]
    rfl
  · have hnat : n.natAbs % 2 = 1 := by omega
    rw [h, hnat]
    rfl

/-- An integer is even exactly when its magnitude is. -/
private theorem emod_two_eq_zero (n : Int) : (n % 2 == 0) = Nat.beq (n.natAbs % 2) 0 := by
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · have hnat : n.natAbs % 2 = 0 := by omega
    rw [h, hnat]
    rfl
  · have hnat : n.natAbs % 2 = 1 := by omega
    rw [h, hnat]
    rfl

/-! ## `rootn` and `rSqrt` -/

/--
Encoding of the root of integer degree `degree` of the value that `a` encodes, rounded to
nearest even (`rootn_eq_spec`). A finite nonzero word whose root exists is decoded and `rootOf`
rounds the root of its magnitude, or of the reciprocal of its magnitude for a negative degree,
with the sign of an odd root of a negative value. A zero, an infinity, a NaN, the degree zero
and an even root of a negative value go to the reference.
-/
def rootn (fmt : FloatFormat) (degree : Int) (a : Nat) : Nat :=
  (fun reference =>
    (fun k negative =>
      Bool.casesOn (motive := fun _ => Nat)
        (Bool.and
          (Bool.and (Nat.beq (finiteCode fmt a) 1) (Bool.not (Nat.beq (zeroCode fmt a) 1)))
          (Bool.and (Bool.not (Nat.beq k 0))
            (Bool.not (Bool.and negative (Nat.beq (Nat.mod k 2) 0)))))
        reference
        (rootOf fmt (Bool.and negative (Nat.beq (Nat.mod k 2) 1)) (decode fmt a)
          (Int.blt' degree (Int.ofNat 0)) k reference))
      (Kernel.Z.natAbs degree) (Nat.beq (signCode fmt a) 1))
    ((Model.rootn (Model.ofNatBits a : Model fmt) degree).toNatBits)

/--
`rootn` computes the encoding of `Model.rootn x degree`, for every format descriptor, every
value and every integer degree.
-/
theorem rootn_eq_spec {fmt : FloatFormat} (degree : Int) (x : Model fmt) :
    rootn fmt degree x.toNatBits = (Model.rootn x degree).toNatBits := by
  unfold rootn
  rw [Model.ofNatBits_toNatBits, finiteCode_eq, zeroCode_eq, signCode_eq]
  have hmod : ∀ a b : Nat, Nat.mod a b = a % b := fun _ _ => rfl
  simp only [Kernel.Z.natAbs_eq, hmod, Int.ofNat_eq_natCast, Nat.cast_zero]
  refine casesOn_eq_of _ _ _ _ (fun _ => rfl) (fun hguard => ?_)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hguard
  obtain ⟨⟨hfinite, hzero⟩, hk, heven⟩ := hguard
  have hdegree : degree ≠ 0 := by
    intro h
    rw [h] at hk
    exact absurd hk (by decide)
  have hk' : degree.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hdegree
  have hdecode := toDyadic?_eq_decode x hfinite
  have hsignificand :=
    Model.significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdecode hzero
  have hnan := Model.isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hreciprocal : (Int.blt' degree 0 = true) ↔ degree < 0 := Kernel.Z.blt'_iff degree 0
  have hspec : Model.rootn x degree =
      rootRat fmt (Model.signBit x && Nat.beq (degree.natAbs % 2) 1)
        (if Int.blt' degree 0 = true then |(decode fmt x.toNatBits).toRat|⁻¹
          else |(decode fmt x.toNatBits).toRat|) degree.natAbs := by
    unfold Model.rootn
    rw [(Model.chooseNaN1_eq_none_iff x).mpr hnan, hzero,
      Model.isInfinite_eq_false_of_isFinite_eq_true x hfinite, emod_two_ne_zero,
      emod_two_eq_zero, heven]
    simp only [Bool.false_eq_true, ↓reduceIte, hdegree, Model.toRat?, hdecode, Option.map_some,
      rootWithSqrt, hreciprocal]
  rw [hspec]
  exact rootOf_eq fmt _ _ hsignificand _ _ hk' _ rfl

/--
Encoding of the reciprocal square root of the value that `a` encodes, rounded to nearest even
(`rSqrt_eq_spec`). A finite positive nonzero word is decoded and `rootOf` rounds the square root
of the reciprocal of its value. A zero, a negative value, an infinity and a NaN go to the
reference.
-/
def rSqrt (fmt : FloatFormat) (a : Nat) : Nat :=
  (fun reference =>
    Bool.casesOn (motive := fun _ => Nat)
      (Bool.and
        (Bool.and (Nat.beq (finiteCode fmt a) 1) (Bool.not (Nat.beq (zeroCode fmt a) 1)))
        (Bool.not (Nat.beq (signCode fmt a) 1)))
      reference
      (rootOf fmt false (decode fmt a) true 2 reference))
    ((Model.rSqrt (Model.ofNatBits a : Model fmt)).toNatBits)

/-- The rational value of a dyadic that is not negative is its magnitude. -/
theorem toRat_of_negative_eq_false (d : Numerics.Dyadic) (h : d.negative = false) :
    d.toRat = |d.toRat| := by
  rw [abs_toRat]
  unfold Numerics.Dyadic.toRat Numerics.Dyadic.signedSignificand
  simp [h]

/--
`rSqrt` computes the encoding of `Model.rSqrt x`, for every format descriptor and every value.
-/
theorem rSqrt_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    rSqrt fmt x.toNatBits = (Model.rSqrt x).toNatBits := by
  unfold rSqrt
  rw [Model.ofNatBits_toNatBits, finiteCode_eq, zeroCode_eq, signCode_eq]
  refine casesOn_eq_of _ _ _ _ (fun _ => rfl) (fun hguard => ?_)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hguard
  obtain ⟨⟨hfinite, hzero⟩, hsign⟩ := hguard
  have hdecode := toDyadic?_eq_decode x hfinite
  have hsignificand :=
    Model.significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdecode hzero
  have hnan := Model.isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hnegative : (decode fmt x.toNatBits).negative = false := by
    change Nat.beq (signCode fmt x.toNatBits) 1 = false
    rw [signCode_eq]
    exact hsign
  have hspec : Model.rSqrt x =
      rootRat fmt false (if true = true then |(decode fmt x.toNatBits).toRat|⁻¹
        else |(decode fmt x.toNatBits).toRat|) 2 := by
    unfold Model.rSqrt
    rw [(Model.chooseNaN1_eq_none_iff x).mpr hnan, hzero, hsign,
      Model.isInfinite_eq_false_of_isFinite_eq_true x hfinite]
    simp only [Bool.false_eq_true, ↓reduceIte, Model.toRat?, hdecode, Option.map_some, sqrtRat,
      ← toRat_of_negative_eq_false _ hnegative]
  rw [hspec]
  exact rootOf_eq fmt _ _ hsignificand _ _ (by decide) _ rfl

/-! ## `hypot` -/

/--
The place of a square root after its integer part `root`, from the remainder of the radicand,
as two bits (`sqrtQuarter_eq`): zero for an exact root, one for a root below `root + 1/2` and
three for a root above it.
-/
def sqrtQuarter (root remainder : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq remainder 0)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.ble remainder root) 3 1) 0

/-- `sqrtQuarter` is the accuracy of the square root of Lean's model as two bits. -/
theorem sqrtQuarter_eq (root remainder : Nat) :
    sqrtQuarter root remainder =
      accuracyQuarter (if remainder = 0 then Accuracy.exact
        else Accuracy.inexact (if remainder ≤ root then .lt else .gt)) := by
  unfold sqrtQuarter
  by_cases hzero : remainder = 0
  · subst hzero
    rfl
  · have hbeq : Nat.beq remainder 0 = false := by
      cases h : Nat.beq remainder 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hzero
    rw [ite_eq_right hzero, hbeq]
    by_cases hle : remainder ≤ root
    · rw [ite_eq_left hle, Nat.ble_eq_true_of_le hle]
      rfl
    · have hble : Nat.ble remainder root = false := by
        cases h : Nat.ble remainder root
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true h) hle
      rw [ite_eq_right hle, hble]
      rfl

/--
The exponent at which Lean's model takes the integer square root of `m * 2 ^ e`
(`sqrtTarget_eq`): half the exponent, or the exponent that the format asks for at the binade
of the root when that is smaller.
-/
def sqrtTarget (fmt : FloatFormat) (m : Nat) (e : Int) : Int :=
  Kernel.Z.min (Kernel.Z.floorDiv e 2)
    (Kernel.Z.max
      (Kernel.Z.sub
        (Kernel.Z.floorDiv
          (Kernel.Z.add (Kernel.Z.add (Int.ofNat (Nat.succ (Kernel.log2 m))) e) (Int.ofNat 1)) 2)
        (Int.ofNat (Nat.succ fmt.fracWidth)))
      (Kernel.Z.subNat 2 (Nat.add (Nat.pow 2 (Nat.sub fmt.expWidth 1)) fmt.fracWidth)))

/-- `sqrtTarget` is the target exponent of the square root of Lean's model. -/
theorem sqrtTarget_eq (fmt : FloatFormat) (m : Nat) (e : Int) :
    sqrtTarget fmt m e =
      min (e.ediv 2)
        ((FloatFormat.toModel fmt).targetExponent ((totalExponent m e + 1).ediv 2)) := by
  have hediv : ∀ x : Int, x.ediv 2 = x / 2 := fun _ => rfl
  unfold sqrtTarget Float.Model.Format.targetExponent Float.Model.Format.minExponent
    Float.Model.Format.mantissaBits totalExponent
  simp only [hediv, Kernel.Z.min_eq, Kernel.Z.max_eq, Kernel.Z.floorDiv_eq, Kernel.Z.add_eq,
    Kernel.Z.sub_eq, Kernel.Z.subNat_eq, Kernel.log2_eq, FloatFormat.toModel, Nat.add_eq,
    Nat.pow_eq, Nat.sub_eq, Nat.succ_eq_add_one, Int.ofNat_eq_natCast]
  push_cast
  congr 2 <;> omega


/--
Encoding of the square root of the positive dyadic `m * 2 ^ e`, rounded to nearest even
(`sqrtDyadic_eq`), as Lean's model of IEEE arithmetic takes it: the checked integer square root
of the significand shifted to the exponent `sqrtTarget`, its remainder as two more bits, and one
`roundDyadic`. A format that is not an IEEE layout and a root with fewer bits than a
significand are `reference`.
-/
def sqrtDyadic (fmt : FloatFormat) (m : Nat) (e : Int) (reference : Nat) : Nat :=
  (fun target =>
    (fun scaled =>
      (fun root =>
        Bool.casesOn (motive := fun _ => Nat)
          (Bool.and fmt.isIEEE (Nat.ble (Nat.shiftLeft 1 fmt.fracWidth) root))
          reference
          (roundDyadic fmt .nearest
            { negative := false
              significand :=
                Nat.add (Nat.mul 4 root) (sqrtQuarter root (Nat.sub scaled (Nat.mul root root)))
              exponent := Kernel.Z.sub target (Int.ofNat 2) }))
        (Kernel.isqrt scaled))
      (Nat.shiftLeft m (Kernel.Z.toNat (Kernel.Z.sub e (Kernel.Z.mul (Int.ofNat 2) target)))))
    (sqrtTarget fmt m e)

/--
`sqrtDyadic` computes the encoding of the reference square root of a positive dyadic, for every
format descriptor, when `reference` is that encoding.
-/
theorem sqrtDyadic_eq (fmt : FloatFormat) (m : Nat) (e : Int) (hm : m ≠ 0) (reference : Nat)
    (href : reference = (Model.FiniteSqrt.sqrtPositiveDyadic fmt m e).toNatBits) :
    sqrtDyadic fmt m e reference = (Model.FiniteSqrt.sqrtPositiveDyadic fmt m e).toNatBits := by
  have hsub : ∀ a b : Nat, Nat.sub a b = a - b := fun _ _ => rfl
  unfold sqrtDyadic
  simp only [sqrtTarget_eq, sqrtQuarter_eq, Kernel.Z.sub_eq, Kernel.Z.mul_eq, Kernel.Z.toNat_eq,
    Kernel.isqrt_eq, Nat.shiftLeft_eq', hsub, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast,
    Nat.cast_ofNat]
  refine casesOn_eq_of _ _ _ _ (fun _ => href) (fun hguard => ?_)
  simp only [Bool.and_eq_true, Nat.ble_eq] at hguard
  obtain ⟨hfmt, hbits⟩ := hguard
  rw [Nat.shiftLeft_eq, Nat.one_mul] at hbits
  generalize htarget : min (e.ediv 2)
    ((FloatFormat.toModel fmt).targetExponent ((totalExponent m e + 1).ediv 2)) = target at hbits ⊢
  have hsqrt : Model.FiniteSqrt.sqrtPositiveDyadic fmt m e =
      roundCertificate fmt false
        ⟨Nat.sqrt (m <<< (e - 2 * target).toNat), target,
          if m <<< (e - 2 * target).toNat -
              Nat.sqrt (m <<< (e - 2 * target).toNat) * Nat.sqrt (m <<< (e - 2 * target).toNat) = 0
            then Accuracy.exact
          else Accuracy.inexact
            (if m <<< (e - 2 * target).toNat -
                Nat.sqrt (m <<< (e - 2 * target).toNat) *
                  Nat.sqrt (m <<< (e - 2 * target).toNat) ≤
                Nat.sqrt (m <<< (e - 2 * target).toNat) then .lt else .gt)⟩ := by
    unfold Model.FiniteSqrt.sqrtPositiveDyadic roundCertificate
    rw [dite_eq_right hm, ite_eq_left hfmt, ite_eq_left hfmt, Model.NativeModelSqrt.sqrt_eq]
    subst htarget
    rfl
  rw [hsqrt, roundCertificate_eq_roundDyadic fmt false _ hbits, roundDyadic_nearest_eq]

/--
Encoding of the Euclidean norm of the two values that `a` and `b` encode, rounded to nearest
even (`hypot_eq_spec`). Two finite words are decoded, the exact sum of their squares is formed
on natural numbers, and `sqrtDyadic` rounds its square root. A NaN, an infinity and two zeros
go to the reference.
-/
def hypot (fmt : FloatFormat) (a b : Nat) : Nat :=
  (fun reference =>
    Bool.casesOn (motive := fun _ => Nat)
      (Bool.and (Nat.beq (finiteCode fmt a) 1) (Nat.beq (finiteCode fmt b) 1))
      reference
      ((fun sum =>
          Bool.casesOn (motive := fun _ => Nat) (Nat.beq sum.significand 0)
            (sqrtDyadic fmt sum.significand sum.exponent reference)
            reference)
        (addExact (mulExact (decode fmt a) (decode fmt a))
          (mulExact (decode fmt b) (decode fmt b)))))
    ((Model.hypot (Model.ofNatBits a : Model fmt) (Model.ofNatBits b)).toNatBits)

/--
`hypot` computes the encoding of `Model.hypot x y`, for every format descriptor and every pair
of values.
-/
theorem hypot_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    hypot fmt x.toNatBits y.toNatBits = (Model.hypot x y).toNatBits := by
  unfold hypot
  rw [Model.ofNatBits_toNatBits, Model.ofNatBits_toNatBits, finiteCode_eq, finiteCode_eq]
  refine casesOn_eq_of _ _ _ _ (fun _ => rfl) (fun hguard => ?_)
  rw [Bool.and_eq_true] at hguard
  obtain ⟨hx, hy⟩ := hguard
  have hspec := Model.hypot_eq_hypotDyadic x y (toDyadic?_eq_decode x hx)
    (toDyadic?_eq_decode y hy)
  rw [mulExact_eq, mulExact_eq, addExact_eq, ← Numerics.Dyadic.sumSquares_eq]
  refine casesOn_eq_of _ _ _ _ (fun hne => ?_) (fun _ => rfl)
  have hm : ((decode fmt x.toNatBits).sumSquares (decode fmt y.toNatBits)).significand ≠ 0 := by
    intro h
    rw [h] at hne
    exact absurd hne (by decide)
  rw [hspec]
  unfold Model.Algebraic.hypotDyadic
  exact sqrtDyadic_eq fmt _ _ hm _ rfl

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel `rootn` of a stored value: its root of integer degree `n`, rounded to nearest. -/
def rootn (n : Int) (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.rootn format n) (fun x => Model.rootn x n) (rootn_eq_spec n) x

/-- The kernel `rootn` is the model operation carried through the conversions. -/
theorem rootn_eq_lift (n : Int) (x : FloatLib.Floats.ExecFloat F) :
    rootn n x = NatView.liftUnary (fun x => Model.rootn x n) x :=
  unary_eq _ _ _ x

/-- The encoding of a root is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_rootn (n : Int) (x : FloatLib.Floats.ExecFloat F) :
    toNat (rootn n x) = KernelPath.rootn format n (toNat x) :=
  toNat_unary _ _ _ x

/-- Kernel `rSqrt` of a stored value: the reciprocal of its square root, rounded to nearest. -/
def rSqrt (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.rSqrt format) (fun x => Model.rSqrt x) rSqrt_eq_spec x

/-- The kernel `rSqrt` is the model operation carried through the conversions. -/
theorem rSqrt_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    rSqrt x = NatView.liftUnary (fun x => Model.rSqrt x) x :=
  unary_eq _ _ _ x

/-- The encoding of a reciprocal square root is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_rSqrt (x : FloatLib.Floats.ExecFloat F) :
    toNat (rSqrt x) = KernelPath.rSqrt format (toNat x) :=
  toNat_unary _ _ _ x

/-- Kernel `hypot` of two stored values: their Euclidean norm, rounded to nearest. -/
selection hypot := (KernelPath.hypot format), Model.hypot, hypot_eq_spec

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
