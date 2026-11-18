/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Predicates
public meta import FloatLib.Tactic.IeeeExtrema
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MagnitudeExtrema.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Sign operations and the minimum and maximum operations on encodings

The quiet-computational sign operations of IEEE 754-2019 §5.5.1 and the eight minimum and
maximum operations of §9.6 return one of their operands, with its sign bit or its quiet bit
changed at most. On natural-number encodings they are selections between two words:

* `copySign fmt a b` and `abs fmt a` are the encodings of `Model.copySign` and `Model.abs`
  (`copySign_eq_spec`, `abs_eq_spec`).
* `extremum fmt larger a b` is the encoding of `Model.minimum` (`larger := false`) and
  `Model.maximum` (`larger := true`): the NaN that `nanChoice` selects when an operand is a
  NaN, and otherwise the word selected by the comparison code, with `-0` below `+0`
  (`extremum_eq_spec`).
* `extremumNumber fmt larger a b` is the encoding of `Model.minimumNumber` and
  `Model.maximumNumber`, which prefer a number to a NaN (`extremumNumber_eq_spec`).
* `magnitudeExtremum fmt larger base a b` is the encoding of `Model.magnitudeExtremum larger`:
  the selection by the comparison code of the two magnitudes, and the word `base a b` when the
  magnitudes are equal or an operand is a NaN (`magnitudeExtremum_eq_spec`).

Every theorem holds for every format descriptor and all operands, NaNs and both zeros included.
`Value.copySign`, `Value.abs`, `Value.minimum` to `Value.maximumMagnitudeNumber` are these
operations on the stored values of any family with a natural-number view, each with the theorem
that it is the model operation carried through the family's conversions and the rule that its
encoding is the flat operation on the encodings of the operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-! ## Sign operations -/

/--
Encoding of `Model.copySign` (`copySign_eq_spec`): the sign bit of `a` is flipped when it differs
from the sign bit of `b`, except for the zero and the NaN of an unsigned-zero format, whose
words have no exponent or fraction bit set.
-/
def copySign (fmt : FloatFormat) (a b : Nat) : Nat :=
  Nat.xor a
    (Nat.shiftLeft
      (Nat.mul
        (Nat.sub 1 (Nat.sub 1 (Nat.add (Nat.land a (magnitudeMask fmt)) (signedZero fmt))))
        (Nat.xor (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))))
      (signPos fmt))

/-- Encoding of `Model.abs` (`abs_eq_spec`): `copySign` with a clear sign. -/
def abs (fmt : FloatFormat) (a : Nat) : Nat :=
  copySign fmt a 0

/-- The encoding of positive zero is zero. -/
theorem toNatBits_posZero (fmt : FloatFormat) : (Model.posZero fmt).toNatBits = 0 :=
  Model.toNatBits_ofNatBits_of_lt 0 (Nat.two_pow_pos _)

/-- `copySign` computes the encoding of `Model.copySign`, for every format descriptor. -/
theorem copySign_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    copySign fmt x.toNatBits y.toNatBits = (Model.copySign x y).toNatBits := by
  have hlt := fields_lt_two_pow_signPos x
  have hword := toNatBits_eq_fields x
  unfold copySign
  simp only [Nat.xor_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq, Nat.land_eq, Nat.mul_eq,
    Nat.shiftRight_eq', magnitude_toNatBits, sign_toNatBits, Nat.shiftLeft_eq]
  have hsigns : (if Model.signBit x then 1 else 0) ^^^ (if Model.signBit y then 1 else 0) =
      if Model.signBit x == Model.signBit y then 0 else 1 := by
    cases Model.signBit x <;> cases Model.signBit y <;> rfl
  rw [hsigns]
  unfold Model.copySign
  by_cases hsigned : fmt.supportsSignedZero = true
  · have hflag : signedZero fmt = 1 := by
      unfold signedZero
      cases hencoding : fmt.encoding <;>
        simp_all [FloatFormat.supportsSignedZero]
    have h1 : 1 - (1 - (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x + 1)) = 1 := by
      omega
    rw [hflag, h1, Nat.one_mul, hsigned]
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    by_cases hsame : Model.signBit x = Model.signBit y
    · simp [hsame]
    · have hbeq : (Model.signBit x == Model.signBit y) = false := by simpa using hsame
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_mul]
      exact (toNatBits_toggleSign x).symm
  · have hencoding : fmt.encoding = .finiteUnsignedZero := by
      cases h : fmt.encoding <;> simp_all [FloatFormat.supportsSignedZero]
    have hunsigned : fmt.supportsSignedZero = false := by simpa using hsigned
    have hflag : signedZero fmt = 0 := by simp [signedZero, hencoding]
    have hwidth : fmt.bitWidth - 1 = signPos fmt := by
      unfold FloatFormat.bitWidth signPos; omega
    have hnan : Model.isNaN x = true ↔ x.toNatBits = 2 ^ signPos fmt := by
      simp only [Model.isNaN, hencoding, beq_iff_eq]
      rw [← hwidth, ← FloatFormat.signMask_toNat]
      exact BitVec.toNat_inj.symm
    have hzero : Model.isZero x = true ↔ x.toNatBits = 0 := by
      simp only [Model.isZero, hencoding, beq_iff_eq]
      exact BitVec.toNat_inj.symm
    rw [hflag, Nat.add_zero, hunsigned]
    simp only [Bool.not_false, Bool.true_and]
    generalize Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x = u at hlt hword ⊢
    by_cases hmagnitude : u = 0
    · subst hmagnitude
      have hcond : (Model.isNaN x || Model.isZero x) = true := by
        rw [Bool.or_eq_true, hnan, hzero, hword]
        cases Model.signBit x <;> simp
      rw [ite_eq_left hcond]
      simp
    · have h1 : 1 - (1 - u) = 1 := by omega
      have hcond : ¬ (Model.isNaN x || Model.isZero x) = true := by
        rw [Bool.or_eq_true, hnan, hzero, hword]
        cases Model.signBit x
        · simp
          omega
        · simp
          omega
      rw [ite_eq_right hcond, h1, Nat.one_mul]
      by_cases hsame : Model.signBit x = Model.signBit y
      · simp [hsame]
      · have hbeq : (Model.signBit x == Model.signBit y) = false := by simpa using hsame
        rw [hbeq]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_mul]
        exact (toNatBits_toggleSign x).symm

/-- `abs` computes the encoding of `Model.abs`, for every format descriptor. -/
theorem abs_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    abs fmt x.toNatBits = (Model.abs x).toNatBits := by
  unfold abs Model.abs
  rw [← copySign_eq_spec, toNatBits_posZero]

/-! ## Selection between two numbers -/

/--
The word that `Model.minimum` (`larger := false`) or `Model.maximum` (`larger := true`) selects
from two words that are not NaNs: the second word when the comparison code says so, and when
both words are zeros and the first has the sign that the operation does not prefer.
-/
def extremumOfNumbers (fmt : FloatFormat) (larger : Bool) (a b : Nat) : Nat :=
  (fun code =>
    Bool.casesOn (motive := fun _ => Nat)
      (Bool.casesOn (motive := fun _ => Bool) larger (Nat.beq code 2) (Nat.beq code 0) ||
        (Nat.beq code 1 && Nat.beq (zeroCode fmt a) 1 && Nat.beq (zeroCode fmt b) 1 &&
          Bool.casesOn (motive := fun _ => Bool) larger (!Nat.beq (signCode fmt a) 1)
            (Nat.beq (signCode fmt a) 1)))
      a b)
    (compareCode fmt a b)

/--
Encoding of `Model.minimum` (`larger := false`) and `Model.maximum` (`larger := true`): the NaN
that `nanChoice` selects when a word is a NaN, and `extremumOfNumbers` otherwise.
-/
def extremum (fmt : FloatFormat) (larger : Bool) (a b : Nat) : Nat :=
  (fun nanA nanB =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.add nanA nanB) 0)
      (nanChoice fmt a b (Nat.mul nanA (signalingFlag fmt a)) (Nat.mul nanB (signalingFlag fmt b))
        nanA)
      (extremumOfNumbers fmt larger a b))
    (nanCode fmt a) (nanCode fmt b)

/--
Encoding of `Model.minimumNumber` (`larger := false`) and `Model.maximumNumber`
(`larger := true`): the other word when exactly one is a NaN, for two NaNs the first one
quieted unless only the second is signaling, and `extremumOfNumbers` otherwise.
-/
def extremumNumber (fmt : FloatFormat) (larger : Bool) (a b : Nat) : Nat :=
  (fun nanA nanB =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq nanA 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq nanB 0)
        (Nat.lor
          (Bool.casesOn (motive := fun _ => Nat)
            (Nat.beq (Nat.mul (Nat.sub 1 (signalingFlag fmt a)) (signalingFlag fmt b)) 0) b a)
          (quietMask fmt))
        b)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq nanB 0) a
        (extremumOfNumbers fmt larger a b)))
    (nanCode fmt a) (nanCode fmt b)

/--
Encoding of `Model.magnitudeExtremum larger`: by the comparison code of the two magnitudes the
first or the second word, and the word `base a b` when the magnitudes are equal or a word is a
NaN.
-/
def magnitudeExtremum (fmt : FloatFormat) (larger : Bool) (base : Nat → Nat → Nat) (a b : Nat) :
    Nat :=
  (fun code =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq code 0)
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq code 2) (base a b)
        (Bool.casesOn (motive := fun _ => Nat) larger b a))
      (Bool.casesOn (motive := fun _ => Nat) larger a b))
    (compareCode fmt (abs fmt a) (abs fmt b))

/-! ## Classification of an encoding, as numbers -/

/-- `nanCode` of an encoding is one for a NaN and zero otherwise. -/
theorem nanCode_toNatBits {fmt : FloatFormat} (x : Model fmt) :
    nanCode fmt x.toNatBits = if Model.isNaN x then 1 else 0 := by
  unfold nanCode
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, nanFlag_eq]

/-- A zero is the zero of its own sign. -/
theorem zero_signBit_of_isZero {fmt : FloatFormat} (x : Model fmt)
    (hzero : Model.isZero x = true) : Model.zero fmt (Model.signBit x) = x := by
  have hfields := Model.isZero_ofFields fmt (Model.signBit x) _ _ (Model.expField_lt_pow2 x)
    (Model.fracField_lt_pow2 x)
  rw [Model.ofFields_signBit_expField_fracField x, hzero] at hfields
  have hx : Model.expField x = 0 ∧ Model.fracField x = 0 ∧
      (Model.signBit x && fmt.supportsSignedZero) = Model.signBit x := by
    unfold FloatFormat.supportsSignedZero
    revert hfields
    cases fmt.encoding <;> cases Model.signBit x <;> simp
  apply eq_of_fields_eq
  · rw [Model.signBit_zero, hx.2.2]
  · rw [hx.1, hx.2.1]
    unfold Model.zero
    split <;> simp

/-! ## The selections compute the model operations -/

/-- The comparison of two values that are not NaNs, as a comparison code. -/
theorem compareNonNaN_eq_code {fmt : FloatFormat} (x y : Model fmt)
    (hx : Model.isNaN x = false) (hy : Model.isNaN y = false) :
    decodeOrdering (compareCode fmt x.toNatBits y.toNatBits) =
      some (Model.compareNonNaN x y hx hy) := by
  rw [compareCode_eq]
  unfold Model.compare
  simp [hx, hy]

/--
`extremumOfNumbers` computes the encoding of `Model.maximum` (`larger := true`) and of
`Model.minimum` (`larger := false`) on two values that are not NaNs, for every format
descriptor.
-/
theorem extremumOfNumbers_eq_spec {fmt : FloatFormat} (larger : Bool) (x y : Model fmt)
    (hx : Model.isNaN x = false) (hy : Model.isNaN y = false) :
    extremumOfNumbers fmt larger x.toNatBits y.toNatBits =
      (bif larger then Model.Internal.Value.maximum x y
        else Model.Internal.Value.minimum x y).toNatBits := by
  have hsel : Model.chooseNaN2 x y = none := (Model.chooseNaN2_eq_none_iff x y).2 ⟨hx, hy⟩
  have hcode := compareNonNaN_eq_code x y hx hy
  unfold Model.Internal.Value.maximum Model.Internal.Value.minimum extremumOfNumbers
  rw [Model.withNaNSelection_of_none _ _ hsel, Model.withNaNSelection_of_none _ _ hsel]
  simp only [zeroCode_eq, signCode_eq]
  generalize compareCode fmt x.toNatBits y.toNatBits = code at hcode ⊢
  simp only [← decodeOrdering_beq_lt, ← decodeOrdering_beq_eq, ← decodeOrdering_beq_gt, hcode]
  generalize Model.compareNonNaN x y _ _ = ordering
  cases larger <;> cases ordering <;> try rfl
  · change _ = (if Model.isZero x && Model.isZero y then _ else x).toNatBits
    cases hzx : Model.isZero x <;> cases hzy : Model.isZero y <;>
      cases hsx : Model.signBit x <;> try rfl
    · change y.toNatBits = (Model.zero fmt (false || Model.signBit y)).toNatBits
      rw [Bool.false_or, zero_signBit_of_isZero y hzy]
    · change x.toNatBits = (Model.zero fmt (true || Model.signBit y)).toNatBits
      rw [Bool.true_or, ← hsx, zero_signBit_of_isZero x hzx]
  · change _ = (if Model.isZero x && Model.isZero y then _ else x).toNatBits
    cases hzx : Model.isZero x <;> cases hzy : Model.isZero y <;>
      cases hsx : Model.signBit x <;> try rfl
    · change x.toNatBits = (Model.zero fmt (false && Model.signBit y)).toNatBits
      rw [Bool.false_and, ← hsx, zero_signBit_of_isZero x hzx]
    · change y.toNatBits = (Model.zero fmt (true && Model.signBit y)).toNatBits
      rw [Bool.true_and, zero_signBit_of_isZero y hzy]

/--
The NaN branch of a two-operand selection on encodings: with a NaN operand the result of
`Model.withNaNSelection (Model.chooseNaN2 x y)` is `nanChoice`, and otherwise the word of the
rest of the operation.
-/
theorem withNaNSelection_bits {fmt : FloatFormat} (x y : Model fmt)
    (rest : Model.chooseNaN2 x y = none → Model fmt) (word : Nat)
    (hrest : ∀ hsel, Model.isNaN x = false → Model.isNaN y = false →
      (rest hsel).toNatBits = word) :
    (Model.withNaNSelection (Model.chooseNaN2 x y) rest).toNatBits =
      Bool.casesOn (motive := fun _ => Nat)
        (Nat.beq (Nat.add (nanCode fmt x.toNatBits) (nanCode fmt y.toNatBits)) 0)
        (nanChoice fmt x.toNatBits y.toNatBits
          (Nat.mul (nanCode fmt x.toNatBits) (signalingFlag fmt x.toNatBits))
          (Nat.mul (nanCode fmt y.toNatBits) (signalingFlag fmt y.toNatBits))
          (nanCode fmt x.toNatBits))
        word := by
  rw [nanCode_toNatBits, nanCode_toNatBits]
  rcases Option.eq_none_or_eq_some (Model.chooseNaN2 x y) with hsel | ⟨nan, hsel⟩
  · obtain ⟨hx, hy⟩ := (Model.chooseNaN2_eq_none_iff x y).1 hsel
    rw [Model.withNaNSelection_of_none _ _ hsel, hx, hy]
    exact hrest hsel hx hy
  · rw [Model.withNaNSelection_of_some _ _ nan hsel]
    have hbits := chooseNaN2_getD_bits x y nan nan.toNatBits (fun _ _ => rfl)
    rw [hsel] at hbits
    cases hx : Model.isNaN x <;> cases hy : Model.isNaN y
    · rw [(Model.chooseNaN2_eq_none_iff x y).2 ⟨hx, hy⟩] at hsel
      exact absurd hsel (by simp)
    all_goals
      rw [hx, hy] at hbits
      exact hbits

/--
`extremum` computes the encoding of `Model.maximum` (`larger := true`) and of `Model.minimum`
(`larger := false`), for every format descriptor and all operands.
-/
theorem extremum_eq_spec {fmt : FloatFormat} (larger : Bool) (x y : Model fmt) :
    extremum fmt larger x.toNatBits y.toNatBits =
      (bif larger then Model.Internal.Value.maximum x y
        else Model.Internal.Value.minimum x y).toNatBits := by
  have hnumbers := extremumOfNumbers_eq_spec larger x y
  cases larger
  · change _ = (Model.Internal.Value.minimum x y).toNatBits
    unfold Model.Internal.Value.minimum at hnumbers ⊢
    refine (withNaNSelection_bits x y _ _ fun hsel hx hy => ?_).symm
    rw [hnumbers hx hy, Bool.cond_false, Model.withNaNSelection_of_none _ _ hsel]
  · change _ = (Model.Internal.Value.maximum x y).toNatBits
    unfold Model.Internal.Value.maximum at hnumbers ⊢
    refine (withNaNSelection_bits x y _ _ fun hsel hx hy => ?_).symm
    rw [hnumbers hx hy, Bool.cond_true, Model.withNaNSelection_of_none _ _ hsel]

/--
The NaN rule of `minimumNumber` and `maximumNumber` on encodings: the other word when exactly
one operand is a NaN, the quieted NaN that `Model.bothNaNNumber` selects for two NaNs, and
otherwise the word of the operation on two numbers.
-/
theorem number_bits {fmt : FloatFormat} (x y rest : Model fmt) (word : Nat)
    (hrest : Model.isNaN x = false → Model.isNaN y = false → rest.toNatBits = word) :
    (if Model.isNaN x then (if Model.isNaN y then Model.bothNaNNumber x y else y)
      else if Model.isNaN y then x else rest).toNatBits =
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanCode fmt x.toNatBits) 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanCode fmt y.toNatBits) 0)
          (Nat.lor
            (Bool.casesOn (motive := fun _ => Nat)
              (Nat.beq (Nat.mul (Nat.sub 1 (signalingFlag fmt x.toNatBits))
                (signalingFlag fmt y.toNatBits)) 0) y.toNatBits x.toNatBits)
            (quietMask fmt))
          y.toNatBits)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanCode fmt y.toNatBits) 0) x.toNatBits
          word) := by
  rw [nanCode_toNatBits, nanCode_toNatBits]
  cases hx : Model.isNaN x <;> cases hy : Model.isNaN y
  · exact hrest hx hy
  · rfl
  · rfl
  · change (Model.bothNaNNumber x y).toNatBits = _
    unfold Model.bothNaNNumber
    rw [signalingFlag_eq x hx, signalingFlag_eq y hy]
    cases Model.isSignaling x <;> cases Model.isSignaling y <;>
      simp [quietNaN_bits x hx, quietNaN_bits y hy] <;> rfl

/--
`extremumNumber` computes the encoding of `Model.maximumNumber` (`larger := true`) and of
`Model.minimumNumber` (`larger := false`), for every format descriptor and all operands.
-/
theorem extremumNumber_eq_spec {fmt : FloatFormat} (larger : Bool) (x y : Model fmt) :
    extremumNumber fmt larger x.toNatBits y.toNatBits =
      (bif larger then Model.Internal.Value.maximumNumber x y
        else Model.Internal.Value.minimumNumber x y).toNatBits := by
  have hnumbers := extremumOfNumbers_eq_spec larger x y
  cases larger
  · exact (number_bits x y _ _ fun hx hy => (hnumbers hx hy).symm).symm
  · exact (number_bits x y _ _ fun hx hy => (hnumbers hx hy).symm).symm

/--
`magnitudeExtremum` computes the encoding of `Model.magnitudeExtremum larger base`, for every
format descriptor, when `flat` computes the encoding of `base`.
-/
theorem magnitudeExtremum_eq_spec {fmt : FloatFormat} (larger : Bool)
    {base : Model fmt → Model fmt → Model fmt} {flat : Nat → Nat → Nat}
    (hbase : ∀ x y, flat x.toNatBits y.toNatBits = (base x y).toNatBits) (x y : Model fmt) :
    magnitudeExtremum fmt larger flat x.toNatBits y.toNatBits =
      (Model.magnitudeExtremum larger base x y).toNatBits := by
  have hcode := compareCode_eq (Model.abs x) (Model.abs y)
  rw [← abs_eq_spec, ← abs_eq_spec] at hcode
  change _ = (Model.Internal.Value.magnitudeExtremum larger base x y).toNatBits
  unfold magnitudeExtremum Model.Internal.Value.magnitudeExtremum
  simp only []
  rw [← hcode, hbase]
  generalize compareCode fmt (abs fmt x.toNatBits) (abs fmt y.toNatBits) = code
  rcases code with _ | _ | _ | code <;> cases larger <;> rfl

/-! ## The operations on stored values -/

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel absolute value of a stored value. -/
def abs (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.abs format) Model.abs abs_eq_spec x

/-- The kernel absolute value is the model operation carried through the conversions. -/
theorem abs_eq_lift (x : FloatLib.Floats.ExecFloat F) : abs x = NatView.liftUnary Model.abs x :=
  unary_eq _ _ _ x

/-- The encoding of an absolute value is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_abs (x : FloatLib.Floats.ExecFloat F) :
    toNat (abs x) = KernelPath.abs format (toNat x) :=
  toNat_unary _ _ _ x


/-- Kernel `copySign`: the first stored value with the sign of the second. -/
selection copySign := (KernelPath.copySign format), Model.copySign, copySign_eq_spec

/-- Kernel `minimum` of two stored values (IEEE 754-2019 §9.6). -/
selection minimum := (extremum format false), (fun x y => Model.minimum x y),
  (extremum_eq_spec false)

/-- Kernel `maximum` of two stored values (IEEE 754-2019 §9.6). -/
selection maximum := (extremum format true), (fun x y => Model.maximum x y),
  (extremum_eq_spec true)

/-- Kernel `minimumNumber` of two stored values (IEEE 754-2019 §9.6). -/
selection minimumNumber := (extremumNumber format false),
  (fun x y => Model.minimumNumber x y), (extremumNumber_eq_spec false)

/-- Kernel `maximumNumber` of two stored values (IEEE 754-2019 §9.6). -/
selection maximumNumber := (extremumNumber format true),
  (fun x y => Model.maximumNumber x y), (extremumNumber_eq_spec true)

/-- Kernel `minimumMagnitude` of two stored values (IEEE 754-2019 §9.6). -/
selection minimumMagnitude := (magnitudeExtremum format false (extremum format false)),
  (fun x y => Model.magnitudeExtremum false (fun x y => Model.minimum x y) x y),
  (magnitudeExtremum_eq_spec false (extremum_eq_spec false))

/-- Kernel `maximumMagnitude` of two stored values (IEEE 754-2019 §9.6). -/
selection maximumMagnitude := (magnitudeExtremum format true (extremum format true)),
  (fun x y => Model.magnitudeExtremum true (fun x y => Model.maximum x y) x y),
  (magnitudeExtremum_eq_spec true (extremum_eq_spec true))

/-- Kernel `minimumMagnitudeNumber` of two stored values (IEEE 754-2019 §9.6). -/
selection minimumMagnitudeNumber :=
  (magnitudeExtremum format false (extremumNumber format false)),
  (fun x y => Model.magnitudeExtremum false (fun x y => Model.minimumNumber x y) x y),
  (magnitudeExtremum_eq_spec false (extremumNumber_eq_spec false))

/-- Kernel `maximumMagnitudeNumber` of two stored values (IEEE 754-2019 §9.6). -/
selection maximumMagnitudeNumber :=
  (magnitudeExtremum format true (extremumNumber format true)),
  (fun x y => Model.magnitudeExtremum true (fun x y => Model.maximumNumber x y) x y),
  (magnitudeExtremum_eq_spec true (extremumNumber_eq_spec true))

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
