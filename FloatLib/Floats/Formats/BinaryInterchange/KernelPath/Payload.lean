/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Payload.Runtime

/-!
# The payload operations on encodings

IEEE 754-2019 §9.7 `getPayload` delivers the payload of a NaN as a floating-point integer and
`-1` for an operand that is not a NaN. `Model.getPayload` casts the payload, a natural number,
into the format with one rounding to nearest-even. `setPayload` and `setPayloadSignaling`
deliver the quiet and the signaling NaN with the payload that their operand names, and `+0` for
an operand that names none.

`getPayload fmt a` computes the encoding of the result from the word `a`: the payload is the
word under the payload mask, as `KernelPath.cast` reads it, and `KernelPath.roundInteger` rounds
it; a word that is not a NaN gives the word of `-1`. `getPayload_eq_spec` proves it equal to the
encoding of `Model.getPayload` for every format descriptor and value.

`admissiblePayload? fmt a` is the payload that the word `a` names: the reference test of
`Model.admissiblePayload?` on the exact value `KernelPath.exactValue` of the word, with the
comparison of the candidate payload against the operand made on encodings
(`admissiblePayload?_eq`). `setPayload fmt a` and `setPayloadSignaling fmt a` build the word of
the NaN from it, and `setPayload_eq_spec` and `setPayloadSignaling_eq_spec` prove them equal to
the encodings of `Model.setPayload` and `Model.setPayloadSignaling`, for every format
descriptor and value.

`Value.getPayload`, `Value.setPayload` and `Value.setPayloadSignaling` are the operations on
stored values, with their `_eq_lift` theorems and the rules `Value.toNat_getPayload`,
`Value.toNat_setPayload` and `Value.toNat_setPayloadSignaling`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-- The encoding of `-1` in `fmt`. -/
def negOneWord (fmt : FloatFormat) : Nat :=
  (Model.negOne fmt).toNatBits

/--
Encoding of the payload of the NaN that `a` encodes, as a number of the format, and of `-1`
when `a` is not a NaN (`getPayload_eq_spec`).
-/
def getPayload (fmt : FloatFormat) (a : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanCode fmt a) 1) (negOneWord fmt)
    (roundInteger fmt .nearest false (Nat.land a (payloadMask fmt)))

/--
`getPayload` computes the encoding of `Model.getPayload x`, for every format descriptor and
every value.
-/
theorem getPayload_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    getPayload fmt x.toNatBits = (Model.getPayload x).toNatBits := by
  unfold getPayload Model.getPayload
  rw [nanCode_eq]
  cases hnan : Model.isNaN x
  · rfl
  · change roundInteger fmt .nearest false (x.toNatBits &&& payloadMask fmt) =
      ((Model.nanPayload x : Nat) : Model fmt).toNatBits
    rw [payload_eq x hnan, roundInteger_eq]
    rfl

/--
The payload that the word `a` names (`admissiblePayload?_eq`): `some n` exactly when `a` is the
encoding of the natural number `n` below the payload bound of the format. The exponent is
tested before the integer is formed, so a format with a wide exponent field costs no more.
-/
def admissiblePayload? (fmt : FloatFormat) (a : Nat) : Option Nat :=
  match exactValue fmt a with
  | .finite value =>
      if value.negative || (fmt.fracWidth : Int) < value.exponent then
        none
      else
        let payload := (Model.roundDyadicToInt .towardZero value).toNat
        if payload < Model.payloadBound fmt ∧ roundInteger fmt .nearest false payload = a then
          some payload
        else
          none
  | .infinity _ | .nan _ _ _ => none

/--
Encoding of the quiet NaN with the payload that `a` names, and of `+0` when it names none
(`setPayload_eq_spec`).
-/
def setPayload (fmt : FloatFormat) (a : Nat) : Nat :=
  match admissiblePayload? fmt a with
  | some payload => nanWord fmt 0 payload
  | none => 0

/--
Encoding of the signaling NaN with the nonzero payload that `a` names in an IEEE encoding, and
of `+0` otherwise (`setPayloadSignaling_eq_spec`).
-/
def setPayloadSignaling (fmt : FloatFormat) (a : Nat) : Nat :=
  match fmt.encoding, admissiblePayload? fmt a with
  | .ieee, some payload =>
      if payload = 0 then 0
      else Nat.add (Nat.mul fmt.expAllOnesNat (Nat.pow 2 fmt.fracWidth)) payload
  | _, _ => 0

/-- Two values are equal exactly when their encodings are. -/
theorem toNatBits_eq_iff {fmt : FloatFormat} (x y : Model fmt) :
    x.toNatBits = y.toNatBits ↔ x = y := by
  constructor
  · intro h
    rw [← Model.ofNatBits_toNatBits x, ← Model.ofNatBits_toNatBits y, h]
  · intro h
    rw [h]

/-- `admissiblePayload?` computes the payload that a value names, on its encoding. -/
theorem admissiblePayload?_eq {fmt : FloatFormat} (x : Model fmt) :
    admissiblePayload? fmt x.toNatBits = Model.admissiblePayload? x := by
  have hcast : ∀ p : Nat,
      roundInteger fmt .nearest false p = x.toNatBits ↔ ((p : Nat) : Model fmt) = x := by
    intro p
    rw [roundInteger_eq]
    exact toNatBits_eq_iff _ x
  unfold admissiblePayload? Model.admissiblePayload?
  rw [exactValue_eq]
  cases Model.exactValue x with
  | finite value =>
      dsimp only
      by_cases hguard :
          (value.negative || decide ((fmt.fracWidth : Int) < value.exponent)) = true
      · rw [ite_eq_left hguard, ite_eq_left hguard]
      · rw [ite_eq_right hguard, ite_eq_right hguard]
        by_cases hpayload :
            (Model.roundDyadicToInt .towardZero value).toNat < Model.payloadBound fmt ∧
              (((Model.roundDyadicToInt .towardZero value).toNat : Nat) : Model fmt) = x
        · rw [ite_eq_left hpayload, ite_eq_left ⟨hpayload.1, (hcast _).2 hpayload.2⟩]
        · rw [ite_eq_right hpayload, ite_eq_right fun h => hpayload ⟨h.1, (hcast _).1 h.2⟩]
  | infinity _ => rfl
  | nan _ _ _ => rfl

/-- A payload that a word names is below the payload bound of the format. -/
theorem lt_payloadBound_of_admissiblePayload? {fmt : FloatFormat} {a n : Nat}
    (h : admissiblePayload? fmt a = some n) : n < Model.payloadBound fmt := by
  unfold admissiblePayload? at h
  generalize exactValue fmt a = exact at h
  cases exact with
  | finite value =>
      dsimp only at h
      by_cases hguard :
          (value.negative || decide ((fmt.fracWidth : Int) < value.exponent)) = true
      · rw [ite_eq_left hguard] at h
        cases h
      · rw [ite_eq_right hguard] at h
        by_cases hpayload :
            (Model.roundDyadicToInt .towardZero value).toNat < Model.payloadBound fmt ∧
              roundInteger fmt .nearest false
                (Model.roundDyadicToInt .towardZero value).toNat = a
        · rw [ite_eq_left hpayload] at h
          cases h
          exact hpayload.1
        · rw [ite_eq_right hpayload] at h
          cases h
  | infinity _ => cases h
  | nan _ _ _ => cases h

/--
`setPayload` computes the encoding of `Model.setPayload x`, for every format descriptor and
every value.
-/
theorem setPayload_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    setPayload fmt x.toNatBits = (Model.setPayload x).toNatBits := by
  unfold setPayload Model.setPayload
  rw [admissiblePayload?_eq]
  cases Model.admissiblePayload? x with
  | none => exact (toNatBits_posZero fmt).symm
  | some payload => exact nanWord_eq fmt false payload

/--
`setPayloadSignaling` computes the encoding of `Model.setPayloadSignaling x`, for every format
descriptor and every value.
-/
theorem setPayloadSignaling_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    setPayloadSignaling fmt x.toNatBits = (Model.setPayloadSignaling x).toNatBits := by
  have hbound := fun n (h : admissiblePayload? fmt x.toNatBits = some n) =>
    lt_payloadBound_of_admissiblePayload? h
  unfold setPayloadSignaling Model.setPayloadSignaling
  rw [admissiblePayload?_eq] at hbound ⊢
  cases hencoding : fmt.encoding <;> cases hpayload : Model.admissiblePayload? x <;>
    simp only [toNatBits_posZero]
  rename_i payload
  have hlt : payload < 2 ^ fmt.fracWidth := by
    have h := hbound payload hpayload
    simp only [Model.payloadBound, hencoding] at h
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  have hexp : fmt.expAllOnesNat < 2 ^ fmt.expWidth := by
    unfold FloatFormat.expAllOnesNat
    have := Nat.two_pow_pos fmt.expWidth
    omega
  by_cases hzero : payload = 0
  · simp only [hzero, ite_true, toNatBits_posZero]
  · simp only [hzero, ite_false]
    rw [toNatBits_ofFields fmt false _ _ hexp hlt]
    simp

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel `getPayload` of a stored value. -/
def getPayload (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.getPayload format) (fun x => Model.getPayload x) getPayload_eq_spec x

/-- The kernel `getPayload` is the model operation carried through the conversions. -/
theorem getPayload_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    getPayload x = NatView.liftUnary (fun x => Model.getPayload x) x :=
  unary_eq _ _ _ x

/-- The encoding of a `getPayload` is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_getPayload (x : FloatLib.Floats.ExecFloat F) :
    toNat (getPayload x) = KernelPath.getPayload format (toNat x) :=
  toNat_unary _ _ _ x

/-- Kernel `setPayload` of a stored value. -/
def setPayload (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.setPayload format) (fun x => Model.setPayload x) setPayload_eq_spec x

/-- The kernel `setPayload` is the model operation carried through the conversions. -/
theorem setPayload_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    setPayload x = NatView.liftUnary (fun x => Model.setPayload x) x :=
  unary_eq _ _ _ x

/-- The encoding of a `setPayload` is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_setPayload (x : FloatLib.Floats.ExecFloat F) :
    toNat (setPayload x) = KernelPath.setPayload format (toNat x) :=
  toNat_unary _ _ _ x

/-- Kernel `setPayloadSignaling` of a stored value. -/
def setPayloadSignaling (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.setPayloadSignaling format) (fun x => Model.setPayloadSignaling x)
    setPayloadSignaling_eq_spec x

/-- The kernel `setPayloadSignaling` is the model operation carried through the conversions. -/
theorem setPayloadSignaling_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    setPayloadSignaling x = NatView.liftUnary (fun x => Model.setPayloadSignaling x) x :=
  unary_eq _ _ _ x

/-- The encoding of a `setPayloadSignaling` is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_setPayloadSignaling (x : FloatLib.Floats.ExecFloat F) :
    toNat (setPayloadSignaling x) = KernelPath.setPayloadSignaling format (toNat x) :=
  toNat_unary _ _ _ x

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
