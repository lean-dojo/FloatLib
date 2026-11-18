/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Scale
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Payload.Runtime

/-!
# `getPayload` on encodings

IEEE 754-2019 §9.7 `getPayload` delivers the payload of a NaN as a floating-point integer and
`-1` for an operand that is not a NaN. `Model.getPayload` casts the payload, a natural number,
into the format with one rounding to nearest-even.

`getPayload fmt a` computes the encoding of the result from the word `a`: the payload is the
word under the payload mask, as `KernelPath.cast` reads it, and `KernelPath.roundInteger` rounds
it; a word that is not a NaN gives the word of `-1`. `getPayload_eq_spec` proves it equal to the
encoding of `Model.getPayload` for every format descriptor and value.

`Value.getPayload` is the operation on stored values, with `Value.getPayload_eq_lift` and the
rule `Value.toNat_getPayload`.
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

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
