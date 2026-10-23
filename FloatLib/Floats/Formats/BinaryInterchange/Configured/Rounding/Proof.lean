/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Packing correctness for configured binary arithmetic

The decoding bridge theorems `toModel_add` through `toModel_sqrt` and their
`IEEEOutcome.toModel_add` through `IEEEOutcome.toModel_sqrt` companions state that decoding a
configured result recovers the single descriptor-model operation used to compute it, with the same
rounding direction and, for the outcomes, the same flags and ternary value. They let proofs
transfer results from the model without depending on the configured storage plan.
`toModel_hAdd`, `toModel_hSub`, `toModel_hMul`, `toModel_hDiv`, `toModel_neg`, and
`toModel_execFloat_sqrt` do the same for the notation `+`, `-`, `*`, `/`, unary `-`, and the
generic `ExecFloat.sqrt`, so `simp` turns a goal about `toModel (a + b)` into one about
`Model.add`. The projection theorems `value_add` through `value_sqrt` mirror the model's: the
value of an operation with `status := true` is the value of the same operation without it.

A nearest-even call without status runs the format's selected capability. A capability certifies
its kernels against its own reference operation, so the value theorems take the instance argument
`ExecFloat.Capability.HasSpec cap Configured.Spec.add` (and its siblings): the selected capability's
reference is the configured model operation. Instance search proves it for every capability
instance in the library, generic, automatic, and first-order binary32 and binary64, since each
declares that reference. A custom capability whose reference operation is only propositionally
the model operation must declare the instance itself. A capability with another reference
operation gets neither the decoding nor the projection theorems, because its default call and its
`status := true` call can then deliver different values.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

namespace IEEEOutcome

/-- Repacking and then decoding a model outcome preserves its value, status, and ternary value. -/
@[simp, grind =] theorem toModel_ofModel (outcome : Model.IEEEOutcome format) :
    toModel (ofModel (plan := plan) (code := code) outcome) = outcome := by
  cases outcome
  simp [toModel, ofModel]

omit [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] in
/-- `bind` delivers the value of its second step. -/
@[simp] theorem value_bind
    (outcome : IEEEOutcome (format := format) (plan := plan) (code := code))
    (next : Value → IEEEOutcome (format := format) (plan := plan) (code := code)) :
    (outcome.bind next).value = (next outcome.value).value :=
  rfl

omit [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] in
/-- `bind` raises every flag that either step raised. -/
@[simp] theorem status_bind
    (outcome : IEEEOutcome (format := format) (plan := plan) (code := code))
    (next : Value → IEEEOutcome (format := format) (plan := plan) (code := code)) :
    (outcome.bind next).status = outcome.status.union (next outcome.value).status :=
  rfl

omit [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] in
/-- `bind` keeps the ternary value of its second step. -/
@[simp] theorem ternary_bind
    (outcome : IEEEOutcome (format := format) (plan := plan) (code := code))
    (next : Value → IEEEOutcome (format := format) (plan := plan) (code := code)) :
    (outcome.bind next).ternary = (next outcome.value).ternary :=
  rfl

end IEEEOutcome

/-- Decoding a rounded rational gives the model rounding with the same direction. -/
@[simp, grind =] theorem toModel_ofRat (q : Rat) (mode : Model.IEEERoundingMode) :
    toModel (ofRat (format := format) (plan := plan) (code := code) q (mode := mode)) =
      Model.ofRat format q (mode := mode) := by
  simp [ofRat]

/-- Decoding a rounded rational with `status := true` preserves the flags and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_ofRat (q : Rat) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel
        (ofRat (format := format) (plan := plan) (code := code) q (mode := mode)
          (status := true)) =
      Model.ofRat format q (mode := mode) (status := true) := by
  simp [ofRat]

/-- Rounding a rational with `status := true` delivers the value of the same rounding. -/
@[simp] theorem value_ofRat (q : Rat) (mode : Model.IEEERoundingMode) :
    (ofRat (format := format) (plan := plan) (code := code) q (mode := mode)
        (status := true)).value =
      ofRat q (mode := mode) :=
  rfl

/--
Decoding configured addition gives model addition with the same rounding mode.

The nearest-even call runs the selected `ExecFloat.Add` capability, so the theorem asks, as an
instance argument, that its reference operation be `Configured.Spec.add`, the configured model
operation. Instance search proves this for every capability the library declares. A custom
capability whose reference is only propositionally that operation must declare the instance, and
one with another reference operation does not satisfy the theorem.
-/
@[simp, grind =] theorem toModel_add
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    toModel (add left right (mode := mode)) =
      Model.add (toModel left) (toModel right) (mode := mode) := by
  cases mode
  case nearest =>
    change toModel (ExecFloat.add left right) = _
    rw [ExecFloat.Proof.add_eq_spec, ExecFloat.Spec.add, ExecFloat.Add.spec,
      ExecFloat.Capability.HasSpec.spec_eq (cap := cap) (spec := Configured.Spec.add)]
    simp [Configured.Spec.add, toModel, Configured.Family.toModel, Model.Proof.add_eq_spec]
  all_goals simp [add, toModel, Configured.Family.toModel]

/--
Decoding configured subtraction gives model subtraction with the same rounding mode.

As for `toModel_add`, the nearest-even call runs the selected `ExecFloat.Sub` capability, whose
reference operation the instance argument fixes to `Configured.Spec.sub`.
-/
@[simp, grind =] theorem toModel_sub
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    toModel (sub left right (mode := mode)) =
      Model.sub (toModel left) (toModel right) (mode := mode) := by
  cases mode
  case nearest =>
    change toModel (ExecFloat.sub left right) = _
    rw [ExecFloat.Proof.sub_eq_spec, ExecFloat.Spec.sub, ExecFloat.Sub.spec,
      ExecFloat.Capability.HasSpec.spec_eq (cap := cap) (spec := Configured.Spec.sub)]
    simp [Configured.Spec.sub, toModel, Configured.Family.toModel, Model.Proof.sub_eq_spec]
  all_goals simp [sub, toModel, Configured.Family.toModel]

/--
Decoding configured multiplication gives model multiplication with the same rounding mode.

As for `toModel_add`, the nearest-even call runs the selected `ExecFloat.Mul` capability, whose
reference operation the instance argument fixes to `Configured.Spec.mul`.
-/
@[simp, grind =] theorem toModel_mul
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    toModel (mul left right (mode := mode)) =
      Model.mul (toModel left) (toModel right) (mode := mode) := by
  cases mode
  case nearest =>
    change toModel (ExecFloat.mul left right) = _
    rw [ExecFloat.Proof.mul_eq_spec, ExecFloat.Spec.mul, ExecFloat.Mul.spec,
      ExecFloat.Capability.HasSpec.spec_eq (cap := cap) (spec := Configured.Spec.mul)]
    simp [Configured.Spec.mul, toModel, Configured.Family.toModel, Model.Proof.mul_eq_spec]
  all_goals simp [mul, toModel, Configured.Family.toModel]

/--
Decoding configured division gives model division with the same rounding mode.

As for `toModel_add`, the nearest-even call runs the selected `ExecFloat.Div` capability, whose
reference operation the instance argument fixes to `Configured.Spec.div`.
-/
@[simp, grind =] theorem toModel_div
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    toModel (div left right (mode := mode)) =
      Model.div (toModel left) (toModel right) (mode := mode) := by
  cases mode
  case nearest =>
    change toModel (ExecFloat.div left right) = _
    rw [ExecFloat.Proof.div_eq_spec, ExecFloat.Spec.div, ExecFloat.Div.spec,
      ExecFloat.Capability.HasSpec.spec_eq (cap := cap) (spec := Configured.Spec.div)]
    simp [Configured.Spec.div, toModel, Configured.Family.toModel, Model.Proof.div_eq_spec]
  all_goals simp [div, toModel, Configured.Family.toModel]

/--
Decoding configured FMA gives model FMA with the same rounding mode.

As for `toModel_add`, the nearest-even call runs the selected `ExecFloat.Fma` capability, whose
reference operation the instance argument fixes to `Configured.Spec.fma`.
-/
@[simp, grind =] theorem toModel_fma
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (left right addend : Value) (mode : Model.IEEERoundingMode) :
    toModel (fma left right addend (mode := mode)) =
      Model.fma (toModel left) (toModel right) (toModel addend) (mode := mode) := by
  cases mode
  case nearest =>
    change toModel (ExecFloat.fma left right addend) = _
    rw [ExecFloat.Proof.fma_eq_spec, ExecFloat.Spec.fma, ExecFloat.Fma.spec,
      ExecFloat.Capability.HasSpec.spec_eq (cap := cap) (spec := Configured.Spec.fma)]
    simp [Configured.Spec.fma, toModel, Configured.Family.toModel, Model.Proof.fma_eq_spec]
  all_goals simp [fma, toModel, Configured.Family.toModel]

/--
Decoding configured square root gives model square root with the same rounding mode.

As for `toModel_add`, the nearest-even call runs the selected `ExecFloat.Sqrt` capability, whose
reference operation the instance argument fixes to `Configured.Spec.sqrt`.
-/
@[simp, grind =] theorem toModel_sqrt
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (value : Value) (mode : Model.IEEERoundingMode) :
    toModel (sqrt value (mode := mode)) =
      Model.sqrt (toModel value) (mode := mode) := by
  cases mode
  case nearest =>
    change toModel (ExecFloat.sqrt value) = _
    rw [ExecFloat.Proof.sqrt_eq_spec, ExecFloat.Spec.sqrt, ExecFloat.Sqrt.spec,
      ExecFloat.Capability.HasSpec.spec_eq (cap := cap) (spec := Configured.Spec.sqrt)]
    simp [Configured.Spec.sqrt, toModel, Configured.Family.toModel, Model.Proof.sqrt_eq_spec]
  case nearestAway =>
    change toModel (ExecFloat.sqrt value) = Model.sqrt (toModel value)
    rw [ExecFloat.Proof.sqrt_eq_spec, ExecFloat.Spec.sqrt, ExecFloat.Sqrt.spec,
      ExecFloat.Capability.HasSpec.spec_eq (cap := cap) (spec := Configured.Spec.sqrt)]
    simp [Configured.Spec.sqrt, toModel, Configured.Family.toModel, Model.Proof.sqrt_eq_spec]
  all_goals simp [sqrt, toModel, Configured.Family.toModel]

/-! ## Operator notation -/

/--
Decoding a configured sum `left + right` gives nearest-even model addition.

`+` runs the selected `ExecFloat.Add` capability, so, as for `toModel_add`, the theorem asks that
its reference operation be `Configured.Spec.add`, which instance search proves for every
capability the library declares.
-/
@[simp, grind =] theorem toModel_hAdd
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (left right : Value) :
    toModel (left + right) = Model.add (toModel left) (toModel right) :=
  toModel_add left right (mode := .nearest)

/--
Decoding a configured difference `left - right` gives nearest-even model subtraction.

`-` runs the selected `ExecFloat.Sub` capability, whose reference operation the instance argument
fixes to `Configured.Spec.sub`.
-/
@[simp, grind =] theorem toModel_hSub
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (left right : Value) :
    toModel (left - right) = Model.sub (toModel left) (toModel right) :=
  toModel_sub left right (mode := .nearest)

/--
Decoding a configured product `left * right` gives nearest-even model multiplication.

`*` runs the selected `ExecFloat.Mul` capability, whose reference operation the instance argument
fixes to `Configured.Spec.mul`.
-/
@[simp, grind =] theorem toModel_hMul
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (left right : Value) :
    toModel (left * right) = Model.mul (toModel left) (toModel right) :=
  toModel_mul left right (mode := .nearest)

/--
Decoding a configured quotient `left / right` gives nearest-even model division.

`/` runs the selected `ExecFloat.Div` capability, whose reference operation the instance argument
fixes to `Configured.Spec.div`.
-/
@[simp, grind =] theorem toModel_hDiv
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (left right : Value) :
    toModel (left / right) = Model.div (toModel left) (toModel right) :=
  toModel_div left right (mode := .nearest)

/--
Decoding a configured negation `-value` gives model negation.

Negation goes through the storage codec rather than a selected capability, so
the theorem has no instance argument.
-/
@[simp, grind =] theorem toModel_neg (value : Value) :
    toModel (-value) = Model.neg (toModel value) :=
  ExecFloat.ModelCodec.decode_liftUnary (Model := Model format) (plan := plan) Model.neg value

/--
Decoding the generic square root `ExecFloat.sqrt value` gives nearest-even model square root.

`value.sqrt` on a configured value is `ExecFloat.Binary.sqrt`, covered by `toModel_sqrt`. This
theorem covers the format-generic call, which runs the selected `ExecFloat.Sqrt` capability with
reference operation `Configured.Spec.sqrt`.
-/
@[simp, grind =] theorem toModel_execFloat_sqrt
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (value : Value) :
    toModel (ExecFloat.sqrt (F := Configured.Family format code plan) value) =
      Model.sqrt (toModel value) :=
  toModel_sqrt value (mode := .nearest)

/-- Decoding configured addition preserves the model result, flags, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_add
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Add (Configured.Family format code plan)]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (add left right (mode := mode) (status := true)) =
      Model.add (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) (mode := mode)
        (status := true) := by
  simp [add]

/-- Decoding configured subtraction preserves the model result, flags, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_sub
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Sub (Configured.Family format code plan)]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (sub left right (mode := mode) (status := true)) =
      Model.sub (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) (mode := mode)
        (status := true) := by
  simp [sub]

/-- Decoding configured multiplication preserves the model result, flags, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_mul
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Mul (Configured.Family format code plan)]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (mul left right (mode := mode) (status := true)) =
      Model.mul (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) (mode := mode)
        (status := true) := by
  simp [mul]

/-- Decoding configured division preserves the model result, flags, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_div
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Div (Configured.Family format code plan)]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (div left right (mode := mode) (status := true)) =
      Model.div (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) (mode := mode)
        (status := true) := by
  simp [div]

/-- Decoding configured FMA preserves the model result, flags, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_fma
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Fma (Configured.Family format code plan)]
    (left right addend : Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (fma left right addend (mode := mode) (status := true)) =
      Model.fma (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
        (ExecFloat.Binary.toModel addend) (mode := mode) (status := true) := by
  simp [fma]

/-- Decoding configured square root preserves the model result, flags, and ternary value. -/
@[simp, grind =] theorem IEEEOutcome.toModel_sqrt
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [ExecFloat.Sqrt (Configured.Family format code plan)]
    (value : Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (sqrt value (mode := mode) (status := true)) =
      Model.sqrt (ExecFloat.Binary.toModel value) (mode := mode)
        (status := true) := by
  simp [sqrt]

/--
Configured addition with `status := true` delivers the value of configured addition.

Like `toModel_add`, it takes the instance argument `HasSpec cap Configured.Spec.add`, which
instance search proves for every capability the library declares.
-/
@[simp] theorem value_add
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    (add left right (mode := mode) (status := true)).value = add left right (mode := mode) := by
  rw [← ofModel_toModel (add left right (mode := mode)), toModel_add, ← Model.value_add]
  rfl

/--
Configured subtraction with `status := true` delivers the value of configured subtraction.

Like `toModel_sub`, it takes the instance argument `HasSpec cap Configured.Spec.sub`.
-/
@[simp] theorem value_sub
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Sub (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sub]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    (sub left right (mode := mode) (status := true)).value = sub left right (mode := mode) := by
  rw [← ofModel_toModel (sub left right (mode := mode)), toModel_sub, ← Model.value_sub]
  rfl

/--
Configured multiplication with `status := true` delivers the value of configured multiplication.

Like `toModel_mul`, it takes the instance argument `HasSpec cap Configured.Spec.mul`.
-/
@[simp] theorem value_mul
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Mul (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.mul]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    (mul left right (mode := mode) (status := true)).value = mul left right (mode := mode) := by
  rw [← ofModel_toModel (mul left right (mode := mode)), toModel_mul, ← Model.value_mul]
  rfl

/--
Configured division with `status := true` delivers the value of configured division.

Like `toModel_div`, it takes the instance argument `HasSpec cap Configured.Spec.div`.
-/
@[simp] theorem value_div
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Div (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.div]
    (left right : Value) (mode : Model.IEEERoundingMode) :
    (div left right (mode := mode) (status := true)).value = div left right (mode := mode) := by
  rw [← ofModel_toModel (div left right (mode := mode)), toModel_div, ← Model.value_div]
  rfl

/--
Configured FMA with `status := true` delivers the value of configured FMA.

Like `toModel_fma`, it takes the instance argument `HasSpec cap Configured.Spec.fma`.
-/
@[simp] theorem value_fma
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Fma (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.fma]
    (left right addend : Value) (mode : Model.IEEERoundingMode) :
    (fma left right addend (mode := mode) (status := true)).value =
      fma left right addend (mode := mode) := by
  rw [← ofModel_toModel (fma left right addend (mode := mode)), toModel_fma, ← Model.value_fma]
  rfl

/--
Configured square root with `status := true` delivers the value of configured square root.

Like `toModel_sqrt`, it takes the instance argument `HasSpec cap Configured.Spec.sqrt`.
-/
@[simp] theorem value_sqrt
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Sqrt (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.sqrt]
    (value : Value) (mode : Model.IEEERoundingMode) :
    (sqrt value (mode := mode) (status := true)).value = sqrt value (mode := mode) := by
  rw [← ofModel_toModel (sqrt value (mode := mode)), toModel_sqrt, ← Model.value_sqrt]
  rfl

end FloatLib.Floats.ExecFloat.Binary
