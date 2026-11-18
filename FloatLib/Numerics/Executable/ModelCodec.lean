/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Carrier

/-!
# Lossless transport between executable carriers and proof models

`ModelCodec` gives inverse encoding and decoding maps for an arbitrary static plan.
The lift equations transport unary, binary, and ternary operations through those maps.
No radix, exceptional-value policy, or arithmetic semantics is assumed.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat

open FloatLib.Numerics

universe u v w

/--
Lossless conversion between a runtime carrier and its proof model.

`plan` is an arbitrary static index used only to distinguish carrier choices during typeclass
search. Nothing in the contract depends on radix, encoding, exceptional values or arithmetic
semantics. Format families therefore share these inverse laws while keeping their storage plans
and model types separate.
-/
class ModelCodec {Plan : Type u} (plan : Plan)
    (Model : Type v) (Code : outParam (Type w)) where
  /-- Decode one runtime code into the proof model. -/
  toModel : Code → Model
  /-- Pack one proof-model value into the runtime carrier. -/
  ofModel : Model → Code
  /-- Decoding after packing returns the model value. -/
  toModel_ofModel : ∀ value, toModel (ofModel value) = value
  /-- Packing after decoding preserves the runtime code. -/
  ofModel_toModel : ∀ value, ofModel (toModel value) = value

variable {F : Type u} [EncodedFormat F]

namespace ModelCodec

variable {Plan : Type v} {plan : Plan} {Model : Type w}
    [codec : ModelCodec plan Model (FormatCode F)]

/-- Decode an executable value through its lossless proof-model codec. -/
@[always_inline, inline] def decode (value : ExecFloat F) : Model :=
  codec.toModel value.raw

/-- Encode a proof-model value through its lossless runtime codec. -/
@[always_inline, inline] def encode (value : Model) : ExecFloat F :=
  ofRaw (codec.ofModel value)

/-- Lift a unary proof-model operation to the executable carrier. -/
@[always_inline, inline] def liftUnary
    (operation : Model → Model) (value : ExecFloat F) : ExecFloat F :=
  encode (Model := Model) (plan := plan)
    (operation (decode (Model := Model) (plan := plan) value))

/-- Lift a binary proof-model operation to the executable carrier. -/
@[always_inline, inline] def liftBinary
    (operation : Model → Model → Model)
    (left right : ExecFloat F) : ExecFloat F :=
  encode (Model := Model) (plan := plan)
    (operation
      (decode (Model := Model) (plan := plan) left)
      (decode (Model := Model) (plan := plan) right))

/-- Lift a ternary proof-model operation to the executable carrier. -/
@[always_inline, inline] def liftTernary
    (operation : Model → Model → Model → Model)
    (left right third : ExecFloat F) : ExecFloat F :=
  encode (Model := Model) (plan := plan)
    (operation
      (decode (Model := Model) (plan := plan) left)
      (decode (Model := Model) (plan := plan) right)
      (decode (Model := Model) (plan := plan) third))

/-- Decoding immediately after encoding recovers the proof-model value. -/
@[simp, grind =] theorem decode_encode (value : Model) :
    decode (Model := Model) (plan := plan)
      (encode (F := F) (Model := Model) (plan := plan) value) = value :=
  codec.toModel_ofModel value

/-- Encoding immediately after decoding recovers the executable value. -/
@[simp, grind =] theorem encode_decode (value : ExecFloat F) :
    encode (Model := Model) (plan := plan)
      (decode (Model := Model) (plan := plan) value) = value := by
  apply ExecFloat.ext
  exact codec.ofModel_toModel value.raw

/-- Decoding a lifted unary operation exposes the underlying proof-model operation. -/
@[simp, grind =] theorem decode_liftUnary
    (operation : Model → Model) (value : ExecFloat F) :
    decode (Model := Model) (plan := plan)
        (liftUnary (Model := Model) (plan := plan) operation value) =
      operation (decode (Model := Model) (plan := plan) value) := by
  simp only [liftUnary, decode_encode]

/-- Decoding a lifted binary operation exposes the underlying proof-model operation. -/
@[simp, grind =] theorem decode_liftBinary
    (operation : Model → Model → Model) (left right : ExecFloat F) :
    decode (Model := Model) (plan := plan)
        (liftBinary (Model := Model) (plan := plan) operation left right) =
      operation
        (decode (Model := Model) (plan := plan) left)
        (decode (Model := Model) (plan := plan) right) := by
  simp only [liftBinary, decode_encode]

/-- Decoding a lifted ternary operation exposes the underlying proof-model operation. -/
@[simp, grind =] theorem decode_liftTernary
    (operation : Model → Model → Model → Model)
    (left right third : ExecFloat F) :
    decode (Model := Model) (plan := plan)
        (liftTernary (Model := Model) (plan := plan) operation left right third) =
      operation
        (decode (Model := Model) (plan := plan) left)
        (decode (Model := Model) (plan := plan) right)
        (decode (Model := Model) (plan := plan) third) := by
  simp only [liftTernary, decode_encode]

/-- Codec decoding is injective because encoding is its inverse. -/
theorem decode_injective {left right : ExecFloat F}
    (equality :
      decode (Model := Model) (plan := plan) left =
        decode (Model := Model) (plan := plan) right) :
    left = right := by
  rw [← encode_decode (Model := Model) (plan := plan) left,
    ← encode_decode (Model := Model) (plan := plan) right, equality]

/--
A unary code operation that commutes with `toModel` is the lift of its model operation.

The executable side stays the code operation, and the model equation is used only in proofs.
-/
theorem applyUnary_eq_lift
    (operation : FormatCode F → FormatCode F)
    (modelOperation : Model → Model)
    (operation_eq : ∀ value,
      codec.toModel (operation value) = modelOperation (codec.toModel value))
    (value : ExecFloat F) :
    applyUnary operation value =
      liftUnary (Model := Model) (plan := plan) modelOperation value := by
  apply decode_injective (Model := Model) (plan := plan)
  rw [decode_liftUnary]
  change
    codec.toModel (operation value.raw) =
      modelOperation (codec.toModel value.raw)
  exact operation_eq value.raw

/--
A binary code operation that commutes with `toModel` is the lift of its model operation.
-/
theorem applyBinary_eq_lift
    (operation : FormatCode F → FormatCode F → FormatCode F)
    (modelOperation : Model → Model → Model)
    (operation_eq : ∀ left right,
      codec.toModel (operation left right) =
        modelOperation (codec.toModel left) (codec.toModel right))
    (left right : ExecFloat F) :
    applyBinary operation left right =
      liftBinary (Model := Model) (plan := plan) modelOperation left right := by
  apply decode_injective (Model := Model) (plan := plan)
  rw [decode_liftBinary]
  change
    codec.toModel (operation left.raw right.raw) =
      modelOperation (codec.toModel left.raw) (codec.toModel right.raw)
  exact operation_eq left.raw right.raw

/--
A ternary code operation that commutes with `toModel` is the lift of its model operation.
-/
theorem applyTernary_eq_lift
    (operation : FormatCode F → FormatCode F → FormatCode F → FormatCode F)
    (modelOperation : Model → Model → Model → Model)
    (operation_eq : ∀ left right third,
      codec.toModel (operation left right third) =
        modelOperation
          (codec.toModel left) (codec.toModel right) (codec.toModel third))
    (left right third : ExecFloat F) :
    applyTernary operation left right third =
      liftTernary (Model := Model) (plan := plan)
        modelOperation left right third := by
  apply decode_injective (Model := Model) (plan := plan)
  rw [decode_liftTernary]
  change
    codec.toModel (operation left.raw right.raw third.raw) =
      modelOperation
        (codec.toModel left.raw) (codec.toModel right.raw) (codec.toModel third.raw)
  exact operation_eq left.raw right.raw third.raw

/-- Pointwise-equal unary model operations have equal executable lifts. -/
theorem liftUnary_congr
    {leftOperation rightOperation : Model → Model}
    (equal : ∀ value, leftOperation value = rightOperation value)
    (value : ExecFloat F) :
    liftUnary (Model := Model) (plan := plan) leftOperation value =
      liftUnary (Model := Model) (plan := plan) rightOperation value := by
  apply decode_injective (Model := Model) (plan := plan)
  simp only [decode_liftUnary]
  exact equal _

/-- Pointwise-equal binary model operations have equal executable lifts. -/
theorem liftBinary_congr
    {leftOperation rightOperation : Model → Model → Model}
    (equal :
      ∀ left right, leftOperation left right = rightOperation left right)
    (left right : ExecFloat F) :
    liftBinary (Model := Model) (plan := plan) leftOperation left right =
      liftBinary (Model := Model) (plan := plan) rightOperation left right := by
  apply decode_injective (Model := Model) (plan := plan)
  simp only [decode_liftBinary]
  exact equal _ _

/-- Pointwise-equal ternary model operations have equal executable lifts. -/
theorem liftTernary_congr
    {leftOperation rightOperation : Model → Model → Model → Model}
    (equal :
      ∀ left right third,
        leftOperation left right third = rightOperation left right third)
    (left right third : ExecFloat F) :
    liftTernary (Model := Model) (plan := plan)
        leftOperation left right third =
      liftTernary (Model := Model) (plan := plan)
        rightOperation left right third := by
  apply decode_injective (Model := Model) (plan := plan)
  simp only [decode_liftTernary]
  exact equal _ _ _

end ModelCodec

end FloatLib.Floats.ExecFloat
