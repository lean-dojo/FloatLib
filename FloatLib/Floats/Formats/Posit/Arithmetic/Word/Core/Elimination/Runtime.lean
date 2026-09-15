/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Fields.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Fields.Runtime

/-!
# Posit scalar-field elimination

These continuation interfaces eliminate one, two, or three packed posit words into exact scalar
dyadic fields without allocating decoded input records. Their semantic refinement theorems live
in `FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Elimination.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWord

/-- Eliminate a stored posit word into exact scalar dyadic fields. -/
@[inline] def withDyadicFields {α : Type}
    (format : Format) (code : UInt64) (onNaR : α)
    (continuation : Bool → Nat → Int → α) : α :=
  if code.toNat == format.signMaskNat then
    onNaR
  else if code == 0 then
    continuation false 0 0
  else
    let negative := decide (format.signMaskNat ≤ code.toNat)
    let magnitude := UInt64.ofNat (magnitudeNat format code)
    withNonnegativeFields format magnitude fun significand exponent =>
      continuation negative significand exponent

/-- Eliminate one stored posit word using prepared native layout constants. -/
@[inline] def withDyadicWordFieldsAt {α : Type}
    (payloadBits : Nat) (signMask modulus code : UInt64)
    (onNaR : α) (continuation : Bool → UInt64 → Int → α) : α :=
  if code == signMask then
    onNaR
  else if code == 0 then
    continuation false 0 0
  else
    let negative := decide (signMask ≤ code)
    let magnitude := magnitudeWordAt signMask modulus code
    withNonnegativeWordFieldsAtPayload payloadBits magnitude
      fun significand exponent =>
      continuation negative significand exponent

/-- Eliminate a proved-valid stored word into native-word dyadic fields. -/
@[inline] def withDyadicWordFieldsValid {α : Type}
    (format : Format) (_heligible : Eligible format)
    (code : UInt64) (_hcode : code.toNat < format.modulus)
    (onNaR : α) (continuation : Bool → UInt64 → Int → α) : α :=
  withDyadicWordFieldsAt format.payloadBits
    (signMaskWord format) (modulusWord format) code onNaR continuation

/-- Natural-number view of `withDyadicWordFieldsValid`. -/
@[inline] def withDyadicFieldsValid {α : Type}
    (format : Format) (heligible : Eligible format)
    (code : UInt64) (hcode : code.toNat < format.modulus)
    (onNaR : α) (continuation : Bool → Nat → Int → α) : α :=
  withDyadicWordFieldsValid format heligible code hcode onNaR
    fun negative significand exponent =>
      continuation negative significand.toNat exponent

/-- Eliminate two stored posit words into scalar exact-dyadic fields. -/
@[inline] def withTwoDyadicFields {α : Type}
    (format : Format) (left right : UInt64) (onNaR : α)
    (continuation :
      Bool → Nat → Int → Bool → Nat → Int → α) : α :=
  withDyadicFields format left onNaR
    fun leftNegative leftSignificand leftExponent =>
      withDyadicFields format right onNaR
        fun rightNegative rightSignificand rightExponent =>
          continuation leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent

/-- Native-valid two-word scalar elimination. Proposition arguments erase at runtime. -/
@[inline] def withTwoDyadicWordFieldsValid {α : Type}
    (format : Format) (_heligible : Eligible format)
    (left : UInt64) (_hleft : left.toNat < format.modulus)
    (right : UInt64) (_hright : right.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → UInt64 → Int → Bool → UInt64 → Int → α) : α :=
  let payloadBits := format.payloadBits
  let signMask := signMaskWord format
  let modulus := signMask + signMask
  withDyadicWordFieldsAt payloadBits signMask modulus left onNaR
    fun leftNegative leftSignificand leftExponent =>
      withDyadicWordFieldsAt payloadBits signMask modulus right onNaR
        fun rightNegative rightSignificand rightExponent =>
          continuation leftNegative leftSignificand leftExponent
            rightNegative rightSignificand rightExponent

/-- Native-valid two-word exact-field elimination. -/
@[inline] def withTwoDyadicFieldsValid {α : Type}
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → Nat → Int → Bool → Nat → Int → α) : α :=
  withTwoDyadicWordFieldsValid format heligible
      left hleft right hright onNaR
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent =>
      continuation leftNegative leftSignificand.toNat leftExponent
        rightNegative rightSignificand.toNat rightExponent

/-- Eliminate three stored posit words into scalar exact-dyadic fields. -/
@[inline] def withThreeDyadicFields {α : Type}
    (format : Format) (left right addend : UInt64) (onNaR : α)
    (continuation :
      Bool → Nat → Int →
      Bool → Nat → Int →
      Bool → Nat → Int → α) : α :=
  withDyadicFields format left onNaR
    fun leftNegative leftSignificand leftExponent =>
      withDyadicFields format right onNaR
        fun rightNegative rightSignificand rightExponent =>
          withDyadicFields format addend onNaR
            fun addendNegative addendSignificand addendExponent =>
              continuation leftNegative leftSignificand leftExponent
                rightNegative rightSignificand rightExponent
                addendNegative addendSignificand addendExponent

/-- Native-valid three-word scalar elimination. Proposition arguments erase at runtime. -/
@[inline] def withThreeDyadicWordFieldsValid {α : Type}
    (format : Format) (_heligible : Eligible format)
    (left : UInt64) (_hleft : left.toNat < format.modulus)
    (right : UInt64) (_hright : right.toNat < format.modulus)
    (addend : UInt64) (_haddend : addend.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → UInt64 → Int →
      Bool → UInt64 → Int →
      Bool → UInt64 → Int → α) : α :=
  let payloadBits := format.payloadBits
  let signMask := signMaskWord format
  let modulus := signMask + signMask
  withDyadicWordFieldsAt payloadBits signMask modulus left onNaR
    fun leftNegative leftSignificand leftExponent =>
      withDyadicWordFieldsAt payloadBits signMask modulus right onNaR
        fun rightNegative rightSignificand rightExponent =>
          withDyadicWordFieldsAt payloadBits signMask modulus addend onNaR
            fun addendNegative addendSignificand addendExponent =>
              continuation leftNegative leftSignificand leftExponent
                rightNegative rightSignificand rightExponent
                addendNegative addendSignificand addendExponent

/-- Native-valid three-word exact-field elimination. -/
@[inline] def withThreeDyadicFieldsValid {α : Type}
    (format : Format) (heligible : Eligible format)
    (left : UInt64) (hleft : left.toNat < format.modulus)
    (right : UInt64) (hright : right.toNat < format.modulus)
    (addend : UInt64) (haddend : addend.toNat < format.modulus)
    (onNaR : α)
    (continuation :
      Bool → Nat → Int →
      Bool → Nat → Int →
      Bool → Nat → Int → α) : α :=
  withThreeDyadicWordFieldsValid format heligible
      left hleft right hright addend haddend onNaR
    fun leftNegative leftSignificand leftExponent
        rightNegative rightSignificand rightExponent
        addendNegative addendSignificand addendExponent =>
      continuation leftNegative leftSignificand.toNat leftExponent
        rightNegative rightSignificand.toNat rightExponent
        addendNegative addendSignificand.toNat addendExponent

end FloatLib.Floats.Formats.Posit.Model.NativeWord
