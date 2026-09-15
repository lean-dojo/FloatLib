/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Carrier
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Common

/-!
# Shared fixed-word posit kernels

The public `UInt8`, `UInt16`, `UInt32`, and `UInt64` entry points are thin monomorphic wrappers
around these always-inlined definitions. Arithmetic is performed by the same proved packed
`UInt64` kernels for every carrier; only widening and narrowing vary.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords

variable {α : Type} {capacity : Nat}

/-- Widening an in-range carrier word to `UInt64` keeps it below the posit modulus. -/
theorem widened_lt_modulus
    (carrier : Carrier α capacity)
    {format : Format} {value : α}
    (hvalue : carrier.toNat value < format.modulus) :
    (carrier.toUInt64 value).toNat < format.modulus := by
  rw [carrier.toNat_toUInt64]
  exact hvalue

/-! ## Always-inlined raw kernels -/

/-- Carrier-generic packed addition. -/
@[always_inline] def addRaw
    (carrier : Carrier α capacity)
    (format : Format) (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) : α :=
  let eligible : Model.NativeWord.Eligible format :=
    le_trans width_le carrier.capacity_le
  carrier.narrow <|
    Model.NativeWordArithmetic.PackedSignedSum.addWordsCodeWordValid
      eligible (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright)

/-- Carrier-generic packed subtraction. -/
@[always_inline] def subRaw
    (carrier : Carrier α capacity)
    (format : Format) (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) : α :=
  let eligible : Model.NativeWord.Eligible format :=
    le_trans width_le carrier.capacity_le
  carrier.narrow <|
    Model.NativeWordArithmetic.PackedSignedSum.subWordsCodeWordValid
      eligible (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright)

/-- Carrier-generic packed multiplication. -/
@[always_inline] def mulRaw
    (carrier : Carrier α capacity)
    (format : Format) (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) : α :=
  let eligible : Model.NativeWord.Eligible format :=
    le_trans width_le carrier.capacity_le
  carrier.narrow <|
    Model.NativeWordArithmetic.PackedProduct.mulWordsCodeWordValid
      eligible (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright)

/-- Carrier-generic packed division. -/
@[always_inline] def divRaw
    (carrier : Carrier α capacity)
    (format : Format) (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) : α :=
  let eligible : Model.NativeWord.Eligible format :=
    le_trans width_le carrier.capacity_le
  carrier.narrow <|
    Model.NativeWordArithmetic.PackedQuotient.divWordsCodeWordValid
      eligible (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright)

/-- Carrier-generic packed square root. -/
@[always_inline] def sqrtRaw
    (carrier : Carrier α capacity)
    (format : Format) (width_le : format.bits ≤ capacity)
    (value : α)
    (hvalue : carrier.toNat value < format.modulus) : α :=
  let eligible : Model.NativeWord.Eligible format :=
    le_trans width_le carrier.capacity_le
  carrier.narrow <|
    Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeWordValid
      eligible (carrier.toUInt64 value)
      (widened_lt_modulus carrier hvalue)

/-- Carrier-generic packed fused multiply-add. -/
@[always_inline] def fmaRaw
    (carrier : Carrier α capacity)
    (format : Format) (width_le : format.bits ≤ capacity)
    (left right addend : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus)
    (haddend : carrier.toNat addend < format.modulus) : α :=
  let eligible : Model.NativeWord.Eligible format :=
    le_trans width_le carrier.capacity_le
  carrier.narrow <|
    Model.NativeWordArithmetic.PackedSignedSum.fmaWordsCodeWordValid
      eligible
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (carrier.toUInt64 addend)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright)
      (widened_lt_modulus carrier haddend)

/-! ## Shared range certificates -/

/-- Raw addition of in-range words returns a word below the posit modulus. -/
theorem addRaw_lt_modulus
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) :
    carrier.toNat (addRaw carrier format width_le left right hleft hright) <
      format.modulus := by
  unfold addRaw
  exact observed_lt_modulus width_le (carrier.toNat_narrow _)
    (packedAdd_lt_modulus (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright))

/-- Raw subtraction of in-range words returns a word below the posit modulus. -/
theorem subRaw_lt_modulus
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) :
    carrier.toNat (subRaw carrier format width_le left right hleft hright) <
      format.modulus := by
  unfold subRaw
  exact observed_lt_modulus width_le (carrier.toNat_narrow _)
    (packedSub_lt_modulus (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright))

/-- Raw multiplication of in-range words returns a word below the posit modulus. -/
theorem mulRaw_lt_modulus
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) :
    carrier.toNat (mulRaw carrier format width_le left right hleft hright) <
      format.modulus := by
  unfold mulRaw
  exact observed_lt_modulus width_le (carrier.toNat_narrow _)
    (packedMul_lt_modulus (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright))

/-- Raw division of in-range words returns a word below the posit modulus. -/
theorem divRaw_lt_modulus
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) :
    carrier.toNat (divRaw carrier format width_le left right hleft hright) <
      format.modulus := by
  unfold divRaw
  exact observed_lt_modulus width_le (carrier.toNat_narrow _)
    (packedDiv_lt_modulus (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright))

/-- The raw square root of an in-range word is below the posit modulus. -/
theorem sqrtRaw_lt_modulus
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (value : α)
    (hvalue : carrier.toNat value < format.modulus) :
    carrier.toNat (sqrtRaw carrier format width_le value hvalue) <
      format.modulus := by
  unfold sqrtRaw
  exact observed_lt_modulus width_le (carrier.toNat_narrow _)
    (packedSqrt_lt_modulus (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 value)
      (widened_lt_modulus carrier hvalue))

/-- Raw fused multiply-add of in-range words returns a word below the posit modulus. -/
theorem fmaRaw_lt_modulus
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right addend : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus)
    (haddend : carrier.toNat addend < format.modulus) :
    carrier.toNat
        (fmaRaw carrier format width_le left right addend
          hleft hright haddend) <
      format.modulus := by
  unfold fmaRaw
  exact observed_lt_modulus width_le (carrier.toNat_narrow _)
    (packedFma_lt_modulus (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (carrier.toUInt64 addend)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright)
      (widened_lt_modulus carrier haddend))

/-! ## Shared observations used by semantic refinement -/

/--
Two range-checked carrier values are equal when their natural-number observations agree.

The width hypothesis is used only to construct the right-hand range certificate. This theorem is
proof-only and does not change the monomorphic fixed-word runtime boundary.
-/
theorem validCode_eq_of_toNat_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (value : α) (hvalue : carrier.toNat value < format.modulus)
    (result : Nat) (result_lt : result < format.modulus)
    (value_eq : carrier.toNat value = carrier.toNat (carrier.ofNat result)) :
    (⟨value, hvalue⟩ :
      { bits : α // carrier.toNat bits < format.modulus }) =
      ⟨carrier.ofNat result,
        observed_lt_modulus width_le (carrier.toNat_ofNat result) result_lt⟩ := by
  apply Subtype.ext
  exact carrier.toNat_injective value_eq

/-- Raw fixed-carrier addition and configured native packing produce the same code. -/
theorem addRaw_toNat_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) :
    carrier.toNat (addRaw carrier format width_le left right hleft hright) =
      carrier.toNat (carrier.ofNat
        (Model.NativeWordArithmetic.addWordsCodeFlatValid
          (le_trans width_le carrier.capacity_le)
          (carrier.toUInt64 left) (carrier.toUInt64 right)
          (widened_lt_modulus carrier hleft)
          (widened_lt_modulus carrier hright))) := by
  unfold addRaw
  rw [carrier.toNat_narrow, carrier.toNat_ofNat]
  exact congrArg (fun result : Nat => result % 2 ^ capacity)
    (Model.NativeWordArithmetic.PackedSignedSum.addWordsCodeWordValid_toNat
      (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright))

/-- Raw fixed-carrier subtraction and configured native packing produce the same code. -/
theorem subRaw_toNat_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) :
    carrier.toNat (subRaw carrier format width_le left right hleft hright) =
      carrier.toNat (carrier.ofNat
        (Model.NativeWordArithmetic.subWordsCodeFlatValid
          (le_trans width_le carrier.capacity_le)
          (carrier.toUInt64 left) (carrier.toUInt64 right)
          (widened_lt_modulus carrier hleft)
          (widened_lt_modulus carrier hright))) := by
  unfold subRaw
  rw [carrier.toNat_narrow, carrier.toNat_ofNat]
  exact congrArg (fun result : Nat => result % 2 ^ capacity)
    (Model.NativeWordArithmetic.PackedSignedSum.subWordsCodeWordValid_toNat
      (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright))

/-- Raw fixed-carrier multiplication and configured native packing produce the same code. -/
theorem mulRaw_toNat_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) :
    carrier.toNat (mulRaw carrier format width_le left right hleft hright) =
      carrier.toNat (carrier.ofNat
        (Model.NativeWordArithmetic.PackedProduct.mulWordsCodeValid
          (le_trans width_le carrier.capacity_le)
          (carrier.toUInt64 left) (carrier.toUInt64 right)
          (widened_lt_modulus carrier hleft)
          (widened_lt_modulus carrier hright))) := by
  unfold mulRaw
  rw [carrier.toNat_narrow, carrier.toNat_ofNat]
  exact congrArg (fun result : Nat => result % 2 ^ capacity)
    (Model.NativeWordArithmetic.PackedProduct.mulWordsCodeWordValid_toNat
      (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright))

/-- Raw fixed-carrier division and configured native packing produce the same code. -/
theorem divRaw_toNat_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus) :
    carrier.toNat (divRaw carrier format width_le left right hleft hright) =
      carrier.toNat (carrier.ofNat
        (Model.NativeWordArithmetic.PackedQuotient.divWordsCodeValid
          (le_trans width_le carrier.capacity_le)
          (carrier.toUInt64 left) (carrier.toUInt64 right)
          (widened_lt_modulus carrier hleft)
          (widened_lt_modulus carrier hright))) := by
  unfold divRaw
  rw [carrier.toNat_narrow, carrier.toNat_ofNat]
  exact congrArg (fun result : Nat => result % 2 ^ capacity)
    (Model.NativeWordArithmetic.PackedQuotient.divWordsCodeWordValid_toNat
      (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright))

/-- Raw fixed-carrier square root and configured native packing produce the same code. -/
theorem sqrtRaw_toNat_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (value : α)
    (hvalue : carrier.toNat value < format.modulus) :
    carrier.toNat (sqrtRaw carrier format width_le value hvalue) =
      carrier.toNat (carrier.ofNat
        (Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeValid
          (le_trans width_le carrier.capacity_le)
          (carrier.toUInt64 value)
          (widened_lt_modulus carrier hvalue))) := by
  unfold sqrtRaw
  rw [carrier.toNat_narrow, carrier.toNat_ofNat]
  exact congrArg (fun result : Nat => result % 2 ^ capacity)
    (Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeWordValid_toNat
      (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 value)
      (widened_lt_modulus carrier hvalue))

/-- Raw fixed-carrier FMA and configured native packing produce the same code. -/
theorem fmaRaw_toNat_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right addend : α)
    (hleft : carrier.toNat left < format.modulus)
    (hright : carrier.toNat right < format.modulus)
    (haddend : carrier.toNat addend < format.modulus) :
    carrier.toNat
        (fmaRaw carrier format width_le left right addend
          hleft hright haddend) =
      carrier.toNat (carrier.ofNat
        (Model.NativeWordArithmetic.fmaWordsCodeFlatValid
          (le_trans width_le carrier.capacity_le)
          (carrier.toUInt64 left) (carrier.toUInt64 right)
          (carrier.toUInt64 addend)
          (widened_lt_modulus carrier hleft)
          (widened_lt_modulus carrier hright)
          (widened_lt_modulus carrier haddend))) := by
  unfold fmaRaw
  rw [carrier.toNat_narrow, carrier.toNat_ofNat]
  exact congrArg (fun result : Nat => result % 2 ^ capacity)
    (Model.NativeWordArithmetic.PackedSignedSum.fmaWordsCodeWordValid_toNat
      (le_trans width_le carrier.capacity_le)
      (carrier.toUInt64 left) (carrier.toUInt64 right)
      (carrier.toUInt64 addend)
      (widened_lt_modulus carrier hleft)
      (widened_lt_modulus carrier hright)
      (widened_lt_modulus carrier haddend))

/-! ## Range-checked carrier equalities -/

/--
Fixed-carrier addition returns the same range-checked code as exact native-word packing.
-/
theorem addCode_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right :
      { bits : α // carrier.toNat bits < format.modulus }) :
    (⟨addRaw carrier format width_le left.1 right.1 left.2 right.2,
        addRaw_lt_modulus carrier width_le
          left.1 right.1 left.2 right.2⟩ :
      { bits : α // carrier.toNat bits < format.modulus }) =
      ⟨carrier.ofNat
          (Model.NativeWordArithmetic.addWordsCodeFlatValid
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2)),
        observed_lt_modulus width_le
          (carrier.toNat_ofNat _)
          (Model.NativeWordArithmetic.addWordsCodeFlatValid_lt_modulus
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2))⟩ := by
  apply validCode_eq_of_toNat_eq carrier width_le
  exact Model.NativeWordArithmetic.addWordsCodeFlatValid_lt_modulus
    (le_trans width_le carrier.capacity_le)
    (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
    (widened_lt_modulus carrier left.2)
    (widened_lt_modulus carrier right.2)
  exact addRaw_toNat_eq carrier width_le
    left.1 right.1 left.2 right.2

/-- Fixed-carrier subtraction returns the same code as exact native-word packing. -/
theorem subCode_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right :
      { bits : α // carrier.toNat bits < format.modulus }) :
    (⟨subRaw carrier format width_le left.1 right.1 left.2 right.2,
        subRaw_lt_modulus carrier width_le
          left.1 right.1 left.2 right.2⟩ :
      { bits : α // carrier.toNat bits < format.modulus }) =
      ⟨carrier.ofNat
          (Model.NativeWordArithmetic.subWordsCodeFlatValid
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2)),
        observed_lt_modulus width_le
          (carrier.toNat_ofNat _)
          (Model.NativeWordArithmetic.subWordsCodeFlatValid_lt_modulus
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2))⟩ := by
  apply validCode_eq_of_toNat_eq carrier width_le
  exact Model.NativeWordArithmetic.subWordsCodeFlatValid_lt_modulus
    (le_trans width_le carrier.capacity_le)
    (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
    (widened_lt_modulus carrier left.2)
    (widened_lt_modulus carrier right.2)
  exact subRaw_toNat_eq carrier width_le
    left.1 right.1 left.2 right.2

/-- Fixed-carrier multiplication returns the same code as exact native-word packing. -/
theorem mulCode_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right :
      { bits : α // carrier.toNat bits < format.modulus }) :
    (⟨mulRaw carrier format width_le left.1 right.1 left.2 right.2,
        mulRaw_lt_modulus carrier width_le
          left.1 right.1 left.2 right.2⟩ :
      { bits : α // carrier.toNat bits < format.modulus }) =
      ⟨carrier.ofNat
          (Model.NativeWordArithmetic.PackedProduct.mulWordsCodeValid
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2)),
        observed_lt_modulus width_le
          (carrier.toNat_ofNat _)
          (Model.NativeWordArithmetic.PackedProduct.mulWordsCodeValid_lt_modulus
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2))⟩ := by
  apply validCode_eq_of_toNat_eq carrier width_le
  exact Model.NativeWordArithmetic.PackedProduct.mulWordsCodeValid_lt_modulus
    (le_trans width_le carrier.capacity_le)
    (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
    (widened_lt_modulus carrier left.2)
    (widened_lt_modulus carrier right.2)
  exact mulRaw_toNat_eq carrier width_le
    left.1 right.1 left.2 right.2

/-- Fixed-carrier division returns the same code as exact native-word packing. -/
theorem divCode_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right :
      { bits : α // carrier.toNat bits < format.modulus }) :
    (⟨divRaw carrier format width_le left.1 right.1 left.2 right.2,
        divRaw_lt_modulus carrier width_le
          left.1 right.1 left.2 right.2⟩ :
      { bits : α // carrier.toNat bits < format.modulus }) =
      ⟨carrier.ofNat
          (Model.NativeWordArithmetic.PackedQuotient.divWordsCodeValid
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2)),
        observed_lt_modulus width_le
          (carrier.toNat_ofNat _)
          (Model.NativeWordArithmetic.PackedQuotient.divWordsCodeValid_lt_modulus
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2))⟩ := by
  apply validCode_eq_of_toNat_eq carrier width_le
  exact Model.NativeWordArithmetic.PackedQuotient.divWordsCodeValid_lt_modulus
    (le_trans width_le carrier.capacity_le)
    (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
    (widened_lt_modulus carrier left.2)
    (widened_lt_modulus carrier right.2)
  exact divRaw_toNat_eq carrier width_le
    left.1 right.1 left.2 right.2

/-- Fixed-carrier square root returns the same code as exact native-word packing. -/
theorem sqrtCode_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (value : { bits : α // carrier.toNat bits < format.modulus }) :
    (⟨sqrtRaw carrier format width_le value.1 value.2,
        sqrtRaw_lt_modulus carrier width_le value.1 value.2⟩ :
      { bits : α // carrier.toNat bits < format.modulus }) =
      ⟨carrier.ofNat
          (Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeValid
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 value.1)
            (widened_lt_modulus carrier value.2)),
        observed_lt_modulus width_le
          (carrier.toNat_ofNat _)
          (Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeValid_lt_modulus
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 value.1)
            (widened_lt_modulus carrier value.2))⟩ := by
  apply validCode_eq_of_toNat_eq carrier width_le
  exact Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeValid_lt_modulus
    (le_trans width_le carrier.capacity_le)
    (carrier.toUInt64 value.1)
    (widened_lt_modulus carrier value.2)
  exact sqrtRaw_toNat_eq carrier width_le value.1 value.2

/-- Fixed-carrier FMA returns the same code as exact native-word packing. -/
theorem fmaCode_eq
    (carrier : Carrier α capacity)
    {format : Format} (width_le : format.bits ≤ capacity)
    (left right addend :
      { bits : α // carrier.toNat bits < format.modulus }) :
    (⟨fmaRaw carrier format width_le
          left.1 right.1 addend.1 left.2 right.2 addend.2,
        fmaRaw_lt_modulus carrier width_le
          left.1 right.1 addend.1 left.2 right.2 addend.2⟩ :
      { bits : α // carrier.toNat bits < format.modulus }) =
      ⟨carrier.ofNat
          (Model.NativeWordArithmetic.fmaWordsCodeFlatValid
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (carrier.toUInt64 addend.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2)
            (widened_lt_modulus carrier addend.2)),
        observed_lt_modulus width_le
          (carrier.toNat_ofNat _)
          (Model.NativeWordArithmetic.fmaWordsCodeFlatValid_lt_modulus
            (le_trans width_le carrier.capacity_le)
            (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
            (carrier.toUInt64 addend.1)
            (widened_lt_modulus carrier left.2)
            (widened_lt_modulus carrier right.2)
            (widened_lt_modulus carrier addend.2))⟩ := by
  apply validCode_eq_of_toNat_eq carrier width_le
  exact Model.NativeWordArithmetic.fmaWordsCodeFlatValid_lt_modulus
    (le_trans width_le carrier.capacity_le)
    (carrier.toUInt64 left.1) (carrier.toUInt64 right.1)
    (carrier.toUInt64 addend.1)
    (widened_lt_modulus carrier left.2)
    (widened_lt_modulus carrier right.2)
    (widened_lt_modulus carrier addend.2)
  exact fmaRaw_toNat_eq carrier width_le
    left.1 right.1 addend.1 left.2 right.2 addend.2

end FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords
