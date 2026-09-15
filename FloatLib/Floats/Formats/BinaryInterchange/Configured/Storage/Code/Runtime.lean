/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Core
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Runtime

/-!
# Runtime packing for configured binary formats

`Code.toModel` and `Code.ofModel` are the single executable conversion pair for every built-in
carrier. Range proofs are erased. The `word16`, `word32`, and `word64` plans use the carrier's
stored range proof to avoid computing powers of two or remainders during decoding.
`Code.Proof` shows that packing and decoding are mutual inverses for every plan.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Numerics
namespace Code

variable {format : FloatFormat} {plan : StoragePlan format}

/--
Interpret a packed runtime code in the exact-width proof model.

The machine-word carriers already carry the proof that their natural-number view is below
`2 ^ format.bitWidth`, so the model word is built with `BitVec.ofNatLT`. Compiled code then
performs no modular reduction and no power computation on the decode path: the conversion is the
unboxing of the word. The byte carrier keeps the canonical `Model.ofNatBits` decoder because the
byte tier executes exhaustive tables, whose proofs are stated in terms of that decoder.
-/
@[always_inline, inline] def toModel : Code plan → Model format :=
  match plan with
  | .byte _ => fun code => Model.ofNatBits code.1.toNat
  | .word16 _ => fun code => Model.ofBits (BitVec.ofNatLT code.1.toNat code.2)
  | .word32 _ => fun code => Model.ofBits (BitVec.ofNatLT code.1.toNat code.2)
  | .word64 _ => fun code => Model.ofBits (BitVec.ofNatLT code.1.toNat code.2)
  | .wide => fun code => code
  | .limbs _ => fun code => Model.WideLimb.toModel code

/-- Pack a proof-model value into the statically selected runtime code. -/
@[always_inline, inline] def ofModel : Model format → Code plan :=
  match plan with
  | .byte width_le => fun value =>
      StaticByte.modelToByteCode format width_le value
  | .word16 width_le => fun value =>
      StaticStorage.Word16Code.ofNat
        value.toNatBits
        (Model.toNatBits_lt_two_pow value)
        (Nat.lt_two_pow_of_lt_two_pow_of_le
          (Model.toNatBits_lt_two_pow value) width_le)
  | .word32 width_le => fun value =>
      StaticStorage.Word32Code.ofNat
        value.toNatBits
        (Model.toNatBits_lt_two_pow value)
        (Nat.lt_two_pow_of_lt_two_pow_of_le
          (Model.toNatBits_lt_two_pow value) width_le)
  | .word64 width_le => fun value =>
      StaticStorage.Word64Code.ofNat
        value.toNatBits
        (Model.toNatBits_lt_two_pow value)
        (Nat.lt_two_pow_of_lt_two_pow_of_le
          (Model.toNatBits_lt_two_pow value) width_le)
  | .wide => fun value => value
  | .limbs _ => fun value => Model.WideLimb.ofModel value

end Code

end FloatLib.Floats.Formats.BinaryInterchange.Configured
