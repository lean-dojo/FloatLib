/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Comparison
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Mathlib ordering and enumeration for configured posits

Here configured posits get their Mathlib `LinearOrder` and `FinEnum` instances, both through
`modelEquiv`. A configured value lives in a packed carrier chosen from its static width, but the
certified codec is an equivalence with the exact-width model. So the standard posit order and the
finite enumeration carry over through any lawful model codec, whether the storage is a primitive
word, a word pair, or wide `BitVec` storage.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

namespace Family

variable {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Certified equivalence between a configured runtime value and its exact-width proof model. -/
def modelEquiv :
    FloatLib.Floats.ExecFloat (Family format code plan) ≃ Model format where
  toFun := toModel
  invFun := ofModel
  left_inv := ofModel_toModel
  right_inv := toModel_ofModel

/-- Finite enumeration transported from all exact-width posit words. -/
instance : FinEnum (FloatLib.Floats.ExecFloat (Family format code plan)) :=
  FinEnum.ofEquiv (Model format) (modelEquiv (format := format) (plan := plan) (code := code))

/--
Standard posit comparison order on the public configured carrier.

The transport is representation-independent and preserves NaR as the least word under the
two's-complement comparison rule. This is an order on encodings, including NaR. The
`DecidableEq` field reuses the carrier's existing instance rather than a second one built from
`toModel`.
-/
instance : LinearOrder (FloatLib.Floats.ExecFloat (Family format code plan)) where
  __ := PartialOrder.lift toModel fun _ _ equality => toModel_injective equality
  le_total left right := le_total (toModel left) (toModel right)
  toDecidableLE left right :=
    inferInstanceAs (Decidable (toModel left ≤ toModel right))
  toDecidableLT left right :=
    inferInstanceAs (Decidable (toModel left < toModel right))
  toDecidableEq := inferInstance

end Family

end FloatLib.Floats.Formats.Posit.Configured
