/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Configured.DotProduct.Runtime
public import FloatLib.Floats.Formats.OCP.MX.Standard.DotProduct.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Configured MX dot-product accuracy

The configured binary32 carrier preserves the executable exact-accumulation result bit for bit.
The public error theorem therefore inherits the numerical half-ULP bound of the model operation,
with finite input and output hypotheses stated at the configured decoding boundary.
-/

public section

namespace FloatLib.Floats.ExecFloat.OCP.MX.Standard

open FloatLib.Numerics
open FloatLib.Floats.Formats.OCP.MX.Standard
open FloatLib.Floats.Formats.BinaryInterchange

/-- Configured packing introduces no further rounding of a one-block dot. -/
@[simp] theorem toModel_dot {leftProfile rightProfile : Profile}
    (left : Standard leftProfile) (right : Standard rightProfile) :
    ExecFloat.Binary.toModel (dot left right) =
      Formats.OCP.MX.Standard.dot left.toCode right.toCode := by
  unfold dot
  exact ExecFloat.Binary.toModel_ofModel _

/-- Configured packing preserves the single final rounding across all blocks. -/
@[simp] theorem toModel_dotGeneral {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Standard leftProfile) n) (right : Vector (Standard rightProfile) n) :
    ExecFloat.Binary.toModel (dotGeneral left right) =
      Formats.OCP.MX.Standard.dotGeneral (left.map toCode) (right.map toCode) := by
  unfold dotGeneral
  exact ExecFloat.Binary.toModel_ofModel _

/-- Configured multi-block dots have only the final half-ULP error, including near zero. -/
theorem abs_toReal_dotGeneral_sub_le {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Standard leftProfile) n) (right : Vector (Standard rightProfile) n)
    (a b : Fin n → Fin 32 → SignedRat)
    (ha : ∀ (j : Fin n) (i : Fin 32), left[j.val].toCode.decodeLane i = .finite (a j i))
    (hb : ∀ (j : Fin n) (i : Fin 32), right[j.val].toCode.decodeLane i = .finite (b j i))
    (hfinite : ExecFloat.Binary.isFinite (dotGeneral left right) = true) :
    |Model.toReal (ExecFloat.Binary.toModel (dotGeneral left right)) - realDot a b| ≤
      Model.epsilonAt .binary32 (realDot a b) := by
  rw [toModel_dotGeneral]
  apply Formats.OCP.MX.Standard.abs_toReal_dotGeneral_sub_le
      (left.map toCode) (right.map toCode) a b
  · simpa using ha
  · simpa using hb
  · exact (congrArg (Model.isFinite (fmt := .binary32))
      (toModel_dotGeneral left right)).symm.trans hfinite

end FloatLib.Floats.ExecFloat.OCP.MX.Standard
