/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Configured.Functions.Basic
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime
public import FloatLib.Floats.Formats.Posit.Functions.BasicProof

/-!
# Exact configured absolute value and sign

The Posit Standard (2022), §5.2 rational semantics transfer through any invertible
storage codec. NaR remains unavailable in the optional rational view.
-/

@[expose] public section

namespace FloatLib.Floats

open Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Decoding configured absolute value recovers model absolute value at every width. -/
@[simp] theorem toModel_abs (value : Value) :
    toModel (abs value) = Model.abs (toModel value) := by
  simp [abs, toModel, Configured.Family.toModel]

/-- Decoding configured sign recovers model sign at every width. -/
@[simp] theorem toModel_sign (value : Value) :
    toModel (sign value) = Model.sign (toModel value) := by
  simp [sign, toModel, Configured.Family.toModel]

/-- Posit Standard §5.2 absolute value is exact through every configured storage codec. -/
@[simp] theorem toRat?_abs (value : Value) :
    toRat? (abs value) = (toRat? value).map (fun q => |q|) := by
  simpa only [toRat?, toModel_abs] using Model.toRat?_abs (toModel value)

/-- Posit Standard §5.2 sign is exactly −1, 0 or 1, with NaR propagation. -/
@[simp] theorem toRat?_sign (value : Value) :
    toRat? (sign value) =
      (toRat? value).map (fun q => if q < 0 then -1 else if q = 0 then 0 else 1) := by
  simpa only [toRat?, toModel_sign] using Model.toRat?_sign (toModel value)

end ExecFloat.Posit
end FloatLib.Floats
