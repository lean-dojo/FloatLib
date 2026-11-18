/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Configured
public import FloatLib.Floats.Formats.Block.Stored
public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath

/-! Shared stored-tensor certificates and NVFP4 Appendix B policy observations. -/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.BlockBackend

open FloatLib.Numerics FloatLib.Floats.Formats
open FloatLib.Floats.Formats.Block
open FloatLib.Floats.ExecFloat

-- The compiled path reconstructs the value theory for every storage format and policy.
example {ι γ : Type} (F : CodedFormat ι γ) (policy : Policy ι γ)
    (x : ι → SignedRat) (i : ι) :
    ((compiled_reference% CodedFormat.quantize (ι := ι) (γ := γ) using
      { name := "stored block quantization", kind := .generic, steadyCost := 1 }).run
        F policy x).value i =
      (F.toFormat policy).reconstruct (fun j => (x j).value) i := by
  exact CodedFormat.value_quantize F policy x i

-- The decoder certificate includes exceptional scales, independently of the element codec.
example {ι γ : Type} {F : CodedFormat ι γ} (t : Tensor F) (i : ι)
    (h : ScaleCodes.isFinite F.levels t.scales i = false) :
    (compiled_reference% Tensor.decode (F := F) using
      { name := "stored block decoding", kind := .generic, steadyCost := 1 }).run t i =
        .exceptional .nan := by
  exact Tensor.decode_of_not_isFinite t i h

private def format : CodedFormat (Fin 16) Unit :=
  nvfp4Stored (fun _ => ()) (fun _ => ())

private def policy : Policy (Fin 16) Unit :=
  nvfp4Supplied (fun _ => ()) (fun _ => 1)

-- Signed zero survives the zero local scale and exact decoding.
example : ((format.quantize policy fun _ => SignedRat.negZero).elements 0).toNat = 8 := by
  decide +kernel

example : (format.quantize policy fun _ => SignedRat.negZero).decode 0 =
    .finite SignedRat.negZero := by
  decide +kernel

-- A constant block at six selects the unit local scale and the largest positive E2M1 code.
example : ((format.quantize policy fun _ => SignedRat.ofRat 6).scales.2.1 ()).toNat = 56 := by
  decide +kernel

example : ((format.quantize policy fun _ => SignedRat.ofRat 6).elements 0).toNat = 7 := by
  decide +kernel

end FloatLibTests.Conformance.Formats.BlockBackend
