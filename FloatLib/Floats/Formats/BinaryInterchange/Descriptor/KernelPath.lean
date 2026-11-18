/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value -- shake: keep

/-!
# Kernel view of descriptor values

`Descriptor format` stores the exact-width model word. The instance `natView` reads its encoding
as a natural number and stores one back with primitive projections and constructors, which makes
the kernel operations of `KernelPath.Value` and their rewrite theorems available for every
binary descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Descriptor

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath (NatView)

/-- Every binary descriptor has the natural-number view of its model word. -/
instance natView (format : FloatFormat) : NatView (Descriptor format) format where
  toNat := fun (c : Model format) => kernel_proj% (kernel_proj% (kernel_proj% c 0) 0) 0
  ofNat := fun n hn => (⟨⟨⟨n, hn⟩⟩⟩ : Model format)
  toModel := (descriptorModelCodec format).toModel
  ofModel := (descriptorModelCodec format).ofModel
  toNat_eq := fun _ => rfl
  toNat_ofNat := fun _ _ => rfl
  ofModel_toModel := fun _ => rfl

end FloatLib.Floats.Formats.BinaryInterchange.Descriptor
