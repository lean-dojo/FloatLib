/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelRefl
public import FloatLib.Floats.Formats.P3109.KernelPath.Core
public meta import FloatLib.Tactic.P3109InlineStages
public import FloatLib.Tactic.KernelInline

/-!
# P3109 operations on encodings, one definition each

`KernelPath.Core` writes the P3109 operations in stages (decode, exact arithmetic on classes
and ratios, round, saturate, encode) that the proofs follow. Lean's kernel copies the body of
every stage that it unfolds. `Flat.add`, `Flat.mul`, `Flat.div`, `Flat.fma` and `Flat.convert`
are the same functions with every stage unfolded at elaboration time, and each is
definitionally its staged form (`Flat.add_eq` and its siblings), so the theorems of
`KernelPath.Arithmetic` transfer. The bit length `Numerics.Kernel.size` stays a call.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7 and 4.10.3–4.10.8.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Floats.ExecFloat.KernelPath


namespace Flat

/-- `KernelPath.add` with its stages unfolded. -/
noncomputable def add (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si flip a b : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.add K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si flip a b)

/-- `KernelPath.mul` with its stages unfolded. -/
noncomputable def mul (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.mul K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b)

/-- `KernelPath.div` with its stages unfolded. -/
noncomputable def div (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.div K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b)

/-- `KernelPath.fma` with its stages unfolded. -/
noncomputable def fma
    (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c : Nat) : Nat :=
  p3109_inline_stages%
    (KernelPath.fma K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c)

/-- `KernelPath.convert` with its stages unfolded. -/
noncomputable def convert (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si flip a : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.convert K₁ P₁ sg₁ ex₁ K P sg ex mi N R si flip a)

/-- `KernelPath.project` with its stages unfolded. -/
noncomputable def project (K P sg ex mi N R si cls s n d : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.project K P sg ex mi N R si cls s n d)

/-- `Flat.add` is `KernelPath.add`, by unfolding. -/
theorem add_eq (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si flip a b : Nat) :
    add K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si flip a b =
      KernelPath.add K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si flip a b := kernel_refl%

/-- `Flat.mul` is `KernelPath.mul`, by unfolding. -/
theorem mul_eq (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) :
    mul K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b =
      KernelPath.mul K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b := kernel_refl%

/-- `Flat.div` is `KernelPath.div`, by unfolding. -/
theorem div_eq (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) :
    div K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b =
      KernelPath.div K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b := kernel_refl%

/-- `Flat.fma` is `KernelPath.fma`, by unfolding. -/
theorem fma_eq
    (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c : Nat) :
    fma K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c =
      KernelPath.fma K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c :=
  kernel_refl%

/-- `Flat.convert` is `KernelPath.convert`, by unfolding. -/
theorem convert_eq (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si flip a : Nat) :
    convert K₁ P₁ sg₁ ex₁ K P sg ex mi N R si flip a =
      KernelPath.convert K₁ P₁ sg₁ ex₁ K P sg ex mi N R si flip a := kernel_refl%

/-- `Flat.project` is `KernelPath.project`, by unfolding. -/
theorem project_eq (K P sg ex mi N R si cls s n d : Nat) :
    project K P sg ex mi N R si cls s n d = KernelPath.project K P sg ex mi N R si cls s n d :=
  kernel_refl%

end Flat

end FloatLib.Floats.Formats.P3109.KernelPath
