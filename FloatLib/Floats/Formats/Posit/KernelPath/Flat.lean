/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelRefl
public import FloatLib.Floats.Formats.Posit.KernelPath.Quire
public meta import FloatLib.Tactic.PositInlineStages
public import FloatLib.Tactic.KernelInline

/-!
# Posit operations on encodings, one definition each

`KernelPath.Core` writes the posit operations in stages (decode, align, round) that the proofs
follow. Lean's kernel pays for every stage that it unfolds: it copies the body of the stage
before it evaluates it. `Flat.add`, `Flat.sub`, `Flat.mul`, `Flat.div`, `Flat.sqrt`, `Flat.fma`,
`Flat.cast` and `Flat.ofRatio` are the same functions with every stage unfolded at elaboration
    time, so that
the kernel unfolds one definition for an operation, and `Flat.quireAddPosit`,
`Flat.quireAddProduct`, `Flat.quireAddQuire` and `Flat.quireRound` are the quire operations of
`KernelPath.Quire` in the same form. Each is definitionally its staged form (`Flat.add_eq` and
its siblings), so the theorems of `KernelPath.Standard` and `KernelPath.QuireProof` transfer.

The bit length (`Numerics.Kernel.bitLength`, `size`) and the integer square root (`isqrt`) stay
calls: their code is on no other path.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Floats.ExecFloat.KernelPath


namespace Flat

/-- `KernelPath.add` with its stages unfolded. -/
noncomputable def add (p es a b : Nat) : Nat := posit_inline_stages% (KernelPath.add p es a b)

/-- `KernelPath.sub` with its stages unfolded. -/
noncomputable def sub (p es a b : Nat) : Nat := posit_inline_stages% (KernelPath.sub p es a b)

/-- `KernelPath.mul` with its stages unfolded. -/
noncomputable def mul (p es a b : Nat) : Nat := posit_inline_stages% (KernelPath.mul p es a b)

/-- `KernelPath.div` with its stages unfolded. -/
noncomputable def div (p es a b : Nat) : Nat := posit_inline_stages% (KernelPath.div p es a b)

/-- `KernelPath.sqrt` with its stages unfolded. -/
noncomputable def sqrt (p es a : Nat) : Nat := posit_inline_stages% (KernelPath.sqrt p es a)

/-- `KernelPath.fma` with its stages unfolded. -/
noncomputable def fma (p es a b c : Nat) : Nat := posit_inline_stages% (KernelPath.fma p es a b c)

/-- `KernelPath.cast` with its stages unfolded. -/
noncomputable def cast (p es q es' a : Nat) : Nat := posit_inline_stages% (KernelPath.cast p es
    q es' a)

/-- `KernelPath.ofRatio` with its stages unfolded. -/
noncomputable def ofRatio (p es s num den : Nat) : Nat :=
  posit_inline_stages% (KernelPath.ofRatio p es s num den)

/-- `KernelPath.quireAddPosit` with its stages unfolded. -/
noncomputable def quireAddPosit (p q a flip : Nat) : Nat :=
  posit_inline_stages% (KernelPath.quireAddPosit p q a flip)

/-- `KernelPath.quireAddProduct` with its stages unfolded. -/
noncomputable def quireAddProduct (p q a b flip : Nat) : Nat :=
  posit_inline_stages% (KernelPath.quireAddProduct p q a b flip)

/-- `KernelPath.quireAddQuire` with its stages unfolded. -/
noncomputable def quireAddQuire (p q r flip : Nat) : Nat :=
  posit_inline_stages% (KernelPath.quireAddQuire p q r flip)

/-- `KernelPath.quireRound` with its stages unfolded. -/
noncomputable def quireRound (p q : Nat) : Nat := posit_inline_stages% (KernelPath.quireRound p q)

/-- `Flat.add` is `KernelPath.add`, by unfolding. -/
theorem add_eq (p es a b : Nat) : add p es a b = KernelPath.add p es a b := kernel_refl%

/-- `Flat.sub` is `KernelPath.sub`, by unfolding. -/
theorem sub_eq (p es a b : Nat) : sub p es a b = KernelPath.sub p es a b := kernel_refl%

/-- `Flat.mul` is `KernelPath.mul`, by unfolding. -/
theorem mul_eq (p es a b : Nat) : mul p es a b = KernelPath.mul p es a b := kernel_refl%

/-- `Flat.div` is `KernelPath.div`, by unfolding. -/
theorem div_eq (p es a b : Nat) : div p es a b = KernelPath.div p es a b := kernel_refl%

/-- `Flat.sqrt` is `KernelPath.sqrt`, by unfolding. -/
theorem sqrt_eq (p es a : Nat) : sqrt p es a = KernelPath.sqrt p es a := kernel_refl%

/-- `Flat.fma` is `KernelPath.fma`, by unfolding. -/
theorem fma_eq (p es a b c : Nat) : fma p es a b c = KernelPath.fma p es a b c := kernel_refl%

/-- `Flat.cast` is `KernelPath.cast`, by unfolding. -/
theorem cast_eq (p es q es' a : Nat) : cast p es q es' a = KernelPath.cast p es q es' a :=
  kernel_refl%

/-- `Flat.ofRatio` is `KernelPath.ofRatio`, by unfolding. -/
theorem ofRatio_eq (p es s num den : Nat) :
    ofRatio p es s num den = KernelPath.ofRatio p es s num den := kernel_refl%

/-- `Flat.quireAddPosit` is `KernelPath.quireAddPosit`, by unfolding. -/
theorem quireAddPosit_eq (p q a flip : Nat) :
    quireAddPosit p q a flip = KernelPath.quireAddPosit p q a flip := kernel_refl%

/-- `Flat.quireAddProduct` is `KernelPath.quireAddProduct`, by unfolding. -/
theorem quireAddProduct_eq (p q a b flip : Nat) :
    quireAddProduct p q a b flip = KernelPath.quireAddProduct p q a b flip := kernel_refl%

/-- `Flat.quireAddQuire` is `KernelPath.quireAddQuire`, by unfolding. -/
theorem quireAddQuire_eq (p q r flip : Nat) :
    quireAddQuire p q r flip = KernelPath.quireAddQuire p q r flip := kernel_refl%

/-- `Flat.quireRound` is `KernelPath.quireRound`, by unfolding. -/
theorem quireRound_eq (p q : Nat) : quireRound p q = KernelPath.quireRound p q := kernel_refl%

end Flat

end FloatLib.Floats.Formats.Posit.KernelPath
