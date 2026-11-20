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
every stage that it unfolds. `Flat.add`, `Flat.mul`, `Flat.div`, `Flat.fma`, `Flat.convert`,
`Flat.recip`, `Flat.faa`, `Flat.copySign`, `Flat.sqrt`, `Flat.rsqrt`, `Flat.hypot`, the
comparisons `Flat.less`, `Flat.equal` and `Flat.lessEqual`, `Flat.extremum`, `Flat.clamp` and
the queries `Flat.isNaN` to `Flat.nextDown` are the same functions with every stage unfolded at
elaboration time, and each is definitionally its staged form (`Flat.add_eq` and its siblings),
so the theorems of `KernelPath.Arithmetic`, `KernelPath.Root`, `KernelPath.Selection` and
`KernelPath.Queries` transfer. The
bit length `Numerics.Kernel.size` is unfolded with them: below `2 ^ 128` it is the lanes of 64
bits, with their constants as literals.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7, 4.10 to 4.13 and 4.16.
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

/-- `KernelPath.recip` with its stages unfolded. -/
noncomputable def recip (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.recip K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a)

/-- `KernelPath.faa` with its stages unfolded. -/
noncomputable def faa
    (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c : Nat) : Nat :=
  p3109_inline_stages%
    (KernelPath.faa K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c)

/-- `KernelPath.copySign` with its stages unfolded. -/
noncomputable def copySign (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) : Nat :=
  p3109_inline_stages%
    (KernelPath.copySign K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b)

/-- `KernelPath.less` with its stages unfolded. -/
noncomputable def less (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.less K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b)

/-- `KernelPath.equal` with its stages unfolded. -/
noncomputable def equal (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.equal K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b)

/-- `KernelPath.lessEqual` with its stages unfolded. -/
noncomputable def lessEqual (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.lessEqual K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b)

/-- `KernelPath.extremum` with its stages unfolded. -/
noncomputable def extremum
    (mx mag var K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) : Nat :=
  p3109_inline_stages%
    (KernelPath.extremum mx mag var K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b)

/-- `KernelPath.clamp` with its stages unfolded. -/
noncomputable def clamp
    (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c : Nat) : Nat :=
  p3109_inline_stages%
    (KernelPath.clamp K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c)

/-- `KernelPath.sqrt` with its stages unfolded. -/
noncomputable def sqrt (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.sqrt K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a)

/-- `KernelPath.rsqrt` with its stages unfolded. -/
noncomputable def rsqrt (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.rsqrt K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a)

/-- `KernelPath.hypot` with its stages unfolded. -/
noncomputable def hypot (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.hypot K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b)

/-- `KernelPath.isNaN` with its stages unfolded. -/
noncomputable def isNaN (K sg a : Nat) : Bool := p3109_inline_stages% (KernelPath.isNaN K sg a)

/-- `KernelPath.isInfinite` with its stages unfolded. -/
noncomputable def isInfinite (K sg ex a : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.isInfinite K sg ex a)

/-- `KernelPath.isFinite` with its stages unfolded. -/
noncomputable def isFinite (K sg ex a : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.isFinite K sg ex a)

/-- `KernelPath.isSignMinus` with its stages unfolded. -/
noncomputable def isSignMinus (K sg a : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.isSignMinus K sg a)

/-- `KernelPath.isNormal` with its stages unfolded. -/
noncomputable def isNormal (K P sg ex a : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.isNormal K P sg ex a)

/-- `KernelPath.isSubnormal` with its stages unfolded. -/
noncomputable def isSubnormal (K P sg ex a : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.isSubnormal K P sg ex a)

/-- `KernelPath.isOne` with its stages unfolded. -/
noncomputable def isOne (K P sg ex a : Nat) : Bool :=
  p3109_inline_stages% (KernelPath.isOne K P sg ex a)

/-- `KernelPath.nextUp` with its stages unfolded. -/
noncomputable def nextUp (K sg a : Nat) : Nat := p3109_inline_stages% (KernelPath.nextUp K sg a)

/-- `KernelPath.nextDown` with its stages unfolded. -/
noncomputable def nextDown (K sg a : Nat) : Nat :=
  p3109_inline_stages% (KernelPath.nextDown K sg a)

/-- `Flat.isNaN` is `KernelPath.isNaN`, by unfolding. -/
theorem isNaN_eq (K sg a : Nat) : isNaN K sg a = KernelPath.isNaN K sg a := kernel_refl%

/-- `Flat.isInfinite` is `KernelPath.isInfinite`, by unfolding. -/
theorem isInfinite_eq (K sg ex a : Nat) :
    isInfinite K sg ex a = KernelPath.isInfinite K sg ex a := kernel_refl%

/-- `Flat.isFinite` is `KernelPath.isFinite`, by unfolding. -/
theorem isFinite_eq (K sg ex a : Nat) : isFinite K sg ex a = KernelPath.isFinite K sg ex a :=
  kernel_refl%

/-- `Flat.isSignMinus` is `KernelPath.isSignMinus`, by unfolding. -/
theorem isSignMinus_eq (K sg a : Nat) : isSignMinus K sg a = KernelPath.isSignMinus K sg a :=
  kernel_refl%

/-- `Flat.isNormal` is `KernelPath.isNormal`, by unfolding. -/
theorem isNormal_eq (K P sg ex a : Nat) :
    isNormal K P sg ex a = KernelPath.isNormal K P sg ex a := kernel_refl%

/-- `Flat.isSubnormal` is `KernelPath.isSubnormal`, by unfolding. -/
theorem isSubnormal_eq (K P sg ex a : Nat) :
    isSubnormal K P sg ex a = KernelPath.isSubnormal K P sg ex a := kernel_refl%

/-- `Flat.isOne` is `KernelPath.isOne`, by unfolding. -/
theorem isOne_eq (K P sg ex a : Nat) : isOne K P sg ex a = KernelPath.isOne K P sg ex a :=
  kernel_refl%

/-- `Flat.nextUp` is `KernelPath.nextUp`, by unfolding. -/
theorem nextUp_eq (K sg a : Nat) : nextUp K sg a = KernelPath.nextUp K sg a := kernel_refl%

/-- `Flat.nextDown` is `KernelPath.nextDown`, by unfolding. -/
theorem nextDown_eq (K sg a : Nat) : nextDown K sg a = KernelPath.nextDown K sg a :=
  kernel_refl%

/-- `Flat.sqrt` is `KernelPath.sqrt`, by unfolding. -/
theorem sqrt_eq (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a : Nat) :
    sqrt K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a =
      KernelPath.sqrt K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a := kernel_refl%

/-- `Flat.rsqrt` is `KernelPath.rsqrt`, by unfolding. -/
theorem rsqrt_eq (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a : Nat) :
    rsqrt K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a =
      KernelPath.rsqrt K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a := kernel_refl%

/-- `Flat.hypot` is `KernelPath.hypot`, by unfolding. -/
theorem hypot_eq (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) :
    hypot K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b =
      KernelPath.hypot K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b := kernel_refl%

/-- `Flat.recip` is `KernelPath.recip`, by unfolding. -/
theorem recip_eq (K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a : Nat) :
    recip K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a =
      KernelPath.recip K₁ P₁ sg₁ ex₁ K P sg ex mi N R si a := kernel_refl%

/-- `Flat.faa` is `KernelPath.faa`, by unfolding. -/
theorem faa_eq
    (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c : Nat) :
    faa K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c =
      KernelPath.faa K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c :=
  kernel_refl%

/-- `Flat.copySign` is `KernelPath.copySign`, by unfolding. -/
theorem copySign_eq (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) :
    copySign K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b =
      KernelPath.copySign K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b := kernel_refl%

/-- `Flat.less` is `KernelPath.less`, by unfolding. -/
theorem less_eq (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b : Nat) :
    less K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b = KernelPath.less K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b :=
  kernel_refl%

/-- `Flat.equal` is `KernelPath.equal`, by unfolding. -/
theorem equal_eq (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b : Nat) :
    equal K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b = KernelPath.equal K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b :=
  kernel_refl%

/-- `Flat.lessEqual` is `KernelPath.lessEqual`, by unfolding. -/
theorem lessEqual_eq (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b : Nat) :
    lessEqual K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b =
      KernelPath.lessEqual K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ a b := kernel_refl%

/-- `Flat.extremum` is `KernelPath.extremum`, by unfolding. -/
theorem extremum_eq (mx mag var K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b : Nat) :
    extremum mx mag var K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b =
      KernelPath.extremum mx mag var K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K P sg ex mi N R si a b :=
  kernel_refl%

/-- `Flat.clamp` is `KernelPath.clamp`, by unfolding. -/
theorem clamp_eq
    (K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c : Nat) :
    clamp K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c =
      KernelPath.clamp K₁ P₁ sg₁ ex₁ K₂ P₂ sg₂ ex₂ K₃ P₃ sg₃ ex₃ K P sg ex mi N R si a b c :=
  kernel_refl%

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
