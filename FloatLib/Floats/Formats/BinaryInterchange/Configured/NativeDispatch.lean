/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.NativeCapability

/-!
# First-order dispatch for binary32 and binary64

Binary32 and binary64 use first-order operation instances that name their fixed-format
specializations. The public type constructor lives in `Configured.Type`, while the generic
table, word, limb, and baseline instances live in `Configured.Plan.Instances`.

Each instance names the fixed-format certificate it executes.
`Plan.selectCertified_binary32AddCandidates` and its siblings prove that the planner selects this
certificate under every `Policy`. So the kernel that runs is the proved kernel `#float_info`
reports, whichever `PolicyFor` instance is in scope. Each instance is a `Capability.Static`:
where a candidate tagged `@[compiler_optimize]` applies to binary32 or binary64, the planner
chooses between it and the fixed-format kernel.

The guarded host operations live in `Configured.NativeFPU.Unchecked`, and no compiler
substitution or certified candidate puts them behind these capabilities.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary

/-! ## Binary32: the proved fixed-format word kernels -/

native_capability 32 (8 23) Add add := Configured.Backend.wordAdd, rfl
native_capability 32 (8 23) Sub sub := Configured.Backend.wordSub, rfl
native_capability 32 (8 23) Mul mul := Configured.Backend.wordMul, rfl
native_capability 32 (8 23) Div div := Configured.Backend.wordDiv, rfl
native_capability 32 (8 23) Sqrt sqrt := Configured.Backend.wordSqrt, rfl
native_capability 32 (8 23) Fma fma := Configured.Backend.wordFma, rfl

/-! ## Binary64: kernels on the stored words, compiled once each -/

/--
Binary64 addition on the stored words, compiled once as a specialized function. The instance
calls it rather than inlining the word kernel into every caller, which keeps arithmetic loops
small.
-/
def Internal.binary64Add (left right : FloatLib.Floats.ExecFloat (Family 11 52)) :
    FloatLib.Floats.ExecFloat (Family 11 52) :=
  Configured.Backend.binary64Add (by decide) (by decide) left right

/-- Binary64 subtraction on the stored words, compiled once as a specialized function. -/
def Internal.binary64Sub (left right : FloatLib.Floats.ExecFloat (Family 11 52)) :
    FloatLib.Floats.ExecFloat (Family 11 52) :=
  Configured.Backend.binary64Sub (by decide) (by decide) left right

/-- Binary64 multiplication on the stored words, compiled once as a specialized function. -/
def Internal.binary64Mul (left right : FloatLib.Floats.ExecFloat (Family 11 52)) :
    FloatLib.Floats.ExecFloat (Family 11 52) :=
  Configured.Backend.binary64Mul (by decide) (by decide) left right

/-- Binary64 division on the stored words, compiled once as a specialized function. -/
def Internal.binary64Div (left right : FloatLib.Floats.ExecFloat (Family 11 52)) :
    FloatLib.Floats.ExecFloat (Family 11 52) :=
  Configured.Backend.binary64Div (by decide) (by decide) left right

/-- Binary64 fused multiply-add on the stored words, compiled once as a specialized function. -/
def Internal.binary64Fma (left right addend : FloatLib.Floats.ExecFloat (Family 11 52)) :
    FloatLib.Floats.ExecFloat (Family 11 52) :=
  Configured.Backend.binary64Fma (by decide) (by decide) left right addend

native_capability 64 (11 52) Add add := Internal.binary64Add, by
  funext left right
  exact Configured.Backend.binary64Add_eq (by decide) (by decide) left right
native_capability 64 (11 52) Sub sub := Internal.binary64Sub, by
  funext left right
  exact Configured.Backend.binary64Sub_eq (by decide) (by decide) left right
native_capability 64 (11 52) Mul mul := Internal.binary64Mul, by
  funext left right
  exact Configured.Backend.binary64Mul_eq (by decide) (by decide) left right
native_capability 64 (11 52) Div div := Internal.binary64Div, by
  funext left right
  exact Configured.Backend.binary64Div_eq (by decide) (by decide) left right
native_capability 64 (11 52) Sqrt sqrt := Configured.Backend.wordSqrt, rfl
native_capability 64 (11 52) Fma fma := Internal.binary64Fma, by
  funext left right addend
  exact Configured.Backend.binary64Fma_eq (by decide) (by decide) left right addend

end FloatLib.Floats.ExecFloat.Binary
