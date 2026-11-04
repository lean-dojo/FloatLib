/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Core.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Core.Primitive.Word.Runtime

/-!
# One-word to two-limb Posit storage adapters

Now and then a one-word kernel continues an exact intermediate in the common `UInt128`
implementation, and this module is the boundary it crosses. Here format eligibility widens from the
storage word to the two-limb carrier, and a `UInt64` significand is zero-extended without changing
its mathematical value.

We keep these adapters outside both rounding implementations so the scalar rounder doesn't import
the two-limb arithmetic stack. Only the operation whose intermediate no longer fits one word decides
to cross.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeWordLimb

/-- One-word format eligibility implies eligibility for the common two-limb carrier. -/
theorem limbEligible
    (format : Format) (heligible : NativeWord.Eligible format) :
    NativeLimb.Eligible format := by
  unfold NativeWord.Eligible at heligible
  unfold NativeLimb.Eligible
  omega

/-- Zero-extend a native significand into the common two-limb carrier. -/
@[always_inline, inline] def widen
    (significand : UInt64) : FloatLib.Numerics.FixedWord.UInt128 :=
  { hi := 0, lo := significand }

end FloatLib.Floats.Formats.Posit.Model.NativeWordLimb
