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

The one-word kernels occasionally continue an exact intermediate in the common `UInt128`
implementation. This module owns that representation boundary: format eligibility is widened from
the storage word to the two-limb carrier, and a `UInt64` significand is zero-extended without
changing its mathematical value.

Keeping these adapters outside either rounding implementation prevents the scalar rounder from
importing the two-limb arithmetic stack. The decision to cross this boundary remains local to the
operation whose intermediate no longer fits one word.
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
