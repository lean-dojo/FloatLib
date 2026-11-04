/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Descriptor
public import FloatLib.Kernels.FixedWord.Core.Runtime

/-!
# Runtime capacity contracts for two-limb posit arithmetic

Two `UInt64` limbs hold a posit only up to a certain width, and this module pins that capacity
down with width bounds and native endpoints for the direct two-limb kernels. A complete retained
encoding uses at most 128 bits, and although rounding also looks at the nonnegative half of the
standard's descriptor, which is one bit wider, that half fits the same 128-bit carrier.

`candidateEligible_of_eligible` sits beside the executable definitions because dependent runtime
constructors consume it as an erased capacity certificate.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.NativeLimb

open FloatLib.Numerics

variable {format : Format}

/-- Width bound for storing a complete posit encoding in two native words. -/
def Eligible (format : Format) : Prop :=
  format.bits ≤ 128

instance (format : Format) : Decidable (Eligible format) := by
  unfold Eligible
  infer_instance

/--
Capacity contract for a nonnegative candidate code in two native words.

The sign bit of the candidate descriptor is not stored, so the positive half of a 129-bit
descriptor fills the 128-bit carrier with no bit to spare.
-/
def CandidateEligible (format : Format) : Prop :=
  format.bits ≤ 129

instance (format : Format) : Decidable (CandidateEligible format) := by
  unfold CandidateEligible
  infer_instance

/--
Every fully stored two-limb posit admits direct nonnegative-candidate decoding.

This proposition is an erased width certificate required by dependent runtime constructors.
-/
theorem candidateEligible_of_eligible (format : Format)
    (heligible : Eligible format) :
    CandidateEligible format := by
  unfold Eligible at heligible
  unfold CandidateEligible
  omega

/--
The positive-code exclusive upper endpoint `format.signMaskNat`, in two native limbs.

The word is exact only for `Eligible` formats (`signMaskWord_toNat`), and every caller in the
library has one. At width 129, which `CandidateEligible` admits, the endpoint `2 ^ 128` does not
fit and `UInt128.ofNat` reduces it to zero, so candidate-width code must not compare against
this word.
-/
@[inline] def signMaskWord (format : Format) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  FloatLib.Numerics.FixedWord.UInt128.ofNat format.signMaskNat

end FloatLib.Floats.Formats.Posit.Model.NativeLimb
