/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath.Nearest

/-!
# Specialized nearest-element rounding syntax

This elaboration frontend unfolds the fixed profile constants of the generic algorithm.
-/

public meta section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics FloatLib.Floats.ExecFloat.KernelPath

/-- `nearest` for one sign-magnitude profile with the profile's constants in place. -/
macro "nearest_flat% " profile:term:max sp:term:max neg:term:max ap:term:max q:term:max
    half:term:max bits:term:max : term =>
  `(nearestWith
      (fun j =>
        kernel_inline% [below, signValue, magnitude, floatMagnitude, finiteCode, nonFiniteShift,
            nonFiniteMask, exponentBits, fractionBits, twosComplement, denominator, Profile.width]
          (below $profile (Nat.mul $ap (denominator $profile)) $q j))
      (fun j =>
        kernel_inline% [finiteCode, nonFiniteShift, nonFiniteMask] (finiteCode $profile j))
      (fun code =>
        kernel_inline% [entry, codeKey, distance, tie, magnitude, floatMagnitude, signBit,
            exponentBits, fractionBits, twosComplement, denominator, Profile.width]
          (entry $profile $sp $neg $ap $q code))
      $half $bits $sp)


end FloatLib.Floats.Formats.OCP.MX.Standard.Element
