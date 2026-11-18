/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath.Scan.Basic

/-!
# Specialized profile scans syntax

This elaboration frontend unfolds the fixed profile constants of the generic algorithm.
-/

public meta section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics FloatLib.Floats.ExecFloat.KernelPath

/-- The scan of the first `count` codes of a profile with the profile's constants in place. -/
macro "scan_loop% " profile:term:max sp:term:max neg:term:max ap:term:max q:term:max
    count:term:max : term =>
  `(scanLoop
      (fun code best =>
        kernel_inline% [scanStep, codeKey, distance, tie, magnitude, floatMagnitude, signBit,
            finiteCode, nonFiniteShift, nonFiniteMask, exponentBits, fractionBits,
            twosComplement, denominator, Profile.width]
          (scanStep $profile $sp $neg $ap $q code best))
      $count)


end FloatLib.Floats.Formats.OCP.MX.Standard.Element
