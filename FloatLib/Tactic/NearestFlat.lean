/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath.Nearest

/-!
# Specialized nearest-element rounding syntax

This elaboration frontend unfolds the generic algorithm at a fixed profile and computes the
constants of the profile.
-/

public meta section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics FloatLib.Floats.ExecFloat.KernelPath

/--
`nearest` for one sign-magnitude profile as one flat term: the skeleton, the test of the
bisection and the entries unfolded, with the constants of the profile computed. The bisection
itself stays a call, with the flat test as its argument.
-/
macro "nearest_flat% " profile:term:max sp:term:max neg:term:max ap:term:max q:term:max : term =>
  `(kernel_inline% [nearest, nearestWith, least, Nat.blt, below, entry, codeKey, distance, tie,
        signValue, magnitude, floatMagnitude, signBit, finiteCode, nonFiniteShift, nonFiniteMask,
        exponentBits, fractionBits, twosComplement, denominator, Profile.width]
      (nearest $profile $sp $neg $ap $q))

/-- `int8Nearest` as one flat term, with the constants of INT8 computed. -/
macro "int8_nearest_flat% " sp:term:max neg:term:max ap:term:max q:term:max : term =>
  `(kernel_inline% [int8Nearest, int8NearestWith, least, Nat.blt, int8Below, entry, int8Code,
        codeKey, distance, tie, magnitude, signBit, twosComplement, denominator, Profile.width]
      (int8Nearest $sp $neg $ap $q))

/--
`nearestGuessed` for one sign-magnitude profile as one flat term, with `other` as the
alternative: the guess, its two tests and the entries unfolded, with the constants of the
profile computed.
-/
macro "nearest_guess_flat% " profile:term:max sp:term:max neg:term:max ap:term:max q:term:max
    other:term:max : term =>
  `(kernel_inline% [nearestGuessed, Numerics.Kernel.guarded, nearestAt, fieldGuess, least,
        Nat.blt, below, entry, codeKey, distance, tie, signValue, magnitude, floatMagnitude,
        signBit, finiteCode, nonFiniteShift, nonFiniteMask, exponentBits, fractionBits,
        twosComplement, denominator, Profile.width, Numerics.Kernel.minNat, Numerics.Kernel.size,
        Numerics.Kernel.laneLength, Numerics.Kernel.laneOnes, Numerics.Kernel.laneOffsets]
      (nearestGuessed $profile $sp $neg $ap $q $other))

/-- `int8NearestGuessed` as one flat term, with `other` as the alternative. -/
macro "int8_nearest_guess_flat% " sp:term:max neg:term:max ap:term:max q:term:max
    other:term:max : term =>
  `(kernel_inline% [int8NearestGuessed, Numerics.Kernel.guarded, int8NearestAt, int8Guess,
        least, Nat.blt, int8Below, entry, int8Code, codeKey, distance, tie, magnitude, signBit,
        twosComplement, denominator, Profile.width, Numerics.Kernel.minNat]
      (int8NearestGuessed $sp $neg $ap $q $other))

end FloatLib.Floats.Formats.OCP.MX.Standard.Element
