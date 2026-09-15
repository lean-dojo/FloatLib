/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Narrow.Rounding.Proof
public import FloatLib.Kernels.FixedWord.SignedMagnitude.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rounding

/-!
# Refinement of native signed-magnitude addition

The shared `UInt64` signed-magnitude primitive denotes exact dyadic addition before binary32
rounding. Keeping the proof separate preserves the small runtime import surface of
`FloatLib.Kernels.FixedWord.SignedMagnitude.Runtime`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32

/--
Round one exact signed-magnitude sum at a shared native scale.

The hypotheses require nonzero operands, a sum magnitude below `2^64`, and a scale of at most 506.
-/
theorem roundAddMagnitudesAtScale_eq_roundDyadic
    (xSign ySign : Bool) (xMagnitude yMagnitude scale : UInt64)
    (hx : xMagnitude ≠ 0) (hy : yMagnitude ≠ 0)
    (hsum : xMagnitude.toNat + yMagnitude.toNat < 2 ^ 64)
    (hscale : scale.toNat ≤ 506) :
    roundProduct
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          xSign ySign xMagnitude yMagnitude).1
        (FloatLib.Numerics.FixedWord.addSignedMagnitudes
          xSign ySign xMagnitude yMagnitude).2
        scale =
      roundDyadic
        (Model.addDyadic
          { negative := xSign
            significand := xMagnitude.toNat
            exponent := Int.ofNat scale.toNat - 298 }
          { negative := ySign
            significand := yMagnitude.toNat
            exponent := Int.ofNat scale.toNat - 298 }) := by
  have hround := roundProduct_eq_roundDyadic
    (FloatLib.Numerics.FixedWord.addSignedMagnitudes
      xSign ySign xMagnitude yMagnitude).1
    (FloatLib.Numerics.FixedWord.addSignedMagnitudes
      xSign ySign xMagnitude yMagnitude).2
    scale hscale
  rw [hround]
  have hexact :
      FloatLib.Numerics.FixedWord.signedMagnitudeDyadic
          (FloatLib.Numerics.FixedWord.addSignedMagnitudes
            xSign ySign xMagnitude yMagnitude).1
          (FloatLib.Numerics.FixedWord.addSignedMagnitudes
            xSign ySign xMagnitude yMagnitude).2
          (Int.ofNat scale.toNat - 298) =
        Model.addDyadic
          { negative := xSign
            significand := xMagnitude.toNat
            exponent := Int.ofNat scale.toNat - 298 }
          { negative := ySign
            significand := yMagnitude.toNat
            exponent := Int.ofNat scale.toNat - 298 } := by
    simpa [Model.addDyadic, FloatLib.Numerics.Dyadic.add] using
      (FloatLib.Numerics.FixedWord.signedMagnitudeDyadic_addSignedMagnitudes_eq_addFields
          xSign ySign xMagnitude yMagnitude
          (Int.ofNat scale.toNat - 298)
          hx hy (fun _ => hsum))
  rw [← hexact]
  by_cases hzero :
      (FloatLib.Numerics.FixedWord.addSignedMagnitudes
        xSign ySign xMagnitude yMagnitude).2 = 0
  · have hsign :=
      FloatLib.Numerics.FixedWord.addSignedMagnitudes_sign_eq_false_of_magnitude_eq_zero
          xSign ySign xMagnitude yMagnitude hx hy (fun _ => hsum) hzero
    simp [FloatLib.Numerics.FixedWord.signedMagnitudeDyadic,
      hzero, hsign, roundDyadic]
  · simp [FloatLib.Numerics.FixedWord.signedMagnitudeDyadic, hzero]

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary32
