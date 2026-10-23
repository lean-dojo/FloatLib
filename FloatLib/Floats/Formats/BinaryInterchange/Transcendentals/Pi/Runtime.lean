/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Enclosure.Runtime
public import FloatLib.Numerics.Enclosure.Constants.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Runtime

/-!
# Correctly rounded pi

`Model.pi fmt` rounds an enclosure of pi from the shared constants cache of
`Numerics.Enclosure.Constants`, at the fraction width plus 64 bits. When both endpoints round to the
same finite encoding, which fails only for a descriptor other than IEEE or when pi lies within
`2 ^ -(fracWidth + 62)` of a rounding boundary, that encoding is the result. Otherwise exact
comparisons of `atan 1 = π / 4` with each candidate decide the rounding. After the first use of a
precision, the enclosure costs one shift and two endpoint roundings.

`Pi.Proof` proves that for every IEEE descriptor the result is finite and is the nearest-even
rounding of `Real.pi`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Fractional bits of the cached `π / 2` that `pi` rounds: the fraction width plus 64. -/
def Transcendentals.piBits (fmt : FloatFormat) : Nat :=
  fmt.fracWidth + 64

/--
The enclosure `[2 T, 2 T + 4]` of `π * 2 ^ bits`, where `T` is the cached lower bound of
`π / 2 * 2 ^ bits`.
-/
def Transcendentals.piScaledEnclosure (bits : Nat) : Numerics.RationalInterval :=
  let lower := Numerics.Enclosure.Constants.halfPiLower bits
  ⟨((2 * lower : Nat) : ℚ), ((2 * lower + 4 : Nat) : ℚ)⟩

/--
Pi rounded to nearest-even in `fmt`. For an IEEE descriptor the result is proved finite and
correctly rounded (`toReal_pi`, `isFinite_pi`).

The cached enclosure is checked first. An enclosure that straddles a rounding boundary falls back
to `AlgebraicRounding.round` with exact arctangent comparisons. A descriptor other than IEEE
always takes that comparator path, which has no theorem.
-/
def pi (fmt : FloatFormat) : Model fmt :=
  let bits := Transcendentals.piBits fmt
  match Transcendentals.Enclosure.roundScaled? fmt (Transcendentals.piScaledEnclosure bits)
      (-(bits : Int)) with
  | some result => result
  | none =>
      let quarter := Numerics.TrigonometricComparison.prepareArctan 1 16
      AlgebraicRounding.round fmt false fun boundary => quarter.compare (boundary / 4)

end Model
end FloatLib.Floats.Formats.BinaryInterchange
