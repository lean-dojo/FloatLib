/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.NumericalSystem
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Semantics.Core
public import FloatLib.Floats.Formats.FixedPoint.Exact.Proof
public import FloatLib.Floats.Formats.P3109.Runtime
public import FloatLib.Numerics.Quantization.Stochastic.Lattice

/-!
# Concrete families using the common stochastic grid

All binary descriptors, including OCP FP8/FP6/FP4 element descriptors, and bounded
fixed-point words have finite carriers. P3109 already uses `BitVec` directly.
Consequently `neighbors_of_finite` applies to all those families without a
format-specific probability proof. Unbounded fixed point uses `lattice_brackets`.
These results concern the format grids; they do not assert that an arbitrary
hardware conversion implements the ideal law.

## References

The encoding conventions and their source specifications are documented in
`FloatLib.Floats.Formats.BinaryInterchange`, `FloatLib.Floats.Formats.P3109`,
and `FloatLib.Floats.Formats.FixedPoint`. The common finite-grid and lattice
arguments are proved in `FloatLib.Numerics.Quantization.Stochastic.Grid` and
`FloatLib.Numerics.Quantization.Stochastic.Lattice`.
-/

@[expose] public section

/-- Bitvector encodings have finite carriers at every width. The instance stays in this module:
the instances below are what the stochastic theory uses. -/
local instance (width : ℕ) : Finite (BitVec width) :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

namespace FloatLib.Floats.Formats.BinaryInterchange

/-- A binary interchange format has finitely many values. -/
instance (fmt : FloatFormat) : Finite (Model fmt) :=
  Finite.of_injective Model.toBits (by intro a b h; cases a; cases b; cases h; rfl)

end FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLib.Numerics.Representations

/-- The integers of a fixed width are finitely many. -/
instance (width : ℕ) : Finite (FixedInt width) :=
  Finite.of_injective FixedInt.bits (by intro a b h; cases a; cases b; cases h; rfl)

end FloatLib.Numerics.Representations

namespace FloatLib.Floats.Formats.P3109

/-- A P3109 format has finitely many codes. -/
instance (fmt : Format) : Finite fmt.numericalSystem.Code := by
  change Finite (BitVec fmt.bitWidth)
  infer_instance

end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.Formats.FixedPoint

open FloatLib.Numerics

/-- A bounded fixed-point system has finitely many codes. -/
instance (radix : Radix) (digits width : ℕ) :
    Finite (Bounded.numericalSystem radix digits width).Code := by
  change Finite (Representations.FixedInt width)
  infer_instance

/-- Every unbounded fixed-point family has floor/ceiling neighbors at every real input. -/
theorem stochastic_brackets (radix : Radix) (digits : ℕ) (x : ℝ) :
    Quantization.Ordered.Brackets ((numericalSystem radix digits).mapScalar (fun q : ℚ ↦ (q : ℝ)))
      x ⟨⌊x * scale radix digits⌋⟩ ⟨⌈x * scale radix digits⌉⟩ := by
  have hbase : 0 < radix.base := lt_of_lt_of_le (by decide) radix.base_valid
  have hs : (0 : ℝ) < scale radix digits := Nat.cast_pos.mpr (pow_pos hbase _)
  change Quantization.Ordered.Brackets
    (NumericalSystem.ofFinite (fun c : Code radix digits ↦
      (((c.coefficient : ℚ) / (scale radix digits : ℚ) : ℚ) : ℝ))) x _ _
  have hdecode :
      (fun c : Code radix digits ↦
        (((c.coefficient : ℚ) / (scale radix digits : ℚ) : ℚ) : ℝ)) =
      (fun c : Code radix digits ↦ (c.coefficient : ℝ) / (scale radix digits : ℝ)) := by
    funext c
    push_cast
    rfl
  rw [hdecode]
  exact
    Quantization.Stochastic.lattice_brackets
      (Code.coefficient (radix := radix) (fractionalDigits := digits)) Code.mk
      (fun _ ↦ rfl) (scale radix digits) hs x

end FloatLib.Floats.Formats.FixedPoint
