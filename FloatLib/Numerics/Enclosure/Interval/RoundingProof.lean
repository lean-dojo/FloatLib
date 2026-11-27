/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.BinaryGridProof
public import FloatLib.Numerics.Enclosure.Interval.Rounding

/-!
# Containment and endpoints of the binary-grid roundings

For every exponent `e` and every rational `q`, `dyadicDown e q` is `⌊q * 2 ^ e⌋ / 2 ^ e` and
`dyadicUp e q` is `⌈q * 2 ^ e⌉ / 2 ^ e` (`dyadicDown_def`, `dyadicUp_def`), so the two
bracket `q` (`dyadicDown_le`, `le_dyadicUp`). From this:

* `OutwardRounding.dyadic exponent` is a total outward rounding of rationals, which rounds `q`
  on the grid of spacing `2 ^ (-exponent q)`.
* `OutwardRounding.grid`, `OutwardRounding.relative` and `OutwardRounding.quotient` are the
  members with the exponents of `dyadicHull`, `relativeHull` and `quotientHull`, and those hulls
  are their interval roundings (`encloseInterval?_grid`, `encloseInterval?_relative`,
  `encloseInterval?_quotient`), so each rounding is one operation.
* each hull contains every real member of the input interval (`containsReal_dyadicHull`,
  `containsReal_relativeHull`, `containsReal_quotientHull`).

The endpoint equations state the definitions in ordinary notation, for every input. The fixed
grid rounds with floors and ceilings (`dyadicHull_lo`, `dyadicHull_hi`). The relative rounding
does the same at the exponent `relativeExponent bits q` (`roundDownRel_def`, `roundUpRel_def`),
which `relativeExponent_def` writes with `Nat.log2`. The grid for quotients does the same at
`gridBits bits q` fractional bits (`quotientHull_lo`, `quotientHull_hi`), and `gridBits_def`
writes its bit lengths with Mathlib's `Nat.size`.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

open FloatLib.Numerics.Kernel

/-- `dyadicDown e q` is `⌊q * 2 ^ e⌋ / 2 ^ e`, for every exponent `e`. -/
theorem dyadicDown_def (e : ℤ) (q : ℚ) : dyadicDown e q = (⌊q * 2 ^ e⌋ : ℚ) / 2 ^ e := by
  cases e with
  | ofNat n =>
    change BinaryGrid.toRat n (BinaryGrid.enclose n q).lo = _
    rw [BinaryGrid.toRat_eq_div, BinaryGrid.enclose_lo_eq_floor, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc m =>
    change Q.mk (Z.shiftLeft (Z.floorDiv q.num (q.den <<< (m + 1))) (m + 1)) 1 = _
    have hpow : (2 : ℚ) ^ Int.negSucc m = ((2 : ℚ) ^ (m + 1))⁻¹ := by
      rw [Int.negSucc_eq, ← Nat.cast_succ, zpow_neg, zpow_natCast]
    have hq : q * 2 ^ Int.negSucc m = (q.num : ℚ) / ((q.den <<< (m + 1) : ℕ) : ℚ) := by
      rw [hpow, Nat.shiftLeft_eq, Nat.cast_mul, ← div_div, Rat.num_div_den, div_eq_mul_inv]
      push_cast
      rfl
    rw [Q.mk_eq, Rat.mkRat_one, Z.shiftLeft_eq, Z.floorDiv_eq, Int.shiftLeft_eq, hq,
      Rat.floor_intCast_div_natCast, hpow, div_inv_eq_mul]
    push_cast
    rfl

/-- `dyadicUp e q` is `⌈q * 2 ^ e⌉ / 2 ^ e`, for every exponent `e`. -/
theorem dyadicUp_def (e : ℤ) (q : ℚ) : dyadicUp e q = (⌈q * 2 ^ e⌉ : ℚ) / 2 ^ e := by
  cases e with
  | ofNat n =>
    change BinaryGrid.toRat n (BinaryGrid.enclose n q).hi = _
    rw [BinaryGrid.toRat_eq_div, BinaryGrid.enclose_hi_eq_ceil, Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc m =>
    change Q.mk (Z.shiftLeft (Z.ceilDiv q.num (q.den <<< (m + 1))) (m + 1)) 1 = _
    have hpow : (2 : ℚ) ^ Int.negSucc m = ((2 : ℚ) ^ (m + 1))⁻¹ := by
      rw [Int.negSucc_eq, ← Nat.cast_succ, zpow_neg, zpow_natCast]
    have hq : q * 2 ^ Int.negSucc m = (q.num : ℚ) / ((q.den <<< (m + 1) : ℕ) : ℚ) := by
      rw [hpow, Nat.shiftLeft_eq, Nat.cast_mul, ← div_div, Rat.num_div_den, div_eq_mul_inv]
      push_cast
      rfl
    rw [Q.mk_eq, Rat.mkRat_one, Z.shiftLeft_eq, Z.ceilDiv_eq, Int.shiftLeft_eq, hq,
      Rat.ceil_intCast_div_natCast, hpow, div_inv_eq_mul]
    push_cast
    rfl

/-- Rounding down to a multiple of `2 ^ (-e)` does not increase `q`. -/
theorem dyadicDown_le (e : ℤ) (q : ℚ) : dyadicDown e q ≤ q := by
  rw [dyadicDown_def, div_le_iff₀ (zpow_pos two_pos e)]
  exact Int.floor_le _

/-- Rounding up to a multiple of `2 ^ (-e)` does not decrease `q`. -/
theorem le_dyadicUp (e : ℤ) (q : ℚ) : q ≤ dyadicUp e q := by
  rw [dyadicUp_def, le_div_iff₀ (zpow_pos two_pos e)]
  exact Int.le_ceil _

end FloatLib.Numerics.Interval

namespace FloatLib.Numerics.OutwardRounding

/--
Total outward rounding of rationals to binary grids: `q` is enclosed by the multiples of
`2 ^ (-exponent q)` just below and just above it (`Interval.dyadicDown`, `Interval.dyadicUp`).
The endpoints are rationals, decoded by `some`.
-/
def dyadic (exponent : ℚ → ℤ) : OutwardRounding ℚ ℚ where
  decode := some
  enclose? q := some ⟨Interval.dyadicDown (exponent q) q, Interval.dyadicUp (exponent q) q⟩
  sound := by
    intro q I h
    cases Option.some.inj h
    exact ⟨_, _, rfl, rfl, Interval.dyadicDown_le _ q, Interval.le_dyadicUp _ q⟩

/--
Outward rounding to the fixed grid of spacing `2 ^ (-bits)`. Its interval rounding is
`Interval.dyadicHull bits` (`Interval.encloseInterval?_grid`).
-/
def grid (bits : ℕ) : OutwardRounding ℚ ℚ :=
  dyadic fun _ => Int.ofNat bits

/--
Outward rounding to about `bits` significant bits, on the grid of
`Interval.relativeExponent bits q` fractional bits at `q`. Its interval rounding is
`Interval.relativeHull bits` (`Interval.encloseInterval?_relative`).
-/
def relative (bits : ℕ) : OutwardRounding ℚ ℚ :=
  dyadic (Interval.relativeExponent bits)

/--
Outward rounding on the grid of `Interval.gridBits bits q` fractional bits at `q`, which keeps
the leading bits of small quotients. Its interval rounding is `Interval.quotientHull bits`
(`Interval.encloseInterval?_quotient`).
-/
def quotient (bits : ℕ) : OutwardRounding ℚ ℚ :=
  dyadic fun q => Int.ofNat (Interval.gridBits bits q)

end FloatLib.Numerics.OutwardRounding

namespace FloatLib.Numerics.Interval

open FloatLib.Numerics.Kernel

/-! ### The fixed grid -/

/-- The interval rounding of `OutwardRounding.grid bits` is `dyadicHull bits`. -/
theorem encloseInterval?_grid (bits : ℕ) (I : Interval ℚ) :
    encloseInterval? (OutwardRounding.grid bits) I = some (dyadicHull bits I) :=
  rfl

/-- Every real member of `I` is a member of `dyadicHull bits I`. -/
theorem containsReal_dyadicHull (bits : ℕ) {I : Interval ℚ} {x : ℝ}
    (hx : I.ContainsReal some x) : (dyadicHull bits I).ContainsReal some x :=
  containsReal_encloseInterval? _ (encloseInterval?_grid bits I)
    ((containsReal_some_iff I x).1 hx)

/-- The lower endpoint of `dyadicHull bits I` is `⌊I.lo * 2 ^ bits⌋ / 2 ^ bits`. -/
theorem dyadicHull_lo (bits : ℕ) (I : Interval ℚ) :
    (dyadicHull bits I).lo = (⌊I.lo * 2 ^ bits⌋ : ℚ) / 2 ^ bits := by
  change dyadicDown (Int.ofNat bits) I.lo = _
  rw [dyadicDown_def, Int.ofNat_eq_natCast, zpow_natCast]

/-- The upper endpoint of `dyadicHull bits I` is `⌈I.hi * 2 ^ bits⌉ / 2 ^ bits`. -/
theorem dyadicHull_hi (bits : ℕ) (I : Interval ℚ) :
    (dyadicHull bits I).hi = (⌈I.hi * 2 ^ bits⌉ : ℚ) / 2 ^ bits := by
  change dyadicUp (Int.ofNat bits) I.hi = _
  rw [dyadicUp_def, Int.ofNat_eq_natCast, zpow_natCast]

/-! ### Relative precision -/

/-- `relativeExponent bits q` is `bits - ⌊log₂ |num q|⌋ + ⌊log₂ (den q)⌋`. -/
theorem relativeExponent_def (bits : ℕ) (q : ℚ) :
    relativeExponent bits q =
      (bits : ℤ) - (Nat.log2 q.num.natAbs : ℤ) + (Nat.log2 q.den : ℤ) := by
  rw [relativeExponent, Z.add_eq, Z.subNat_eq, Kernel.log2_eq, Kernel.log2_eq, Z.natAbs_eq,
    Int.ofNat_eq_natCast]

/-- `roundDownRel bits q` is `⌊q * 2 ^ e⌋ / 2 ^ e` for `e = relativeExponent bits q`. -/
theorem roundDownRel_def (bits : ℕ) (q : ℚ) :
    roundDownRel bits q =
      (⌊q * 2 ^ relativeExponent bits q⌋ : ℚ) / 2 ^ relativeExponent bits q :=
  dyadicDown_def _ q

/-- `roundUpRel bits q` is `⌈q * 2 ^ e⌉ / 2 ^ e` for `e = relativeExponent bits q`. -/
theorem roundUpRel_def (bits : ℕ) (q : ℚ) :
    roundUpRel bits q =
      (⌈q * 2 ^ relativeExponent bits q⌉ : ℚ) / 2 ^ relativeExponent bits q :=
  dyadicUp_def _ q

/-- Rounding down on the grid selected by `relativeExponent bits q` does not increase `q`. -/
theorem roundDownRel_le (bits : ℕ) (q : ℚ) : roundDownRel bits q ≤ q :=
  dyadicDown_le _ q

/-- Rounding up on the grid selected by `relativeExponent bits q` does not decrease `q`. -/
theorem le_roundUpRel (bits : ℕ) (q : ℚ) : q ≤ roundUpRel bits q :=
  le_dyadicUp _ q

/-- The lower endpoint is `I.lo` rounded down on its grid to about `bits` significant bits. -/
@[simp]
theorem relativeHull_lo (bits : ℕ) (I : Interval ℚ) :
    (relativeHull bits I).lo = roundDownRel bits I.lo :=
  rfl

/-- The upper endpoint is `I.hi` rounded up on its grid to about `bits` significant bits. -/
@[simp]
theorem relativeHull_hi (bits : ℕ) (I : Interval ℚ) :
    (relativeHull bits I).hi = roundUpRel bits I.hi :=
  rfl

/-- The interval rounding of `OutwardRounding.relative bits` is `relativeHull bits`. -/
theorem encloseInterval?_relative (bits : ℕ) (I : Interval ℚ) :
    encloseInterval? (OutwardRounding.relative bits) I = some (relativeHull bits I) :=
  rfl

/-- Every real member of `I` is a member of `relativeHull bits I`. -/
theorem containsReal_relativeHull (bits : ℕ) {I : Interval ℚ} {x : ℝ}
    (hx : I.ContainsReal some x) : (relativeHull bits I).ContainsReal some x :=
  containsReal_encloseInterval? _ (encloseInterval?_relative bits I)
    ((containsReal_some_iff I x).1 hx)

/-! ### The grid for quotients -/

/-- `gridBits bits q` is `bits` plus the bit length of the denominator of `q` less that of its
numerator, cut off at zero. -/
theorem gridBits_def (bits : ℕ) (q : ℚ) :
    gridBits bits q = bits + (Nat.size q.den - Nat.size q.num.natAbs) := by
  rw [gridBits, Kernel.size_eq, Kernel.size_eq, Z.natAbs_eq]
  rfl

/-- The interval rounding of `OutwardRounding.quotient bits` is `quotientHull bits`. -/
theorem encloseInterval?_quotient (bits : ℕ) (I : Interval ℚ) :
    encloseInterval? (OutwardRounding.quotient bits) I = some (quotientHull bits I) :=
  rfl

/-- Every real member of `I` is a member of `quotientHull bits I`. -/
theorem containsReal_quotientHull (bits : ℕ) {I : Interval ℚ} {x : ℝ}
    (hx : I.ContainsReal some x) : (quotientHull bits I).ContainsReal some x :=
  containsReal_encloseInterval? _ (encloseInterval?_quotient bits I)
    ((containsReal_some_iff I x).1 hx)

/-- The lower endpoint of `quotientHull bits I` is `I.lo` rounded down on the grid of
`gridBits bits I.lo` fractional bits. -/
theorem quotientHull_lo (bits : ℕ) (I : Interval ℚ) :
    (quotientHull bits I).lo =
      (⌊I.lo * 2 ^ gridBits bits I.lo⌋ : ℚ) / 2 ^ gridBits bits I.lo := by
  change dyadicDown (Int.ofNat (gridBits bits I.lo)) I.lo = _
  rw [dyadicDown_def, Int.ofNat_eq_natCast, zpow_natCast]

/-- The upper endpoint of `quotientHull bits I` is `I.hi` rounded up on the grid of
`gridBits bits I.hi` fractional bits. -/
theorem quotientHull_hi (bits : ℕ) (I : Interval ℚ) :
    (quotientHull bits I).hi =
      (⌈I.hi * 2 ^ gridBits bits I.hi⌉ : ℚ) / 2 ^ gridBits bits I.hi := by
  change dyadicUp (Int.ofNat (gridBits bits I.hi)) I.hi = _
  rw [dyadicUp_def, Int.ofNat_eq_natCast, zpow_natCast]

end FloatLib.Numerics.Interval
