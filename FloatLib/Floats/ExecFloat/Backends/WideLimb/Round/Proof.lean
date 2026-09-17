/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Round.Runtime
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import FloatLib.Numerics.ShiftRightJam.Proof

/-!
# Verified wide-limb normal rounding

The proof proceeds through a natural-number specification `roundJammed`, which restates the normal
branch of `FiniteProductRound.round` for a significand whose `jam` low bits have been jammed into
one sticky bit. Two theorems connect it to its neighbours.

* `roundNormal?_map_toModel`: the limb kernel computes `roundJammed` on the value of its
  nonzero significand, assuming the exponent field fits in 32 bits.
* `round_eq_of_roundJammed`: an accepted `roundJammed` result on the jammed value is the exact
  rounder `FiniteProductRound.round` on the exact value, by `roundShiftRightEven_shiftRightJam`.

Together they let each arithmetic kernel prove `toModel result = FiniteProductRound.round ...` and
then reuse the generic kernel's own refinement theorems.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-! ## The natural-number specification -/

/--
The normal branch of `FiniteProductRound.round` for a jammed significand.

For a sufficiently large exact value, `significand = shiftRightJam exact jam` has its leading bit
`jam` positions below that of `exact`. `round_eq_of_roundJammed` states the required bound;
`roundNormal?_map_toModel` relates this specification to the limb kernel on nonzero inputs.
-/
def roundJammed (fmt : FloatFormat) (sign : Bool) (significand jam scale : Nat) :
    Option (Model fmt) :=
  let leading := significand.log2
  let position := leading + jam + scale
  if position < fmt.bias + 2 * fmt.fracWidth - 1 then
    none
  else
    let rounded :=
      if fmt.fracWidth ≤ leading then
        Numerics.roundShiftRightEven significand (leading - fmt.fracWidth)
      else
        significand * 2 ^ (fmt.fracWidth - leading)
    let carry := rounded = 2 ^ (fmt.fracWidth + 1)
    let normalizedPosition := if carry then position + 1 else position
    if 3 * fmt.bias + 2 * fmt.fracWidth - 2 < normalizedPosition then
      none
    else
      some <| ofFields fmt sign
        (normalizedPosition - (fmt.bias + 2 * fmt.fracWidth - 2))
        (rounded % 2 ^ fmt.fracWidth)

/-! ## Bounds on the rounded significand -/

/-- Rounding a nonzero value to `fracWidth + 1` bits lands in `[2^fracWidth, 2^(fracWidth + 1)]`. -/
theorem rounded_bounds (S : Nat) (hS : S ≠ 0) :
    let rounded :=
      if fmt.fracWidth ≤ S.log2 then
        Numerics.roundShiftRightEven S (S.log2 - fmt.fracWidth)
      else
        S * 2 ^ (fmt.fracWidth - S.log2)
    2 ^ fmt.fracWidth ≤ rounded ∧ rounded ≤ 2 ^ (fmt.fracWidth + 1) := by
  intro rounded
  have hlow := Nat.log2_self_le hS
  have hhigh := Nat.lt_log2_self (n := S)
  by_cases hle : fmt.fracWidth ≤ S.log2
  · simp only [rounded, hle, ite_true]
    have hpos : 0 < 2 ^ (S.log2 - fmt.fracWidth) := Nat.two_pow_pos _
    have hdivLow : 2 ^ fmt.fracWidth ≤ S / 2 ^ (S.log2 - fmt.fracWidth) := by
      rw [Nat.le_div_iff_mul_le hpos, ← pow_add, Nat.add_sub_cancel' hle]
      exact hlow
    have hdivHigh : S / 2 ^ (S.log2 - fmt.fracWidth) < 2 ^ (fmt.fracWidth + 1) := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, show fmt.fracWidth + 1 + (S.log2 - fmt.fracWidth) =
        S.log2 + 1 by omega]
      exact hhigh
    constructor
    · exact le_trans hdivLow (div_two_pow_le_roundShiftRightEven _ _)
    · have := roundShiftRightEven_le_succ S (S.log2 - fmt.fracWidth)
      omega
  · simp only [rounded, hle, ite_false]
    have hlt : S.log2 < fmt.fracWidth := Nat.lt_of_not_le hle
    constructor
    · calc
        2 ^ fmt.fracWidth = 2 ^ S.log2 * 2 ^ (fmt.fracWidth - S.log2) := by
          rw [← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hlt)]
        _ ≤ S * 2 ^ (fmt.fracWidth - S.log2) := Nat.mul_le_mul_right _ hlow
    · calc
        S * 2 ^ (fmt.fracWidth - S.log2) ≤ (2 ^ (S.log2 + 1) - 1) * 2 ^ (fmt.fracWidth - S.log2) :=
          Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ (S.log2 + 1) * 2 ^ (fmt.fracWidth - S.log2) :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ = 2 ^ (fmt.fracWidth + 1) := by
          rw [← pow_add]
          congr 1
          omega

/-- A value in `[2^f, 2^(f + 1)]` equals `2^(f + 1)` exactly when its leading bit is at `f + 1`. -/
theorem log2_eq_succ_iff (rounded f : Nat) (hlow : 2 ^ f ≤ rounded) (hhigh : rounded ≤ 2 ^ (f + 1)) :
    rounded.log2 = f + 1 ↔ rounded = 2 ^ (f + 1) := by
  have hne : rounded ≠ 0 := by
    have := Nat.two_pow_pos f
    omega
  constructor
  · intro hlog
    have := Nat.log2_self_le hne
    rw [hlog] at this
    omega
  · intro heq
    rw [heq, Nat.log2_two_pow]

/-! ## The limb kernel computes the specification -/

/-- An accepted limb rounding is the natural-number specification on the significand's value. -/
theorem roundNormal?_map_toModel (hexp : fmt.expWidth ≤ 32) (sign : Bool) (S : LimbArray)
    (jam scale : Nat) (hS : S.toNat ≠ 0) :
    (roundNormal? fmt sign S jam scale).map toModel = roundJammed fmt sign S.toNat jam scale := by
  unfold roundNormal? roundJammed
  rw [LimbArray.log2_eq S hS]
  dsimp only
  by_cases hsub : S.toNat.log2 + jam + scale < fmt.bias + 2 * fmt.fracWidth - 1
  · rw [ite_eq_left hsub, ite_eq_left hsub]
    rfl
  · rw [ite_eq_right hsub, ite_eq_right hsub]
    set roundedLimbs :=
      if fmt.fracWidth ≤ S.toNat.log2 then
        S.roundShiftRightEven (S.toNat.log2 - fmt.fracWidth)
      else
        S.shiftLeft (fmt.fracWidth - S.toNat.log2) with hroundedLimbs
    set rounded :=
      if fmt.fracWidth ≤ S.toNat.log2 then
        Numerics.roundShiftRightEven S.toNat (S.toNat.log2 - fmt.fracWidth)
      else
        S.toNat * 2 ^ (fmt.fracWidth - S.toNat.log2) with hrounded
    have hvalue : roundedLimbs.toNat = rounded := by
      rw [hroundedLimbs, hrounded]
      split
      · rw [LimbArray.toNat_roundShiftRightEven]
      · rw [LimbArray.toNat_shiftLeft]
    obtain ⟨hlow, hhigh⟩ := rounded_bounds (fmt := fmt) S.toNat hS
    have hroundedNe : rounded ≠ 0 := by
      have := Nat.two_pow_pos fmt.fracWidth
      omega
    have hcarry : (roundedLimbs.log2 == fmt.fracWidth + 1) = decide (rounded = 2 ^ (fmt.fracWidth + 1)) := by
      rw [LimbArray.log2_eq _ (by rw [hvalue]; exact hroundedNe), hvalue]
      apply Bool.eq_iff_iff.mpr
      rw [beq_iff_eq, decide_eq_true_iff]
      exact log2_eq_succ_iff rounded fmt.fracWidth hlow hhigh
    rw [hcarry]
    simp only [decide_eq_true_eq]
    by_cases hover : 3 * fmt.bias + 2 * fmt.fracWidth - 2 <
        (if rounded = 2 ^ (fmt.fracWidth + 1) then S.toNat.log2 + jam + scale + 1
          else S.toNat.log2 + jam + scale)
    · rw [ite_eq_left hover, ite_eq_left hover]
      rfl
    · rw [ite_eq_right hover, ite_eq_right hover, Option.map_some]
      congr 1
      have hexpLt : (if rounded = 2 ^ (fmt.fracWidth + 1) then S.toNat.log2 + jam + scale + 1
          else S.toNat.log2 + jam + scale) - (fmt.bias + 2 * fmt.fracWidth - 2) <
            2 ^ fmt.expWidth := by
        have hbias := FloatFormat.two_pow_expWidth_eq_two_mul_bias_add_two fmt
        omega
      have hexpWord : (UInt32.ofNat ((if rounded = 2 ^ (fmt.fracWidth + 1) then
          S.toNat.log2 + jam + scale + 1 else S.toNat.log2 + jam + scale) -
            (fmt.bias + 2 * fmt.fracWidth - 2))).toNat =
          (if rounded = 2 ^ (fmt.fracWidth + 1) then S.toNat.log2 + jam + scale + 1
            else S.toNat.log2 + jam + scale) - (fmt.bias + 2 * fmt.fracWidth - 2) := by
        rw [UInt32.toNat_ofNat']
        apply Nat.mod_eq_of_lt
        exact lt_of_lt_of_le hexpLt (Nat.pow_le_pow_right (by decide) hexp)
      rw [toModel_pack_of_lt _ _ _ hexp (by rw [hexpWord]; exact hexpLt)
        (by rw [LimbArray.toNat_lowBits]; exact Nat.mod_lt _ (Nat.two_pow_pos _)), hexpWord,
        LimbArray.toNat_lowBits, hvalue]

/-! ## The specification refines the exact rounder -/

/-- `shiftRightJam` by zero bits is the identity. -/
theorem shiftRightJam_zero (T : Nat) : shiftRightJam T 0 = T := by
  unfold shiftRightJam
  simp [Nat.mod_one]

/--
An accepted `roundJammed` result on `shiftRightJam exact jam` is the exact rounder on `exact`.

The hypothesis `2 ^ (fracWidth + jam + 2) ≤ exact` (vacuous for `jam = 0`) is what
`roundShiftRightEven_shiftRightJam` needs: at least the guard bit and one more bit of the rounded
quotient lie above the jammed position.
-/
theorem round_eq_of_roundJammed (sign : Bool) (exact jam scale : Nat) (hexact : exact ≠ 0)
    (hjam : jam = 0 ∨ 2 ^ (fmt.fracWidth + jam + 2) ≤ exact) (result : Model fmt)
    (hresult : roundJammed fmt sign (shiftRightJam exact jam) jam scale = some result) :
    FiniteProductRound.round fmt sign exact scale = result := by
  have hnormalize : ∀ S : Nat, S ≠ 0 → S.log2 + jam = exact.log2 →
      (fmt.fracWidth ≤ S.log2 →
        Numerics.roundShiftRightEven S (S.log2 - fmt.fracWidth) =
          Numerics.roundShiftRightEven exact (exact.log2 - fmt.fracWidth)) →
      (¬ fmt.fracWidth ≤ S.log2 → S = exact ∧ jam = 0) →
      roundJammed fmt sign S jam scale = some result →
      FiniteProductRound.round fmt sign exact scale = result := by
    intro S hS hleading hround hshift hres
    unfold roundJammed at hres
    dsimp only at hres
    rw [hleading] at hres
    unfold FiniteProductRound.round
    simp only [beq_iff_eq, hexact, ite_false]
    by_cases hsub : exact.log2 + scale < fmt.bias + 2 * fmt.fracWidth - 1
    · rw [ite_eq_left hsub] at hres
      exact absurd hres (by simp)
    · rw [ite_eq_right hsub] at hres
      rw [ite_eq_right hsub]
      have hrounded :
          (if fmt.fracWidth ≤ S.log2 then Numerics.roundShiftRightEven S (S.log2 - fmt.fracWidth)
            else S * 2 ^ (fmt.fracWidth - S.log2)) =
          (if fmt.fracWidth ≤ exact.log2 then Numerics.roundShiftRightEven exact (exact.log2 - fmt.fracWidth)
            else exact <<< (fmt.fracWidth - exact.log2)) := by
        by_cases hle : fmt.fracWidth ≤ S.log2
        · rw [ite_eq_left hle, ite_eq_left (by omega), hround hle]
        · obtain ⟨hSeq, hjam0⟩ := hshift hle
          rw [hjam0, Nat.add_zero] at hleading
          rw [ite_eq_right hle, ite_eq_right (by omega), Nat.shiftLeft_eq, hleading, hSeq]
      rw [hrounded] at hres
      rw [pow2_eq_two_pow, pow2_eq_two_pow]
      set rounded := (if fmt.fracWidth ≤ exact.log2 then
        Numerics.roundShiftRightEven exact (exact.log2 - fmt.fracWidth)
          else exact <<< (fmt.fracWidth - exact.log2)) with hroundedDef
      by_cases hover : 3 * fmt.bias + 2 * fmt.fracWidth - 2 <
          (if rounded = 2 ^ (fmt.fracWidth + 1) then exact.log2 + scale + 1 else exact.log2 + scale)
      · rw [ite_eq_left hover] at hres
        exact absurd hres (by simp)
      · rw [ite_eq_right hover] at hres
        rw [ite_eq_right hover]
        rw [Option.some.injEq] at hres
        rw [← hres]
        congr 1
        by_cases hcarry : rounded = 2 ^ (fmt.fracWidth + 1)
        · rw [ite_eq_left hcarry, hcarry, Nat.sub_self, pow_succ, Nat.mul_mod_right]
        · rw [ite_eq_right hcarry]
          have hbounds := rounded_bounds (fmt := fmt) exact hexact
          simp only at hbounds
          rw [Nat.shiftLeft_eq] at hroundedDef
          rw [hroundedDef] at hcarry ⊢
          have hlow := hbounds.1
          have hhigh := hbounds.2
          have hlt : (if fmt.fracWidth ≤ exact.log2 then
              Numerics.roundShiftRightEven exact (exact.log2 - fmt.fracWidth)
                else exact * 2 ^ (fmt.fracWidth - exact.log2)) < 2 ^ (fmt.fracWidth + 1) :=
            lt_of_le_of_ne hhigh hcarry
          rw [Nat.mod_eq_sub_mod hlow, Nat.mod_eq_of_lt]
          rw [pow_succ] at hlt
          omega
  rcases hjam with hjam0 | hbig
  · subst hjam0
    rw [shiftRightJam_zero] at hresult
    exact hnormalize exact hexact (Nat.add_zero _) (fun _ => rfl) (fun _ => ⟨rfl, rfl⟩) hresult
  · have hlog : (shiftRightJam exact jam).log2 = exact.log2 - jam := by
      apply log2_shiftRightJam
      exact le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hbig
    have hexactLog : fmt.fracWidth + jam + 2 ≤ exact.log2 := by
      rw [Nat.le_log2 hexact]
      exact hbig
    have hSne : shiftRightJam exact jam ≠ 0 := by
      intro hzero
      have := Nat.log2_zero
      rw [hzero, Nat.log2_zero] at hlog
      omega
    apply hnormalize (shiftRightJam exact jam) hSne (by omega)
    · intro _
      rw [hlog, show exact.log2 - jam - fmt.fracWidth = (exact.log2 - fmt.fracWidth) - jam by omega]
      exact roundShiftRightEven_shiftRightJam exact jam (exact.log2 - fmt.fracWidth) (by omega)
    · intro hnot
      exfalso
      apply hnot
      rw [hlog]
      omega
    · exact hresult

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
