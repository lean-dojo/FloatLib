/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Runtime

/-!
# Exponent range of E8M0 scales

Every finite E8M0 scale has an exponent in `[-127, 127]`, and saturating encoding decodes to the
clamped exponent. The scale selection of OCP MX blocks is `Standard.format`, whose theorems are in
`Standard.Format`.
-/

public section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Numerics

/-- Every finite E8M0 scale has a bounded exponent. -/
theorem E8M0.exponent?_bounds {scale : E8M0} {exponent : Int}
    (h : scale.exponent? = some exponent) : -127 ≤ exponent ∧ exponent ≤ 127 := by
  have hbits := scale.isLt
  unfold E8M0.exponent? E8M0.isNaN E8M0.bias at h
  split at h
  · contradiction
  · rename_i hfinite
    simp only [Option.some.injEq] at h
    simp only [beq_iff_eq] at hfinite
    subst exponent
    change scale.toNat < 256 at hbits
    simp only [Int.ofNat_eq_natCast]
    omega

/-- Saturating E8M0 encoding decodes to the clamped mathematical exponent. -/
@[simp] theorem E8M0.exponent?_ofExponentSaturating (exponent : Int) :
    (E8M0.ofExponentSaturating exponent).exponent? =
      some (max (-127) (min 127 exponent)) := by
  let clamped := Numerics.Quantization.Saturating.clamp (-127) 127 exponent
  have hlo : -127 ≤ clamped := Numerics.Quantization.Saturating.lower_le_clamp _ _ _
  have hhi : clamped ≤ 127 := Numerics.Quantization.Saturating.clamp_le_upper (by norm_num)
  have hcode : (clamped + 127).toNat < 256 := by omega
  have hnotnan : (clamped + 127).toNat ≠ 255 := by omega
  change (if (BitVec.ofNat 8 (clamped + 127).toNat).toNat == 255 then none
    else some ((BitVec.ofNat 8 (clamped + 127).toNat).toNat - (127 : Int))) = some clamped
  simp only [BitVec.toNat_ofNat, show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt hcode]
  simp [hnotnan, Int.toNat_of_nonneg (by omega : 0 ≤ clamped + 127)]

end FloatLib.Floats.Formats.OCP.MX
