/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.CBall.Arithmetic
public import Mathlib.Basic.Complex.Basic

import Mathlib.Tactic.IntervalCases

/-!
# Complex arithmetic enclosed by complex balls

Complex membership specializes component containment to real and imaginary parts. Addition,
multiplication, conjugation, scaling and rounding preserve membership. Powers of the imaginary
unit use its period four.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

open scoped Nat

namespace CBall

/-- The complex number `w` is a member of `z`: its parts are members of the parts of `z`. -/
def Mem (z : CBall) (w : ℂ) : Prop := z.Contains w.re w.im

/-- Membership of a complex number given by its parts. -/
theorem mem_mk {z : CBall} {a b : ℝ} (h : z.Contains a b) : z.Mem ⟨a, b⟩ := h

/-- A member of a real ball is a member of its complex ball. -/
theorem mem_ofReal {x : Ball} {a : ℝ} (h : x.Contains a) : (ofReal x).Mem (a : ℂ) :=
  contains_ofReal h

/-- A natural number is a member of its complex ball. -/
theorem mem_ofNat (n : Nat) : (ofNat n).Mem (n : ℂ) := by
  simpa [Mem] using contains_ofNat (K := ℝ) n

/-- A sum of members is a member of the sum. -/
theorem mem_add {x y : CBall} {z w : ℂ} (hx : x.Mem z) (hy : y.Mem w) : (x.add y).Mem (z + w) :=
  contains_add hx hy

/-- The negation of a member is a member of the negation. -/
theorem mem_neg {x : CBall} {z : ℂ} (hx : x.Mem z) : x.neg.Mem (-z) :=
  contains_neg hx

/-- A difference of members is a member of the difference. -/
theorem mem_sub {x y : CBall} {z w : ℂ} (hx : x.Mem z) (hy : y.Mem w) : (x.sub y).Mem (z - w) :=
  contains_sub hx hy

/-- The conjugate of a member is a member of the conjugate. -/
theorem mem_conj {x : CBall} {z : ℂ} (hx : x.Mem z) : x.conj.Mem (starRingEnd ℂ z) :=
  contains_conj hx

/-- A product of members is a member of the product. -/
theorem mem_mul {x y : CBall} {z w : ℂ} (hx : x.Mem z) (hy : y.Mem w) : (x.mul y).Mem (z * w) := by
  simpa only [Mem, Complex.mul_re, Complex.mul_im] using contains_mul hx hy

/-- A member scaled by a member of a real ball is a member of the scaled ball. -/
theorem mem_smul {c : Ball} {x : CBall} {r : ℝ} {z : ℂ} (hc : c.Contains r) (hx : x.Mem z) :
    (smul c x).Mem ((r : ℂ) * z) := by
  simpa [Mem, Complex.mul_re, Complex.mul_im] using contains_smul hc hx

/-- `i` times a member is a member of `mulI`. -/
theorem mem_mulI {x : CBall} {z : ℂ} (hx : x.Mem z) : x.mulI.Mem (Complex.I * z) := by
  simpa [Mem, Complex.mul_re, Complex.mul_im] using contains_mulI hx

/-- Rounding keeps every member. -/
theorem mem_round {x : CBall} {z : ℂ} (hx : x.Mem z) (p : Nat) : (x.round p).Mem z :=
  contains_round hx p

/-- `i ^ k` times a member is a member of `mulIPow k`. -/
theorem mem_mulIPow (k : Nat) {x : CBall} {z : ℂ} (hx : x.Mem z) :
    (mulIPow k x).Mem (Complex.I ^ k * z) := by
  rw [Complex.I_pow_eq_pow_mod]
  have hlt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hdef : mulIPow k x =
      Nat.casesOn (motive := fun _ => CBall) (k % 4) x
        (fun a => Nat.casesOn (motive := fun _ => CBall) a (⟨x.im.neg, x.re⟩ : CBall)
          (fun b => Nat.casesOn (motive := fun _ => CBall) b (⟨x.re.neg, x.im.neg⟩ : CBall)
            (fun _ => (⟨x.im, x.re.neg⟩ : CBall)))) := rfl
  rw [hdef]
  generalize k % 4 = r at hlt ⊢
  interval_cases r
  · simpa using hx
  · change x.mulI.Mem (Complex.I ^ 1 * z)
    simpa using mem_mulI hx
  · change x.neg.Mem (Complex.I ^ 2 * z)
    simpa using mem_neg hx
  · change (⟨x.im, x.re.neg⟩ : CBall).Mem (Complex.I ^ 3 * z)
    simpa [Mem, Contains, neg, mulI, Ball.neg] using mem_neg (mem_mulI hx)

end CBall
end FloatLib.Numerics.Kernel
