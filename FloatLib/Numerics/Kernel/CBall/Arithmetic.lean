/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.BallProof
public import FloatLib.Numerics.Kernel.CBall

import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Component arithmetic for complex balls

Each component operation encloses the corresponding operation over an ordered field. The real-ball
widening and smallness guarantees supply the component bounds used in complex arithmetic and
exponential enclosures.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

open scoped Nat

namespace Ball

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A number within `r / 2 ^ s` of zero is a member of `error r s`. -/
theorem contains_error {r s : Nat} {e : K} (h : |e| ≤ (r : K) / 2 ^ s) :
    (error r s).Contains e := by
  rw [error, contains_mk]
  simpa using h

/-- A member moved by at most `r / 2 ^ s` is a member of the widened ball. -/
theorem contains_widen {x : Ball} {v e : K} {r s : Nat} (hv : x.Contains v)
    (he : |e| ≤ (r : K) / 2 ^ s) : (x.widen r s).Contains (v + e) :=
  contains_add hv (contains_error he)

/-- A passed `within j` bounds every member by `2 ^ (-j)`. -/
theorem within_sound {x : Ball} {j : Nat} (h : x.within j = true) {v : K} (hv : x.Contains v) :
    |v| ≤ 1 / 2 ^ j := by
  have h' : x.upper.le ⟨1, 0, j⟩ = true ∧ Dyad.le ⟨0, 1, j⟩ x.lower = true := by
    simpa [within] using h
  obtain ⟨hlo, hhi⟩ := (contains_iff x v).1 hv
  have hupper := Dyad.le_cast (K := K) h'.1
  have hlower := Dyad.le_cast (K := K) h'.2
  have e1 : ((Dyad.mk 1 0 j).toRat : K) = 1 / 2 ^ j := by
    simp [Dyad.toRat_mk]
  have e2 : ((Dyad.mk 0 1 j).toRat : K) = -(1 / 2 ^ j) := by
    simp [Dyad.toRat_mk, neg_div]
  rw [e1] at hupper
  rw [e2] at hlower
  rw [abs_le]
  exact ⟨hlower.trans hlo, hhi.trans hupper⟩

/-- A number of absolute value at most one is a member of `unit`. -/
theorem contains_unit {v : K} (h : |v| ≤ 1) : unit.Contains v := by
  rw [unit, contains_mk]
  simpa using h

end Ball

namespace CBall

section Field

variable {K : Type*} [Field K] [LinearOrder K]

/-- `a` is a member of the real part of `z` and `b` of its imaginary part. -/
def Contains (z : CBall) (a b : K) : Prop := z.re.Contains a ∧ z.im.Contains b

/-- The negation of a member is a member of the negation. -/
theorem contains_neg {x : CBall} {a b : K} (hx : x.Contains a b) : x.neg.Contains (-a) (-b) :=
  ⟨Ball.contains_neg hx.1, Ball.contains_neg hx.2⟩

/-- The conjugate of a member is a member of the conjugate. -/
theorem contains_conj {x : CBall} {a b : K} (hx : x.Contains a b) : x.conj.Contains a (-b) :=
  ⟨hx.1, Ball.contains_neg hx.2⟩

/-- `i` times a member, `-b + i a`, is a member of `mulI`. -/
theorem contains_mulI {x : CBall} {a b : K} (hx : x.Contains a b) : x.mulI.Contains (-b) a :=
  ⟨Ball.contains_neg hx.2, hx.1⟩

variable [IsStrictOrderedRing K]

/-- A member of a real ball, with imaginary part zero. -/
theorem contains_ofReal {x : Ball} {a : K} (h : x.Contains a) : (ofReal x).Contains a 0 := by
  refine ⟨h, ?_⟩
  change (Ball.ofNat 0).Contains (0 : K)
  exact_mod_cast Ball.contains_ofNat (K := K) 0

/-- A natural number is a member of its ball. -/
theorem contains_ofNat (n : Nat) : (ofNat n).Contains (n : K) 0 := by
  refine ⟨Ball.contains_ofNat n, ?_⟩
  change (Ball.ofNat 0).Contains (0 : K)
  exact_mod_cast Ball.contains_ofNat (K := K) 0

/-- A sum of members is a member of the sum. -/
theorem contains_add {x y : CBall} {a b c d : K} (hx : x.Contains a b) (hy : y.Contains c d) :
    (x.add y).Contains (a + c) (b + d) :=
  ⟨Ball.contains_add hx.1 hy.1, Ball.contains_add hx.2 hy.2⟩

/-- A difference of members is a member of the difference. -/
theorem contains_sub {x y : CBall} {a b c d : K} (hx : x.Contains a b) (hy : y.Contains c d) :
    (x.sub y).Contains (a - c) (b - d) := by
  simpa only [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

/-- A product of members, `(a + i b) (c + i d)`, is a member of the product. -/
theorem contains_mul {x y : CBall} {a b c d : K} (hx : x.Contains a b) (hy : y.Contains c d) :
    (x.mul y).Contains (a * c - b * d) (a * d + b * c) :=
  ⟨Ball.contains_sub (Ball.contains_mul hx.1 hy.1) (Ball.contains_mul hx.2 hy.2),
    Ball.contains_add (Ball.contains_mul hx.1 hy.2) (Ball.contains_mul hx.2 hy.1)⟩

/-- A member scaled by a member of a real ball is a member of the scaled ball. -/
theorem contains_smul {c : Ball} {x : CBall} {r a b : K} (hc : c.Contains r)
    (hx : x.Contains a b) : (smul c x).Contains (r * a) (r * b) :=
  ⟨Ball.contains_mul hc hx.1, Ball.contains_mul hc hx.2⟩

/-- Rounding keeps every member. -/
theorem contains_round {x : CBall} {a b : K} (hx : x.Contains a b) (p : Nat) :
    (x.round p).Contains a b :=
  ⟨Ball.contains_round hx.1 p, Ball.contains_round hx.2 p⟩

end Field

end CBall
end FloatLib.Numerics.Kernel
