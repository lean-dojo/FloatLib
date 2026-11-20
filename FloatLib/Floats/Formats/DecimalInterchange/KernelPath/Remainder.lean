/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Quantum
public import FloatLib.Floats.Formats.DecimalInterchange.Remainder.Runtime

/-!
# Kernel path of decimal `remainder`

`Arithmetic.remainder` (IEEE 754-2019 §5.3.1) puts two finite operands on their common quantum,
the smaller of the two, divides the two integer coefficients, and delivers the remainder of the
nearest integer quotient, ties to even, at that quantum.

`remainderFinite` computes this on natural numbers: the two quantum exponents are compared once,
by cases on their constructors (`KernelPath.gaps`), the coefficients are scaled by the powers
of ten of the two distances, and the rounding of the quotient is three comparisons of natural
numbers. `remainderFinite_eq` proves it equal to `Arithmetic.remainderFinite`. `remainder_eq`,
tagged `@[kernel_optimize]`, proves the kernel form `remainder` equal to `Arithmetic.remainder`
for every format and all data; a NaN, an infinity and a zero divisor are left to the
specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics

/--
Kernel form of `Arithmetic.remainderFinite` (`remainderFinite_eq`): the remainder of the
nearest integer quotient of two coefficients on their common quantum, ties to even, with the
sign of the dividend when the quotient was rounded down and the opposite sign otherwise.
-/
def remainderFinite (sx : Bool) (cx : Nat) (qx : Int) (cy : Nat) (qy : Int) : Datum :=
  gaps qx qy fun above below =>
    (fun a b =>
      (fun r =>
        (fun up =>
          Datum.finite (differ sx up)
            (Bool.casesOn (motive := fun _ => Nat) up r (Nat.sub b r))
            (Bool.casesOn (motive := fun _ => Int) (Nat.beq above 0) qy qx))
          (Bool.or (Nat.ble (Nat.succ b) (Nat.add r r))
            (Bool.and (Nat.beq b (Nat.add r r)) (Nat.beq (Nat.mod (Nat.div a b) 2) 1))))
        (Nat.mod a b))
      (Nat.mul cx (Nat.pow 10 above)) (Nat.mul cy (Nat.pow 10 below))

/-- `remainderFinite` is `Arithmetic.remainderFinite`, for all operands. -/
theorem remainderFinite_eq (sx : Bool) (cx : Nat) (qx : Int) (cy : Nat) (qy : Int) :
    remainderFinite sx cx qx cy qy = Arithmetic.remainderFinite sx cx qx cy qy := by
  have habove : (qx - min qx qy).toNat = (qx - qy).toNat := by omega
  have hbelow : (qy - min qx qy).toNat = (qy - qx).toNat := by omega
  have hquantum : Bool.casesOn (motive := fun _ => Int) (Nat.beq (qx - qy).toNat 0) qy qx =
      min qx qy := by
    rw [natBeq_eq, casesOn_decide]
    split_ifs <;> omega
  have hup : ∀ a b : Nat,
      Bool.or (Nat.ble (Nat.succ b) (Nat.add (Nat.mod a b) (Nat.mod a b)))
          (Bool.and (Nat.beq b (Nat.add (Nat.mod a b) (Nat.mod a b)))
            (Nat.beq (Nat.mod (Nat.div a b) 2) 1)) =
        Arithmetic.remainderRoundUp a b := by
    intro a b
    have hmod : ∀ m n : Nat, Nat.mod m n = m % n := fun _ _ => rfl
    have hdiv : ∀ m n : Nat, Nat.div m n = m / n := fun _ _ => rfl
    unfold Arithmetic.remainderRoundUp
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, decide_eq_true_eq,
      Nat.succ_eq_add_one, Nat.add_eq, hmod, hdiv]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, h2⟩
  unfold remainderFinite Arithmetic.remainderFinite Arithmetic.remainderCoefficient
  rw [gaps_eq]
  simp only [hup, hquantum, habove, hbelow, differ_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq]
  cases hround : Arithmetic.remainderRoundUp (cx * 10 ^ (qx - qy).toNat)
      (cy * 10 ^ (qy - qx).toNat) <;> cases sx <;> rfl

/--
Kernel form of `Arithmetic.remainder` (`remainder_eq`): `remainderFinite` for two finite data
with a nonzero divisor. A NaN, an infinity and a zero divisor are left to the specification.
-/
def remainder (f : Format) (x y : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun sx cx qx =>
      Datum.casesOn (motive := fun _ => Outcome) y
        (fun _ cy qy =>
          Bool.casesOn (motive := fun _ => Outcome) (Nat.beq cy 0)
            { value := remainderFinite sx cx qx cy qy } (Arithmetic.remainder f x y))
        (fun _ => Arithmetic.remainder f x y) (fun _ _ _ => Arithmetic.remainder f x y))
    (fun _ => Arithmetic.remainder f x y) (fun _ _ _ => Arithmetic.remainder f x y)

/--
IEEE 754-2019 §5.3.1 `remainder` on decimal data is its kernel form, for every format and all
data.
-/
@[kernel_optimize] theorem remainder_eq (f : Format) (x y : Datum) :
    Arithmetic.remainder f x y = remainder f x y := by
  rcases x with ⟨sx, cx, qx⟩ | sx | ⟨sx, tx, px⟩ <;> try rfl
  rcases y with ⟨sy, cy, qy⟩ | sy | ⟨sy, ty, py⟩ <;> try rfl
  change _ = Bool.casesOn (motive := fun _ => Outcome) (Nat.beq cy 0)
    { value := remainderFinite sx cx qx cy qy }
    (Arithmetic.remainder f (.finite sx cx qx) (.finite sy cy qy))
  rcases cy with _ | cy
  · rfl
  · rw [remainderFinite_eq]
    rfl

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
