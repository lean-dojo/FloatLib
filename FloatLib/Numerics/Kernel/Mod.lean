/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits

/-!
# Modular powers and inverses for Lean's kernel

A modular power by repeated squaring takes one interpreted step per bit of the exponent, and at
12 to 13 µs per step (Lean v4.36.0) the steps cost more than the multiplications until the modulus
has a few thousand bits. `powModWindow w a e n` takes `w + 1` bits of the exponent per step: it
raises the running base to the power `2 ^ (w + 1)` and to the power of the next digit with the
kernel's own `Nat.pow`, on numbers of up to `2 ^ (w + 1)` times the size of the modulus, and
reduces once. With `w = 0` it is the usual binary method.

`powMod a e n` picks the window from the size of the modulus: four bits per step below
`2 ^ 1280` and two bits above. Measured on Lean v4.36.0 against the binary method (`w = 0`), that
is about 3 times faster at 64 and at 256 bits, 2 times at 1,024 bits and 1.2 times at 4,096 bits.

The count of the recursion is the exponent plus one, as a literal. The kernel only steps through
as many levels as the exponent has digits, so no bit length is needed.

`invMod a n` is the inverse of `a` modulo `n` by the extended Euclidean algorithm, with residues
in place of signed cofactors, and `isInvMod a x n` checks an inverse that is given.

The theorems are in `FloatLib.Numerics.Kernel.ModProof`: `powModWindow_eq` and `powMod_eq`
(`a ^ e % n`, for all arguments), `invMod_spec` (for coprime `a` and `n`). The loops count down a
literal with `Nat.rec` and have no compiled code of their own; a module that imports `ModProof`
compiles them as the loops `Compiled.powMod` and `Compiled.invMod` (`powMod_eq_compiled`,
`invMod_eq_compiled`).
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/--
`a ^ e % n`, taking `w + 1` bits of the exponent per step (`powModWindow_eq`). The state is the
running base `a ^ (2 ^ ((w + 1) * i)) % n`, the exponent with its lowest `i` digits removed, and
the product of the powers of the digits seen so far.
-/
noncomputable def powModWindow (w a e n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ step base e acc =>
      Bool.rec (motive := fun _ => Nat)
        (step (Nat.mod (Nat.pow base (Nat.shiftLeft 1 (Nat.succ w))) n)
          (Nat.shiftRight e (Nat.succ w))
          (Nat.mod
            (Nat.mul acc (Nat.pow base (Nat.land e (Nat.sub (Nat.shiftLeft 1 (Nat.succ w)) 1))))
            n))
        acc
        (Nat.beq e 0))
    (Nat.succ e) (Nat.mod a n) e (Nat.mod 1 n)

/--
`a ^ e % n` (`powMod_eq`), with the window chosen from the size of the modulus: four bits per
step for `n < 2 ^ 1280` and two bits above, which is where the measured costs cross.
-/
noncomputable def powMod (a e n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (powModWindow 1 a e n) (powModWindow 3 a e n)
    (Nat.beq (Nat.shiftRight n 1280) 0)

/-- Whether `x` is an inverse of `a` modulo `n`: `a * x % n = 1 % n`. -/
def isInvMod (a x n : Nat) : Bool := Nat.beq (Nat.mod (Nat.mul a x) n) (Nat.mod 1 n)

/--
The inverse of `a` modulo `n` when they are coprime (`invMod_spec`), by the extended Euclidean
algorithm. The state is two consecutive remainders `r₀`, `r₁` of the division chain of `n` and
`a % n`, and residues `s₀`, `s₁` with `rᵢ ≡ sᵢ * a` modulo `n`. The count is `a % n + 1`, since
the remainders decrease.
-/
noncomputable def invMod (a n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) (fun _ _ s₀ _ => s₀)
    (fun _ step r₀ r₁ s₀ s₁ =>
      Bool.rec (motive := fun _ => Nat)
        (step r₁ (Nat.mod r₀ r₁) s₁
          (Nat.mod (Nat.add s₀ (Nat.sub n (Nat.mod (Nat.mul (Nat.div r₀ r₁) s₁) n))) n))
        s₀
        (Nat.beq r₁ 0))
    (Nat.succ (Nat.mod a n)) n (Nat.mod a n) 0 (Nat.mod 1 n)

end FloatLib.Numerics.Kernel
