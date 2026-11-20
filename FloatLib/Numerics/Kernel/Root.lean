/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits

/-!
# Integer roots for Lean's kernel: compute by Newton steps, then check

The floor of a `k`-th root is the one number `r` with `r ^ k ≤ n < (r + 1) ^ k`, and the kernel
checks that with two powers and two comparisons (`isRoot`), all native. So a root never has to be
trusted or proved to converge: `rootGuess k n` runs Newton's iteration from the power of two just
above the root, with a count of steps taken from the bit length, and the caller checks its result.

`isqrt n` does both for square roots. It returns the Newton result when `isRoot` accepts it and
core's `Nat.sqrt n` otherwise, so `isqrt n = Nat.sqrt n` holds for every `n` whatever the
iteration does (`isqrt_eq` in `RootProof`), and the kernel takes the checked branch. For a
number of at most 384 bits it first tries `sqrtGuess`, eight Newton steps written out: a step of
the recursion of `rootGuess` costs the kernel about twelve microseconds, a written-out step
about three. `FloatLib.Numerics.IntegerRoot.newton` is defined the same way for every degree.

These functions branch with `Bool.casesOn`, which has compiled code, so they also run compiled.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- Whether `r` is the floor of the `k`-th root of `n`: `r ^ k ≤ n < (r + 1) ^ k`. -/
def isRoot (k r n : Nat) : Bool :=
  Bool.and (Nat.ble (Nat.pow r k) n) (Nat.ble (Nat.succ n) (Nat.pow (Nat.succ r) k))

/--
Newton's iteration for the `k`-th root of `n`, from `2 ^ ⌈bits / k⌉`, which is above the root:
`x ← ((k - 1) * x + n / x ^ (k - 1)) / k` as long as the value decreases, for at most two more
steps than `n` has bits. The result is meant to be checked with `isRoot`.
-/
def rootGuess (k n : Nat) : Nat :=
  (fun bits =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
      (fun _ step x =>
        (fun next =>
          Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ next) x) x (step next))
          (Nat.div (Nat.add (Nat.mul (Nat.sub k 1) x) (Nat.div n (Nat.pow x (Nat.sub k 1)))) k))
      (Nat.add bits 2) (Nat.shiftLeft 1 (ceilDiv bits k)))
    (size n)

/--
Eight steps of Newton's iteration for the square root of `n`, a number of `bits` bits, from
`2 ^ ⌈bits / 2⌉`, which is above the root: `x ← min x ((x + n / x) / 2)`, a step that never
increases the value. They are written out, with no recursion, and reach the floor of the root of
a number of up to 384 bits. The result is meant to be checked with `isRoot`.
-/
def sqrtGuess (n bits : Nat) : Nat :=
  (fun step => step (step (step (step (step (step (step (step
      (Nat.shiftLeft 1 (ceilDiv bits 2))))))))))
    (fun x => minNat x (Nat.shiftRight (Nat.add x (Nat.div n x)) 1))

/--
The floor of the square root of `n` (`isqrt_eq`). For `n` of at most 384 bits it is the result of
the eight written-out Newton steps `sqrtGuess` when that passes `isRoot`. Otherwise it is the
result of the full iteration `rootGuess` when that passes `isRoot`, and core's `Nat.sqrt n` when
it does not.
-/
def isqrt (n : Nat) : Nat :=
  (fun general =>
    (fun bits =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.ble bits 384)
        general
        ((fun r => Bool.casesOn (motive := fun _ => Nat) (isRoot 2 r n) general r)
          (sqrtGuess n bits)))
      (size n))
    ((fun r => Bool.casesOn (motive := fun _ => Nat) (isRoot 2 r n) (Nat.sqrt n) r)
      (rootGuess 2 n))

end FloatLib.Numerics.Kernel
