/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.CFix
public import FloatLib.Numerics.Kernel.Seq

/-!
# Sums of a completely multiplicative function

For a function with `f 1 = 1` and `f (p * m) = f p * f m`, the values at the integers
`1, …, ν` need a direct evaluation only at the primes: every other value is a product. The sum
needs still fewer products when the integers are split as `n = a * r`, with `a` a product of small
primes and `r` a product of large ones:

  `∑ {n ≤ ν} f n = ∑ₐ f a * ∑ {r ≤ ν / a} f r`.

The values `f r` are formed once, in increasing order of `r`, and added up into running sums. The
products `a` form a forest (the children of `a` are the `p * a ≤ ν` for the small primes `p` up to
the smallest prime factor of `a`), and a walk through it takes one product for the value of each
`a` and one with the running sum of the `r` that `a` pairs with.

The products are those of `CFix` and the sums are `CSum`s. The running sums are read through the
shared `Seq.getD` lookup. The value at a prime `p` is asked from a
function `zp` through `strict`, so the kernel computes it once, however many products use it.

Nothing about primes is trusted or proved. A `Split` is the forest of the `a`, each node with the
number `c` of the `r` it pairs with, and the `r` are given as the list of their lists of factors.
`splitOk` checks, with a set of bits, that the products `a * r` of all pairs are exactly
`1, …, ν`, each once, and the theorems of `FloatLib.Numerics.Kernel.MultiplicativeProof` take that
check as their premise. So a split may come from any source.

## Main definitions

* `Split`, `Split.total`: the forest and the sum over all pairs.
* `Split.splitOk plan rough c₁ ν`: the pairs are exactly `1, …, ν`.
* `Cover`: a split for a bound `ν` together with the proof of `splitOk`. `cover% ν y`
  (`FloatLib.Tactic.Cover`) writes one out as a literal for the small
  primes up to `y`, and the kernel checks its proof.
* `Cover.total`, `Cover.find`: the sum for a cover, and the cover for a bound in a list.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- A forest of products of small factors: a node multiplies its parent by `p` and is paired
with the first `c` members of a list of values. -/
inductive Split where
  /-- The empty forest. -/
  | nil : Split
  /-- A node for the factor `p`, its count `c`, the forest below it and its later siblings. -/
  | node (p c : Nat) (sub rest : Split) : Split

namespace Split

/-- The value of a product of factors: one for no factor, `zp q` for one, and the value of the
first factor times the value of the others otherwise. The value of the others is the recursive
value of the recursor, so the kernel has it already when the others are the factors of a number
it has met: with ascending factor lists of `1, …, n`, each composite costs one product. -/
noncomputable def prodOf (s : Nat) (zp : Nat → CFix) (l : List Nat) : CFix :=
  List.rec (motive := fun _ => CFix) (CFix.one s)
    (fun q rest ih =>
      List.rec (motive := fun _ => CFix) (strict q zp)
        (fun _ _ _ => CFix.mul s (strict q zp) ih) rest)
    l

/-- The running sums of the values of a list of factor lists, after `S`: entry `c` is `S` plus the
first `c` values. -/
noncomputable def cums (s : Nat) (zp : Nat → CFix) : List (List Nat) → CSum → List CSum
  | [], S => [S]
  | r :: rest, S => S :: cums s zp rest (CSum.push (prodOf s zp r) S)

/-- The sum over all pairs of the nodes below a node with the value `zm`: the value of a node
times the running sum `cs` at its count. -/
noncomputable def walk (s : Nat) (zp : Nat → CFix) (cs : List CSum) (plan : Split) :
    CFix → CSum :=
  Split.rec (motive := fun _ => CFix → CSum)
    (fun _ => CSum.zero)
    (fun p c _ _ ihs ihr zm =>
      (fun z => CSum.add (CSum.scale s z (Seq.getD cs c CSum.bad)) (CSum.add (ihs z) (ihr zm)))
        (CFix.mul s (strict p zp) zm))
    plan

/-- The sum over all pairs: the first `c₁` values themselves, for the factor one, and the walk
over the forest. -/
noncomputable def total (s : Nat) (zp : Nat → CFix) (rough : List (List Nat)) (c₁ : Nat)
    (plan : Split) : CSum :=
  (fun cs => CSum.add (Seq.getD cs c₁ CSum.bad) (walk s zp cs plan (CFix.one s))) (cums s zp
    rough CSum.zero)

/-- The integers of the pairs of the nodes below `m`. -/
def pairs (rough : List (List Nat)) : Split → Nat → List Nat
  | nil, _ => []
  | node p c sub rest, m =>
    ((rough.take c).map fun r => Nat.mul (Nat.mul p m) (List.prod r)) ++
      (pairs rough sub (Nat.mul p m) ++ pairs rough rest m)

/-- The integers of all pairs. -/
def allPairs (rough : List (List Nat)) (c₁ : Nat) (plan : Split) : List Nat :=
  (rough.take c₁).map List.prod ++ pairs rough plan 1

/-- Whether the list has `count` members, all in `[lo, ν]` and none in the set of bits `seen` or
twice in the list. -/
def cover (lo ν : Nat) : List Nat → Nat → Nat → Bool
  | [], _, count => Nat.beq count 0
  | n :: l, seen, count =>
    Bool.and (Bool.and (Nat.ble lo n) (Nat.ble n ν))
      (Bool.and (Nat.beq (bit seen n) 0)
        (Bool.and (Nat.ble 1 count)
          (cover lo ν l (Nat.lor seen (Nat.shiftLeft 1 n)) (Nat.sub count 1))))

/-- Whether the integers of all pairs are exactly `1, …, ν`, each once. -/
def splitOk (plan : Split) (rough : List (List Nat)) (c₁ ν : Nat) : Bool :=
  cover 1 ν (allPairs rough c₁ plan) 0 ν

end Split

/-- A split of the integers `1, …, ν` that passed the check: the forest of the products of small
factors, the factor lists of the other integers, the number of them that pair with the factor one,
and the proof of `Split.splitOk`. -/
structure Cover where
  /-- The bound. -/
  ν : Nat
  /-- The forest of the products of small factors, each node with its count. -/
  plan : Split
  /-- The factor lists of the integers without a small factor, in increasing order. -/
  rough : List (List Nat)
  /-- The number of those integers up to `ν`. -/
  count : Nat
  /-- The pairs are exactly `1, …, ν`, each once. -/
  ok : Split.splitOk plan rough count ν = true

namespace Cover

/-- The sum of the values at `1, …, ν` (`Cover.total_contains`). -/
noncomputable def total (s : Nat) (zp : Nat → CFix) (c : Cover) : CSum :=
  Split.total s zp c.rough c.count c.plan

/-- The first cover in the list for the bound `ν`. -/
def find (ν : Nat) : List Cover → Option Cover
  | [] => none
  | c :: rest =>
    Bool.casesOn (motive := fun _ => Option Cover) (Nat.beq c.ν ν) (find ν rest) (some c)

end Cover

end FloatLib.Numerics.Kernel
