/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof

/-!
# Horner's rule on packed rows

Say we want a bound on `p(x) = ∑ k < n, cₖ xᵏ` for every `x` in an interval `[lo, hi]`. Put
`x = m + r cos u` with the midpoint `m = (lo + hi) / 2` and the radius `r = (hi - lo) / 2`. Then
`p(x)` is a cosine polynomial in `u` of degree `n - 1`, and everything we know about the circle
applies. That substitution is the change of variables behind Chebyshev series, and here the kernel
does it: with `z = exp (i u)` and `m = M / D`, `r = R / D`,

`(2 D) ^ (n - 1) p(x) = z ^ (1 - n) ∑ k, cₖ (R + 2 M z + R z²) ^ k (2 D z) ^ (n - 1 - k)`,

a homogeneous form in the two rows `a = [0, 2 D]` and `b = [R, 2 M, R]`. Horner's rule evaluates
it at `z = 2 ^ w` with `2 n` big-number products, and when every coefficient of the result fits in
a lane, the integer it returns is the packed Laurent row of the substituted polynomial.

## Main definitions

* `horner w n a b u`: `∑ k < n, xₖ * b ^ k * a ^ (n - 1 - k)` for the entries `xₖ` of the biased
  row `u` of `n` lanes, by Horner's rule from the top coefficient down.
* `compose a b cs`: the same form on integer rows, with the power `a ^ n` that the recursion
  carries along.

## Main statements

* `horner_eq`: at the values `eval (2 ^ w) a` and `eval (2 ^ w) b`, `horner` is the value of
  `compose`, which is the Kronecker identity once more.
* `length_compose` and `l1_compose`: the composed row has at most `(n - 1) e + 1` entries when `a`
  and `b` have at most `e + 1`, and its `l1` norm is at most `l1 cs * K ^ (n - 1)` when `l1 a` and
  `l1 b` are at most `K`.
* `entries_ofInt_horner`: under one comparison of small numbers, the biased row of `horner`
  reads back as the composed row, for rows `a` and `b` of any length. `Coeff.laurent_compose`
  says what that row is on the circle.

## Implementation notes

The kernel walks the coefficients one lane at a time, so `horner` costs a few interpreted steps
per lane plus two products of big numbers, one of them by a short row. The bound `K ^ (n - 1)`
in `l1_compose` is loose for a short interval, but it only decides the lane width, and a few spare
bits per lane cost much less than a sharper check would.

What I find neat here is that the change of basis is never trusted. The untrusted generator
computes the same composed row in Python to build its certificate, but the kernel recomputes it
from the coefficients of the goal, so a wrong basis change can't sneak into a proof. With
`[lo, hi] = [0, 1]` and `p(x) = x² - x`, for instance, `m = r = 1/2` gives `M = R = 1` and
`D = 2`, the rows `a = [0, 4]` and `b = [1, 2, 1]`, and the composed row `[1, 0, -2, 0, 1]`.
Centred at lane `2` it is `z⁻² - 2 + z² = 2 cos (2 u) - 2`, which is `(2 D) ^ 2 p(x) = 16 p(x)`.
Its centre `-2` and its other entries `1, 1` say at once that `16 p ≥ -4`, the exact minimum
`p = -1/4` at `x = 1/2`.

## References

* William George Horner, *A new method of solving numerical equations of all orders, by continuous
  approximation*, Phil. Trans. R. Soc. Lond. 109 (1819), 308–335,
  <https://doi.org/10.1098/rstl.1819.0023>.
* Lloyd N. Trefethen, *Approximation Theory and Approximation Practice*, SIAM (2013), chapter 3,
  for the substitution `x = cos u` that turns polynomials on an interval into cosine series,
  <https://people.maths.ox.ac.uk/trefethen/ATAP/>.

## Tags

Horner's rule, change of variables, Chebyshev, packed row
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-! ### Kernel program -/

/-- Horner's rule on the lanes `k - 1, …, 0` of `u`: the accumulator is multiplied by `b`, and
entry `j` enters times the running power `a ^ (k₀ - 1 - j)` of the starting count `k₀`. -/
def hornerAux (w : Nat) (a b : Int) (u : Nat) : Nat → Int → Int → Int
  | 0, acc, _ => acc
  | k + 1, acc, pw =>
    hornerAux w a b u k (Int.add (Int.mul acc b) (Int.mul (entry w k u) pw)) (Int.mul pw a)

/-- `∑ k < n, entry k * b ^ k * a ^ (n - 1 - k)` for the biased row `u` of `n` lanes. -/
def horner (w n : Nat) (a b : Int) (u : Nat) : Int := hornerAux w a b u n 0 1

/-! ### Integer rows -/

/-- The homogeneous form `∑ k, cs[k] * b ^ k * a ^ (cs.length - 1 - k)` of two rows, with the power
`a ^ cs.length`, by Horner's rule from the last coefficient down. -/
def compose (a b : List Int) (cs : List Int) : List Int × List Int :=
  cs.foldr (fun c r => (add (conv r.1 b) (smul c r.2), conv r.2 a)) ([], [1])

/-- `compose` of no coefficients is the zero row, with the power `1`. -/
@[simp] theorem compose_nil (a b : List Int) : compose a b [] = ([], [1]) := rfl

/-- One step of Horner's rule: multiply by `b` and add the next coefficient times the power. -/
theorem compose_cons (a b : List Int) (c : Int) (cs : List Int) :
    compose a b (c :: cs) =
      (add (conv (compose a b cs).1 b) (smul c (compose a b cs).2), conv (compose a b cs).2 a) :=
  rfl

/-! ### Soundness -/

private theorem hornerAux_eq (w : Nat) (a b : List Int) (u : Nat) : ∀ (k : Nat) (acc pw : List Int),
    hornerAux w (eval (2 ^ w) a) (eval (2 ^ w) b) u k (eval (2 ^ w) acc) (eval (2 ^ w) pw) =
      eval (2 ^ w) ((entries w k u).foldr
        (fun c r => (add (conv r.1 b) (smul c r.2), conv r.2 a)) (acc, pw)).1
  | 0, acc, pw => by simp [hornerAux, entries]
  | k + 1, acc, pw => by
      rw [show entries w (k + 1) u = entries w k u ++ [entry w k u] by
          simp [entries, List.range_succ],
        List.foldr_append, List.foldr_cons, List.foldr_nil, ← hornerAux_eq w a b u k]
      simp only [hornerAux, eval_add, eval_conv, eval_smul, Int.add_def, Int.mul_def]

/-- `horner` at the values of two rows is the value of `compose`, for any biased row `u`. -/
theorem horner_eq (w n : Nat) (a b : List Int) (u : Nat) :
    horner w n (eval (2 ^ w) a) (eval (2 ^ w) b) u =
      eval (2 ^ w) (compose a b (entries w n u)).1 := by
  have h := hornerAux_eq w a b u n [] [1]
  simp only [eval, Int.mul_zero, Int.add_zero] at h
  exact h

/-- The composed row is no longer than `(cs.length - 1) * e + 1` when `a` and `b` have at most
`e + 1` entries, and the power no longer than `cs.length * e + 1`. -/
theorem length_compose {a b : List Int} {e : Nat} (ha : a.length ≤ e + 1) (hb : b.length ≤ e + 1) :
    ∀ cs : List Int, (compose a b cs).1.length ≤ (cs.length - 1) * e + 1 ∧
      (compose a b cs).2.length ≤ cs.length * e + 1
  | [] => by simp
  | [c] => by
      have h := length_conv_le [1] a
      simp only [compose_cons, compose_nil, conv, length_add, smul, List.length_map,
        List.length_cons, List.length_nil] at h ⊢
      omega
  | c :: c' :: cs => by
      obtain ⟨ih1, ih2⟩ := length_compose ha hb (c' :: cs)
      have h1 := length_conv_le (compose a b (c' :: cs)).1 b
      have h2 := length_conv_le (compose a b (c' :: cs)).2 a
      rw [compose_cons]
      simp only [length_add, smul, List.length_map, List.length_cons, Nat.add_sub_cancel,
        Nat.add_mul, Nat.one_mul] at h1 h2 ih1 ih2 ⊢
      omega

/-- The `l1` norm of the composed row is at most `l1 cs * K ^ (cs.length - 1)` when `l1 a` and
`l1 b` are at most `K`, and that of the power at most `K ^ cs.length`. -/
theorem l1_compose {a b : List Int} {K : Nat} (ha : l1 a ≤ K) (hb : l1 b ≤ K) :
    ∀ cs : List Int, l1 (compose a b cs).1 ≤ l1 cs * K ^ (cs.length - 1) ∧
      l1 (compose a b cs).2 ≤ K ^ cs.length
  | [] => by simp [l1]
  | [c] => by
      have h := l1_conv_le [1] a
      have e1 : l1 [1] = 1 := rfl
      rw [e1, Nat.one_mul] at h
      rw [compose_cons, compose_nil,
        show add (conv [] b) (smul c [1]) = [c] by simp [conv, add, smul]]
      exact ⟨by simp, by simpa using Nat.le_trans h ha⟩
  | c :: c' :: cs => by
      obtain ⟨ih1, ih2⟩ := l1_compose ha hb (c' :: cs)
      have h1 := l1_conv_le (compose a b (c' :: cs)).1 b
      have h2 := l1_conv_le (compose a b (c' :: cs)).2 a
      have h3 := l1_add_le (conv (compose a b (c' :: cs)).1 b) (smul c (compose a b (c' :: cs)).2)
      rw [l1_smul] at h3
      rw [compose_cons, l1_cons]
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.pow_succ] at ih1 ih2 ⊢
      generalize K ^ cs.length = P at ih1 ih2 ⊢
      generalize l1 (compose a b (c' :: cs)).1 = x at ih1 h1
      generalize l1 (compose a b (c' :: cs)).2 = y at ih2 h2 h3
      generalize l1 (c' :: cs) = L at ih1 ⊢
      have m1 := Nat.mul_le_mul ih1 hb
      have m2 := Nat.mul_le_mul ih2 ha
      have m3 := Nat.mul_le_mul_left c.natAbs ih2
      rw [Nat.mul_assoc] at m1
      rw [Nat.add_mul]
      constructor <;> omega

/-- Reading back the row of `horner`: if `a` and `b` have at most `e + 1` entries and `l1` norms
at most `K`, and the guarded row `u` of `n` lanes with entries in `[-2 ^ g, 2 ^ g)` passes
`n * 2 ^ g * K ^ (n - 1) < 2 ^ (w - 1)`, then the biased row of `N ≥ (n - 1) e + 1` lanes of
`horner` holds the composed row, padded with zeros. For an affine substitution, `e = 2` and
`N = 2 n - 1`. -/
theorem entries_ofInt_horner {w g n u K e N : Nat} {a b : List Int} (hu : guard w g n u = true)
    (ha : a.length ≤ e + 1) (hb : b.length ≤ e + 1) (hN : (n - 1) * e + 1 ≤ N) (hKa : l1 a ≤ K)
    (hKb : l1 b ≤ K) (hroom : n * 2 ^ g * K ^ (n - 1) < 2 ^ (w - 1)) :
    entries w N (ofInt w N (horner w n (eval (2 ^ w) a) (eval (2 ^ w) b) u)) =
      (compose a b (entries w n u)).1 ++
        List.replicate (N - (compose a b (entries w n u)).1.length) 0 := by
  obtain ⟨hgw, -, hb'⟩ := guard_sound hu
  have hw : 1 ≤ w := by omega
  have hl := (length_compose ha hb (entries w n u)).1
  rw [length_entries] at hl
  have hlen : (compose a b (entries w n u)).1.length ≤ N := by omega
  -- the composed row's `l1` norm, so each of its entries, stays below the bias
  have h1 := (l1_compose hKa hKb (entries w n u)).1
  have h2 := l1_le_of_bound hb'
  rw [length_entries] at h1 h2
  have h3 := Nat.mul_le_mul_right (K ^ (n - 1)) h2
  rw [horner_eq, entries_ofInt_eval hw hlen (fits_of_l1_lt (by omega))]

end FloatLib.Numerics.Packed
