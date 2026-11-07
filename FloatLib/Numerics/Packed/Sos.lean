/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof

/-!
# Sum-of-squares certificates

A real trigonometric polynomial `T(u)` is nonnegative on the whole circle when it is a square plus
a remainder that is too small to matter: if `T = |h|² + e` and the constant term of `e` is at least
the sum of the absolute values of its other coefficients, then `T(u) ≥ e(u) ≥ 0`. The Fejér–Riesz
theorem says that a nonnegative `T` is `|h|²` for some polynomial `h` of half its degree, so such
a certificate exists whenever `T - η` is still nonnegative for a small `η`. An untrusted program
finds `h` (a spectral factor of `T - η`, rounded to Gaussian integers), and the kernel only checks
the easy direction.

So let's fix the conventions once. A real trigonometric polynomial of degree `n - 1` is the real
part of a complex row `c₋ₙ₊₁, …, cₙ₋₁` in powers of `z = exp (i u)`, and we keep the real and
imaginary parts of the row in two integer rows: the pair `(t, s)` stands for `t - i s`. That is
the Fourier convention `cₖ = (aₖ - i bₖ) / 2` for `aₖ cos (k u) + bₖ sin (k u)`, so a cosine row
and a sine row of the same half coefficients fill the two parts as they are. The factor is a
Gaussian-integer row `p + i q`, whose `|p + i q|²` has the pair of rows `normSq n p q`.

## Main definitions

* `sqRe` and `sqIm`: the two rows of `|p + i q|²`, centred at lane `n - 1`, by four Kronecker
  products and two reversals.
* `sosCheck w gt gh n m m' kT kc kH t s p q`: range checks on the target `(t, s)` of `2 * n - 1`
  lanes and on the factor `(p, q)` of `m` and `m'` lanes, one comparison of small numbers that
  rules out overflow, and the check that the centre of the real part of
  `kT (t - i s) + kc - kH |p + i q|²` dominates the `l1` norms of both parts.
* `normSq` and `sosDefect`: the same rows on integer lists.

## Main statements

* `sqRe_eq` and `sqIm_eq`: the kernel rows are the values of `normSq`.
* `l1_normSq_le` and `length_normSq_le`: the bounds that keep those rows inside their lanes.
* `sosCheck_sound`: a pass is the integer certificate `l1 e₁ + l1 e₂ ≤ 2 e₁[n - 1]`.
  `Coeff.laurent_sosCheck` turns it into the bound on the circle.

## Implementation notes

The integers `kT`, `kc` and `kH` carry the scales: with `kT > 0` a pass says `kT T(u) + kc ≥ 0`,
a lower bound `T ≥ -kc / kT`, and with `kT < 0` an upper bound. A factor of `m = m' = 0` lanes is
the empty square, and then the check is just centre dominance of `kT T + kc`, the bound that the
`l1` norm of the coefficients gives with no certificate at all. A real factor has `m' = 0`, so its
imaginary part costs nothing: the kernel reverses `q` in zero steps and multiplies by zero.

The factor of a real target can always be taken real, and then `sosCheck` is the plain
`h ⋆ reverse h` check. With sine terms the target is a Hermitian row with a genuinely imaginary
part, and its spectral factor has complex coefficients. I liked that this needed no other kernel
program: the imaginary part of the factor enters through two more products, and the shifts by
`n - m` and `n - m'` line up rows of different lengths at the same centre.

For example, `1 + sin u` is the pair `t = [0, 2, 0]`, `s = [-1, 0, 1]` over `2`, read as
`(t - i s) / 2` at centre `1`. The factor `p = [1, 0]`, `q = [0, -1]` is `1 - i z`, and
`normSq 2 p q = ([0, 2, 0], [-1, 0, 1])`, so the defect of `2 (1 + sin u) - |1 - i z|²` is zero
and the check passes with nothing to spare. That is the exact minimum `0` at `u = -π/2`.

## References

* Lipót Fejér, *Über trigonometrische Polynome*, J. Reine Angew. Math. 146 (1916), 53–82,
  <https://doi.org/10.1515/crll.1916.146.53>.
* Friedrich Riesz, *Über ein Problem des Herrn Carathéodory*, J. Reine Angew. Math. 146 (1916),
  83–87, <https://doi.org/10.1515/crll.1916.146.83>.
* Bogdan Dumitrescu, *Positive Trigonometric Polynomials and Signal Processing Applications*,
  Springer (2007), <https://doi.org/10.1007/978-1-4020-5125-8>, chapter 1 on the Fejér–Riesz
  theorem and spectral factors of polynomials with complex coefficients.

## Tags

sum of squares, Fejér–Riesz theorem, spectral factorization, certificate
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-! ### Kernel programs -/

/-- The real row of `|p + i q|²` for the biased rows `p` of `m` lanes and `q` of `m'` lanes, as a
signed row centred at lane `n - 1`: `p ⋆ reverse p + q ⋆ reverse q`, each product moved up so that
its middle lane lands on lane `n - 1`. -/
def sqRe (w n m m' p q : Nat) : Int :=
  Int.add (shift w (Nat.sub n m) (autocorr w m p)) (shift w (Nat.sub n m') (autocorr w m' q))

/-- The imaginary row of `|p + i q|²` in the convention `t - i s`, centred at lane `n - 1`:
`reverse q ⋆ p - reverse p ⋆ q`. -/
def sqIm (w n m m' p q : Nat) : Int :=
  Int.sub (shift w (Nat.sub n m') (Int.mul (toInt w m' (rev w m' q)) (toInt w m p)))
    (shift w (Nat.sub n m) (Int.mul (toInt w m (rev w m p)) (toInt w m' q)))

/-- The real row of `kT (t - i s) + kc - kH |p + i q|²`, for target rows of `2 * n - 1` lanes. -/
def sosRe (w n m m' : Nat) (kT kc : Int) (kH t p q : Nat) : Int :=
  Int.sub
    (Int.add (Int.mul kT (toInt w (Nat.sub (Nat.mul 2 n) 1) t)) (shift w (Nat.sub n 1) kc))
    (Int.mul (Int.ofNat kH) (sqRe w n m m' p q))

/-- The imaginary row of `kT (t - i s) + kc - kH |p + i q|²`. -/
def sosIm (w n m m' : Nat) (kT : Int) (kH s p q : Nat) : Int :=
  Int.sub (Int.mul kT (toInt w (Nat.sub (Nat.mul 2 n) 1) s))
    (Int.mul (Int.ofNat kH) (sqIm w n m m' p q))

/-- The sum-of-squares check: the target `(t, s)` has `2 * n - 1` lanes with entries in
`[-2 ^ gt, 2 ^ gt)`, the factor `(p, q)` has `m ≤ n` and `m' ≤ n` lanes with entries in
`[-2 ^ gh, 2 ^ gh)`, no lane of the defect can overflow, and the centre of its real row is at least
the sum of the absolute values of all its other entries, real and imaginary. -/
def sosCheck (w gt gh n m m' : Nat) (kT kc : Int) (kH t s p q : Nat) : Bool :=
  Nat.blt 0 n && Nat.ble m n && Nat.ble m' n &&
    guard w gt (Nat.sub (Nat.mul 2 n) 1) t && guard w gt (Nat.sub (Nat.mul 2 n) 1) s &&
    guard w gh m p && guard w gh m' q &&
    Nat.blt
      (Nat.add (Nat.add (Nat.mul (Int.natAbs kT) (Nat.mul (Nat.sub (Nat.mul 2 n) 1) (pow2 gt)))
        (Int.natAbs kc))
        (Nat.mul kH
          (Nat.mul (Nat.mul (Nat.add m m') (pow2 gh)) (Nat.mul (Nat.add m m') (pow2 gh)))))
      (pow2 (Nat.sub w 1)) &&
    Nat.ble
      (Nat.add
        (Nat.add (absSum w (Nat.sub (Nat.mul 2 n) 1) (sosRe w n m m' kT kc kH t p q))
          (absSum w (Nat.sub (Nat.mul 2 n) 1) (sosIm w n m m' kT kH s p q)))
        (Nat.mul 2 (pow2 (Nat.sub w 1))))
      (Nat.mul 2
        (lane w (Nat.sub n 1)
          (ofInt w (Nat.sub (Nat.mul 2 n) 1) (sosRe w n m m' kT kc kH t p q))))

/-! ### Integer rows -/

/-- The two rows of `|P + i Q|²`, centred at entry `n - 1`, in the convention `t - i s`:
`P ⋆ reverse P + Q ⋆ reverse Q` and `reverse Q ⋆ P - reverse P ⋆ Q`, each moved up by the zeros
that put its middle entry at `n - 1`. -/
def normSq (n : Nat) (P Q : List Int) : List Int × List Int :=
  (add (List.replicate (n - P.length) 0 ++ conv P P.reverse)
      (List.replicate (n - Q.length) 0 ++ conv Q Q.reverse),
    sub (List.replicate (n - Q.length) 0 ++ conv Q.reverse P)
      (List.replicate (n - P.length) 0 ++ conv P.reverse Q))

/-- The rows that `sosCheck` tests, on integer lists: `kT (T - i S) + kc - kH |P + i Q|²`, with the
constant `kc` in entry `n - 1`. -/
def sosDefect (n : Nat) (kT kc : Int) (kH : Nat) (T S P Q : List Int) : List Int × List Int :=
  (sub (add (smul kT T) (List.replicate (n - 1) 0 ++ [kc])) (smul kH (normSq n P Q).1),
    sub (smul kT S) (smul kH (normSq n P Q).2))

/-! ### The kernel rows as values -/

private theorem intSub (a b : Int) : Int.sub a b = a - b := rfl

private theorem toInt_rev {w m p : Nat} (hw : 1 ≤ w) :
    toInt w m (rev w m p) = eval (2 ^ w) (entries w m p).reverse := by
  rw [← entries_rev, eval_entries hw (rev_lt w m p)]

/-- `sqRe` is the value of the real row of `normSq`. -/
theorem sqRe_eq {w n m m' p q : Nat} (hw : 1 ≤ w) (hp : p < 2 ^ (w * m))
    (hq : q < 2 ^ (w * m')) :
    sqRe w n m m' p q = eval (2 ^ w) (normSq n (entries w m p) (entries w m' q)).1 := by
  simp only [sqRe, normSq, eval_add, ← shift_eval, length_entries, ← autocorr_eq hw hp,
    ← autocorr_eq hw hq, Nat.sub_eq, Int.add_def]

/-- `sqIm` is the value of the imaginary row of `normSq`. -/
theorem sqIm_eq {w n m m' p q : Nat} (hw : 1 ≤ w) (hp : p < 2 ^ (w * m))
    (hq : q < 2 ^ (w * m')) :
    sqIm w n m m' p q = eval (2 ^ w) (normSq n (entries w m p) (entries w m' q)).2 := by
  simp only [sqIm, normSq, eval_sub, ← shift_eval, eval_conv, length_entries, Nat.sub_eq,
    intSub, Int.mul_def, toInt_rev hw, ← eval_entries hw hp, ← eval_entries hw hq]

/-! ### Bounds on the rows of a square -/

/-- Both rows of `|P + i Q|²` fit in `2 * n - 1` entries when `P` and `Q` have at most `n`. -/
theorem length_normSq_le {n : Nat} (hn : 0 < n) {P Q : List Int} (hP : P.length ≤ n)
    (hQ : Q.length ≤ n) :
    (normSq n P Q).1.length ≤ 2 * n - 1 ∧ (normSq n P Q).2.length ≤ 2 * n - 1 := by
  have c1 := length_conv_le P P.reverse
  have c2 := length_conv_le Q Q.reverse
  have c3 := length_conv_le Q.reverse P
  have c4 := length_conv_le P.reverse Q
  simp only [List.length_reverse] at c1 c2 c3 c4
  simp only [normSq, sub, length_add, smul, List.length_map, List.length_append,
    List.length_replicate]
  omega

/-- The `l1` norms of both rows of `|P + i Q|²` are at most `((|P| + |Q|) 2 ^ g)²` for entries in
`[-2 ^ g, 2 ^ g)`, which is the headroom that `sosCheck` asks for. -/
theorem l1_normSq_le {g : Nat} {P Q : List Int} (hP : ∀ x ∈ P, -2 ^ g ≤ x ∧ x < 2 ^ g)
    (hQ : ∀ x ∈ Q, -2 ^ g ≤ x ∧ x < 2 ^ g) (n : Nat) :
    l1 (normSq n P Q).1 ≤ (P.length + Q.length) * 2 ^ g * ((P.length + Q.length) * 2 ^ g) ∧
      l1 (normSq n P Q).2 ≤ (P.length + Q.length) * 2 ^ g * ((P.length + Q.length) * 2 ^ g) := by
  have hp := l1_le_of_bound hP
  have hq := l1_le_of_bound hQ
  have c1 := l1_conv_le P P.reverse
  have c2 := l1_conv_le Q Q.reverse
  have c3 := l1_conv_le Q.reverse P
  have c4 := l1_conv_le P.reverse Q
  have s1 := l1_add_le (List.replicate (n - P.length) 0 ++ conv P P.reverse)
    (List.replicate (n - Q.length) 0 ++ conv Q Q.reverse)
  have s2 := l1_sub_le (List.replicate (n - Q.length) 0 ++ conv Q.reverse P)
    (List.replicate (n - P.length) 0 ++ conv P.reverse Q)
  simp only [l1_reverse, l1_append, l1_zeros, Nat.zero_add] at c1 c2 c3 c4 s1 s2
  simp only [normSq]
  rw [Nat.add_mul]
  generalize P.length * 2 ^ g = a at hp ⊢
  generalize Q.length * 2 ^ g = b at hq ⊢
  have pp := Nat.mul_le_mul hp hp
  have qq := Nat.mul_le_mul hq hq
  have pq := Nat.mul_le_mul hp hq
  have qp := Nat.mul_le_mul hq hp
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
  constructor <;> omega

/-! ### Soundness -/

private theorem l1_single (k : Nat) (c : Int) : l1 (List.replicate k 0 ++ [c]) = c.natAbs := by
  simp [l1]

/-- A passing `sosCheck` gives the integer certificate: for the rows `e₁ - i e₂` of
`kT (T - i S) + kc - kH |P + i Q|²`, with `T`, `S`, `P` and `Q` the entries of the four rows, the
centre `e₁[n - 1]` is at least the sum of the absolute values of all other entries,
`l1 e₁ + l1 e₂ ≤ 2 e₁[n - 1]`. -/
theorem sosCheck_sound {w gt gh n m m' kH t s p q : Nat} {kT kc : Int}
    (hc : sosCheck w gt gh n m m' kT kc kH t s p q = true) :
    0 < n ∧ m ≤ n ∧ m' ≤ n ∧
      ((l1 (sosDefect n kT kc kH (entries w (2 * n - 1) t) (entries w (2 * n - 1) s)
          (entries w m p) (entries w m' q)).1 +
        l1 (sosDefect n kT kc kH (entries w (2 * n - 1) t) (entries w (2 * n - 1) s)
          (entries w m p) (entries w m' q)).2 : Nat) : Int) ≤
        2 * (sosDefect n kT kc kH (entries w (2 * n - 1) t) (entries w (2 * n - 1) s)
          (entries w m p) (entries w m' q)).1.getD (n - 1) 0 := by
  simp only [sosCheck, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, pow2_eq, Nat.mul_eq, Nat.sub_eq,
    Nat.add_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hn, hm⟩, hm'⟩, ht⟩, hs⟩, hp⟩, hq⟩, hroom⟩, hcheck⟩ := hc
  obtain ⟨hgw, ht', htb⟩ := guard_sound ht
  obtain ⟨-, hs', hsb⟩ := guard_sound hs
  obtain ⟨-, hp', hpb⟩ := guard_sound hp
  obtain ⟨-, hq', hqb⟩ := guard_sound hq
  have hw : 1 ≤ w := by omega
  refine ⟨hn, hm, hm', ?_⟩
  have hsq := l1_normSq_le hpb hqb n
  have hlsq := length_normSq_le hn (P := entries w m p) (Q := entries w m' q)
    (by rw [length_entries]; exact hm) (by rw [length_entries]; exact hm')
  have hre := sqRe_eq (n := n) hw hp' hq'
  have him := sqIm_eq (n := n) hw hp' hq'
  generalize hT : entries w (2 * n - 1) t = T at htb
  generalize hS : entries w (2 * n - 1) s = S at hsb
  generalize hP : entries w m p = P at hpb hsq hlsq hre him
  generalize hQ : entries w m' q = Q at hqb hsq hlsq hre him
  have hTl : T.length = 2 * n - 1 := by rw [← hT, length_entries]
  have hSl : S.length = 2 * n - 1 := by rw [← hS, length_entries]
  have hPl : P.length = m := by rw [← hP, length_entries]
  have hQl : Q.length = m' := by rw [← hQ, length_entries]
  rw [hPl, hQl] at hsq
  generalize hN : normSq n P Q = N at hsq hlsq hre him
  have h1 := l1_le_of_bound htb
  have h2 := l1_le_of_bound hsb
  rw [hTl] at h1
  rw [hSl] at h2
  have hl1 : l1 (sosDefect n kT kc kH T S P Q).1 < 2 ^ (w - 1) := by
    have h5 := l1_sub_le (add (smul kT T) (List.replicate (n - 1) 0 ++ [kc])) (smul kH N.1)
    have h6 := l1_add_le (smul kT T) (List.replicate (n - 1) 0 ++ [kc])
    rw [l1_smul, l1_single] at h6
    rw [l1_smul] at h5
    have h7 := Nat.mul_le_mul_left kT.natAbs h1
    have h8 := Nat.mul_le_mul_left kH hsq.1
    simp only [Int.natAbs_natCast] at h5
    simp only [sosDefect, hN]
    omega
  have hl2 : l1 (sosDefect n kT kc kH T S P Q).2 < 2 ^ (w - 1) := by
    have h5 := l1_sub_le (smul kT S) (smul kH N.2)
    rw [l1_smul, l1_smul] at h5
    have h7 := Nat.mul_le_mul_left kT.natAbs h2
    have h8 := Nat.mul_le_mul_left kH hsq.2
    simp only [Int.natAbs_natCast] at h5
    simp only [sosDefect, hN]
    omega
  have hval1 : sosRe w n m m' kT kc kH t p q = eval (2 ^ w) (sosDefect n kT kc kH T S P Q).1 := by
    simp only [sosRe, Int.add_def, intSub, Int.mul_def, Int.ofNat_eq_natCast, Nat.mul_eq,
      Nat.sub_eq]
    rw [← eval_entries hw ht', hT, hre]
    have hk : shift w (n - 1) kc = eval (2 ^ w) (List.replicate (n - 1) 0 ++ [kc]) := by
      rw [← shift_eval]; simp [eval]
    rw [hk, sosDefect, hN, eval_sub, eval_add, eval_smul, eval_smul]
  have hval2 : sosIm w n m m' kT kH s p q = eval (2 ^ w) (sosDefect n kT kc kH T S P Q).2 := by
    simp only [sosIm, intSub, Int.mul_def, Int.ofNat_eq_natCast, Nat.mul_eq, Nat.sub_eq]
    rw [← eval_entries hw hs', hS, him, sosDefect, hN, eval_sub, eval_smul, eval_smul]
  have hlen1 : (sosDefect n kT kc kH T S P Q).1.length ≤ 2 * n - 1 := by
    simp only [sosDefect, hN, sub, length_add, smul, List.length_map, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil, hTl]
    omega
  have hlen2 : (sosDefect n kT kc kH T S P Q).2.length ≤ 2 * n - 1 := by
    simp only [sosDefect, hN, sub, length_add, smul, List.length_map, hSl]
    omega
  rw [hval1, hval2, absSum_eval hw hlen1 hl1, absSum_eval hw hlen2 hl2, lane_eq,
    ← lane_eq] at hcheck
  have hentry := entry_ofInt_eval (k := n - 1) hw hlen1 (by omega) (fits_of_l1_lt hl1)
  rw [entry_eq] at hentry
  have e := natCast_two_pow (w - 1)
  omega

end FloatLib.Numerics.Packed
