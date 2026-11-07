/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Packed rows

A packed row is a list of integers kept in one natural number, one integer per lane of `w` bits.
Lean's kernel computes fifteen natural-number functions on literals with GMP (successor, addition,
subtraction, multiplication, division, remainder, gcd, the two comparisons, the three bitwise
operations, both shifts and powers) and interprets everything else one step at a time, at a few
microseconds per step. So a certificate that does its work with a few such operations on a few
large literals checks fast, and one that walks a list entry by entry does not. The programs here
are written with the bare `Nat` functions, so that the fast path fires and no instance is
unfolded.

A row is signed by default: lane `k` of a biased row holds `x + 2 ^ (w - 1)` for the signed entry
`x`. The checks that care about signs take an option `(signed := false)` for rows of natural
numbers, whose lanes hold the entries as they are. With `w = 8`, the signed row `[1, -2, 3]` has
the lanes `129, 126, 131`, so it is stored as the number
`129 + 126 * 256 + 131 * 256 ^ 2 = 8617601`. It stands for the integer
`1 - 2 * 256 + 3 * 256 ^ 2 = 196097`, which `toInt 8 3` returns. Integers multiply the way rows
do. The row `[4, -5]` stands for `4 - 5 * 256 = -1276`, and `196097 * -1276` is the integer of
`[4, -13, 22, -15]`, the Cauchy product of the two rows, because every lane of the product fits in
eight bits. That is Kronecker substitution.

## Main definitions

Kernel programs, on biased rows `u : Nat` and signed rows `z : Int`:

* `lane w k u` reads lane `k` by one shift and one mask, and `entry w k u` is its signed value.
* `guard w g n u` checks that every signed entry lies in `[-2 ^ g, 2 ^ g)` with one addition, one
  conjunction and one comparison, or with `(signed := false)` that every lane is below `2 ^ g`.
* `laneSum w u` adds up the lanes of a row by one remainder modulo `2 ^ w - 1`, and `posSum`,
  `absSum` and `sum` add up the positive entries, the absolute values and the entries of a signed
  row.
* `toInt`, `ofInt` and `pack` move between biased rows, integers and lists, and `shift` moves a
  signed row up by whole lanes.
* `rev` reverses the lanes, and `autocorr` multiplies a row by its reverse.
* `linked w d u k xs` checks that lanes `k, k + 1, …` hold the rationals `xs` times one
  denominator `d`, by cross-multiplication.

The specification, on integer lists:

* `eval b xs` is `∑ k, xs[k] * b ^ k`, and `add`, `smul`, `sub` and `conv` are the lanewise sum,
  the scaling, the difference and the Cauchy product.
* `l1 xs` is the sum of the absolute values, and `Fits w x` says that `x` fits a signed lane.
* `lanes w n u` lists the lanes of a row and `entries w n u` the signed entries of a biased row.

## Main statements

* `eval_conv`: the Kronecker identity `eval b (conv xs ys) = eval b xs * eval b ys`.
* `l1_conv_le`: `l1` is submultiplicative, which bounds the lanes of a product before it is formed.
* `fits_of_l1_lt` and `l1_le_of_bound`: the two directions between `l1` bounds and range checks.
* `linked_sound`: what a passing `linked` says, entry by entry.

The soundness theorems of the kernel programs are in `FloatLib.Numerics.Packed.Proof`, and
`packed_row` in `FloatLib.Numerics.Packed.Literal` brings large rows in as raw literals.

## Implementation notes

Signed rows are `Int` values only where a certificate does a few operations per row, such as a
product or a difference, and biased `Nat` values wherever lanes are read, because the kernel
interprets every `Int` operation. Strides and masks are shifts: under `decide +kernel`, Lean 4.35
evaluates `Nat.pow 2 k` only for `k ≤ 2 ^ 24`, while `1 <<< k` goes well beyond. The kernel keeps
every intermediate value until a declaration ends, so a check that uses one row several times
should do so inside one theorem.

Rows carry no scale. A row of values `x k * q` with one rational factor `q` is the integer row `x`
together with `q`, so binary, decimal and fixed-point data all use the same integer programs, and
the scale is applied where the integers are interpreted.

Most of these programs are SWAR tricks, SIMD within a register, done on one register of a million
bits. The one I like best is `laneSum`. Since `2 ^ w ≡ 1` modulo `2 ^ w - 1`, the remainder of a
row modulo `2 ^ w - 1` is the sum of its lanes, so one division adds up every lane at once. With
`w = 8` and the lanes `3, 1, 4`, the row is `3 + 1 * 256 + 4 * 65536 = 262403`, and
`262403 % 255 = 8`. It's casting out nines in base `2 ^ w`, and HAKMEM item 169 counts the bits
of a word the same way, with a remainder modulo 63. The Kronecker certificates of Lean's `grind`
check polynomial identities in the same spirit, by comparing two big numbers in the kernel.

## References

* Leopold Kronecker, *Grundzüge einer arithmetischen Theorie der algebraischen Grössen*,
  J. Reine Angew. Math. 92 (1882), 1–122, <https://doi.org/10.1515/crll.1882.92.1>.
* David Harvey, *Faster polynomial multiplication via multipoint Kronecker substitution*,
  J. Symbolic Comput. 44 (2009), 1502–1510, <https://doi.org/10.1016/j.jsc.2009.05.004>.
* Randall J. Fisher and Henry G. Dietz, *Compiling for SIMD within a register*, LCPC 1998,
  LNCS 1656 (1999), 290–305, <https://doi.org/10.1007/3-540-48319-5_19>.
* Michael Beeler, R. William Gosper and Richard Schroeppel, *HAKMEM*, MIT AI Memo 239 (1972),
  item 169, <https://dspace.mit.edu/handle/1721.1/6086>.
* Lean 4, release v4.35.0, `type_checker::reduce_nat` in `src/kernel/type_checker.cpp`, which lists
  the functions the kernel computes on literals: <https://github.com/leanprover/lean4>.
* Leonardo de Moura, Lean 4 pull request 15999, *Kronecker certificates* for `grind` and
  `Sym.simp`: <https://github.com/leanprover/lean4/pull/15999>.

## Tags

packed row, Kronecker substitution, SWAR, kernel reduction, certificate
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-! ### Kernel programs -/

/-- `2 ^ k`, computed by one shift. -/
def pow2 (k : Nat) : Nat := Nat.shiftLeft 1 k

/-- The number with a one at the bottom of each of `n` lanes of width `w`,
`∑ k < n, 2 ^ (w * k)`, computed by one division. -/
def ones (w n : Nat) : Nat := Nat.div (Nat.sub (pow2 (Nat.mul w n)) 1) (Nat.sub (pow2 w) 1)

/-- The bias `2 ^ (w - 1)` in each of `n` lanes of width `w`. -/
def bias (w n : Nat) : Nat := Nat.mul (pow2 (Nat.sub w 1)) (ones w n)

/-- Lane `k` of width `w` of `u`, by one shift and one mask. -/
def lane (w k u : Nat) : Nat := Nat.land (Nat.shiftRight u (Nat.mul w k)) (Nat.sub (pow2 w) 1)

/-- The signed entry in lane `k` of the biased row `u`, `lane w k u - 2 ^ (w - 1)`. -/
def entry (w k u : Nat) : Int := Int.subNatNat (lane w k u) (pow2 (Nat.sub w 1))

/-- The integer that the biased row `u` of `n` lanes stands for, `u - bias w n`. -/
def toInt (w n u : Nat) : Int := Int.subNatNat u (bias w n)

/-- The biased row of `n` lanes of the integer `z`, `z + bias w n`. -/
def ofInt (w n : Nat) (z : Int) : Nat := Int.toNat (Int.add z (Int.ofNat (bias w n)))

/-- The signed row `z` moved up by `k` lanes, `z * 2 ^ (w * k)`; lanes `[0, k)` become zero. -/
def shift (w k : Nat) (z : Int) : Int := Int.mul z (Int.ofNat (pow2 (Nat.mul w k)))

/-- The row of a list: lane `k` holds `xs[k] + 2 ^ (w - 1)`, or `xs[k]` itself with
`(signed := false)`. This walks the list, so use it for rows the kernel derives from other data,
and `packed_row` for given data. -/
def pack (w : Nat) (xs : List Int) (signed : Bool := true) : Nat :=
  match xs with
  | [] => 0
  | x :: xs =>
    Nat.add (Int.toNat (Int.add x (Int.ofNat (cond signed (pow2 (Nat.sub w 1)) 0))))
      (Nat.shiftLeft (pack w xs signed) w)

/-- Every signed entry of the biased row `u` of `n` lanes lies in `[-2 ^ g, 2 ^ g)`, and `u` has no
lanes beyond `n`. With `(signed := false)`, every lane of `u` is below `2 ^ g`.

Adding `2 ^ g` to every lane moves a signed entry in range to
`[2 ^ (w - 1), 2 ^ (w - 1) + 2 ^ (g + 1))`, where its bits from `g + 1` up read `100…0`. A lane that
carries into the next one is left with a clear top bit, so one conjunction with a mask of those
bits catches both. An unsigned lane is below `2 ^ g` when its bits from `g` up are clear. -/
def guard (w g n u : Nat) (signed : Bool := true) : Bool :=
  Nat.blt u (pow2 (Nat.mul w n)) &&
    cond signed
      (Nat.blt (Nat.add g 1) w &&
        Nat.beq (Nat.land (Nat.add u (Nat.mul (pow2 g) (ones w n)))
          (Nat.mul (Nat.sub (pow2 w) (pow2 (Nat.add g 1))) (ones w n))) (bias w n))
      (Nat.ble g w && Nat.beq (Nat.land u (Nat.mul (Nat.sub (pow2 w) (pow2 g)) (ones w n))) 0)

/-- The sum of the lanes of `u` modulo `2 ^ w - 1`, which is the sum itself when that is below
`2 ^ w - 1`, by one remainder: `2 ^ w ≡ 1`. -/
def laneSum (w u : Nat) : Nat := Nat.mod u (Nat.sub (pow2 w) 1)

/-- The sum of the positive entries of the signed row `z` of `n` lanes. The sign bits of the biased
row select the lanes to keep, and `laneSum` adds them up. -/
def posSum (w n : Nat) (z : Int) : Nat :=
  laneSum w (Nat.land (ofInt w n z)
    (Nat.mul (Nat.shiftRight (Nat.land (ofInt w n z) (bias w n)) (Nat.sub w 1))
      (Nat.sub (pow2 (Nat.sub w 1)) 1)))

/-- The sum of the absolute values of the entries of the signed row `z` of `n` lanes. -/
def absSum (w n : Nat) (z : Int) : Nat := Nat.add (posSum w n z) (posSum w n (Int.neg z))

/-- The sum of the entries of the signed row `z` of `n` lanes. -/
def sum (w n : Nat) (z : Int) : Int := Int.subNatNat (posSum w n z) (posSum w n (Int.neg z))

/-- Lanes `[0, n)` of `u` in reverse order, splitting the lanes in halves; `d` bounds the depth of
the recursion. -/
def revAux (w : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | d + 1, n, u =>
    cond (Nat.ble n 1) (Nat.land u (Nat.sub (pow2 (Nat.mul w n)) 1))
      (Nat.lor
        (Nat.shiftLeft
          (revAux w d (Nat.div n 2) (Nat.land u (Nat.sub (pow2 (Nat.mul w (Nat.div n 2))) 1)))
          (Nat.mul w (Nat.sub n (Nat.div n 2))))
        (revAux w d (Nat.sub n (Nat.div n 2)) (Nat.shiftRight u (Nat.mul w (Nat.div n 2)))))

/-- The biased row whose lanes are lanes `[0, n)` of `u` in reverse order. -/
def rev (w n u : Nat) : Nat := revAux w n n u

/-- The autocorrelation of the biased row `u` of `n` lanes, by one Kronecker product: the signed
row of `2 * n - 1` lanes whose lane `n - 1 + m` is `∑ j, x[j] * x[j - m]` for the entries `x`. -/
def autocorr (w n u : Nat) : Int := Int.mul (toInt w n u) (toInt w n (rev w n u))

/-- Lanes `k, k + 1, …` of the biased row `u` hold the rationals `xs` times `d`: each
`x = num / den` passes `num * d = entry * den`, two integer products per entry and no rational
arithmetic. -/
def linked (w d u k : Nat) : List Rat → Bool
  | [] => true
  | x :: xs => Int.mul x.num (Int.ofNat d) == Int.mul (entry w k u) (Int.ofNat x.den) &&
      linked w d u (k + 1) xs

/-! ### Integer rows -/

/-- The value of a row at `b`, `∑ k, xs[k] * b ^ k`. -/
def eval (b : Int) : List Int → Int
  | [] => 0
  | x :: xs => x + b * eval b xs

/-- The lanewise sum of two rows, the shorter one padded with zeros. It works for any entries
with an addition: integer rows here, and lists of rational coefficients in
`FloatLib.Numerics.Coeff`. -/
def add {α : Type} [Add α] : List α → List α → List α
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: add xs ys

/-- Every entry multiplied by `c`. -/
def smul {α : Type} [Mul α] (c : α) (xs : List α) : List α := xs.map (c * ·)

/-- The lanewise difference of two rows. -/
def sub (xs ys : List Int) : List Int := add xs (smul (-1) ys)

/-- The Cauchy product of two rows: entry `k` is `∑ i + j = k, xs[i] * ys[j]`. -/
def conv : List Int → List Int → List Int
  | [], _ => []
  | x :: xs, ys => add (smul x ys) (0 :: conv xs ys)

/-- The sum of the absolute values of the entries. -/
def l1 (xs : List Int) : Nat := (xs.map Int.natAbs).sum

/-- Lanes `[0, n)` of `u`. -/
def lanes (w n u : Nat) : List Nat := (List.range n).map fun k => lane w k u

/-- The signed entries in lanes `[0, n)` of the biased row `u`. -/
def entries (w n u : Nat) : List Int := (List.range n).map fun k => entry w k u

/-- `x` fits a signed lane of width `w`: `-2 ^ (w - 1) ≤ x < 2 ^ (w - 1)`. -/
def Fits (w : Nat) (x : Int) : Prop := -2 ^ (w - 1) ≤ x ∧ x < 2 ^ (w - 1)

/-! ### The kernel programs as arithmetic -/

/-- `pow2` is a power of two. -/
theorem pow2_eq (k : Nat) : pow2 k = 2 ^ k := by simp [pow2, Nat.shiftLeft_eq]

/-- A lane is a digit in base `2 ^ w`. -/
theorem lane_eq (w k u : Nat) : lane w k u = u / 2 ^ (w * k) % 2 ^ w := by
  simp only [lane, pow2_eq, Nat.sub_eq, Nat.mul_eq]
  show (u >>> (w * k)) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-- A lane has `w` bits. -/
theorem lane_lt (w k u : Nat) : lane w k u < 2 ^ w := by
  rw [lane_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos w)

/-- An entry is its lane minus the bias. -/
theorem entry_eq (w k u : Nat) : entry w k u = (lane w k u : Int) - 2 ^ (w - 1) := by
  simp [entry, Int.subNatNat_eq_coe, pow2_eq]

/-- `toInt` subtracts the bias. -/
theorem toInt_eq (w n u : Nat) : toInt w n u = (u : Int) - bias w n := by
  simp [toInt, Int.subNatNat_eq_coe]

/-- `ofInt` adds the bias. -/
theorem ofInt_eq (w n : Nat) (z : Int) : ofInt w n z = (z + bias w n).toNat := rfl

/-- `lanes w n u` has `n` lanes. -/
theorem length_lanes (w n u : Nat) : (lanes w n u).length = n := by simp [lanes]

/-- Every lane has `w` bits. -/
theorem lt_of_mem_lanes {w n u d : Nat} (h : d ∈ lanes w n u) : d < 2 ^ w := by
  simp only [lanes, List.mem_map] at h
  obtain ⟨k, _, rfl⟩ := h
  exact lane_lt w k u

/-- The signed entries are the lanes minus the bias. -/
theorem entries_eq_lanes (w n u : Nat) :
    entries w n u = (lanes w n u).map fun (d : Nat) => (d : Int) - 2 ^ (w - 1) := by
  simp [entries, lanes, entry_eq]

/-- A row has as many entries as lanes. -/
theorem length_entries (w n u : Nat) : (entries w n u).length = n := by simp [entries]

/-- Entry `k` of `entries w n u` is the entry in lane `k`. -/
theorem getElem_entries {w n k u : Nat} (hk : k < (entries w n u).length) :
    (entries w n u)[k] = entry w k u := by simp [entries]

/-! ### Row algebra -/

/-- The value of one row followed by another. -/
theorem eval_append (b : Int) (xs ys : List Int) :
    eval b (xs ++ ys) = eval b xs + b ^ xs.length * eval b ys := by
  induction xs with
  | nil => simp [eval]
  | cons x xs ih => simp only [List.cons_append, eval, ih, List.length_cons, Int.pow_succ]; grind

/-- A row of zeros has value zero. -/
@[simp] theorem eval_zeros (b : Int) (k : Nat) : eval b (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, eval, ih]

/-- The cast of a power of two, with the integer literal `2` on the right, the form in which `omega`
matches the two sides. -/
theorem natCast_two_pow (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := rfl

/-- `shift` puts `k` zero entries in front of a row. -/
theorem shift_eval (w k : Nat) (xs : List Int) :
    shift w k (eval (2 ^ w) xs) = eval (2 ^ w) (List.replicate k 0 ++ xs) := by
  simp only [eval_append, eval_zeros, List.length_replicate, Int.zero_add, ← Int.pow_mul, shift,
    pow2_eq, Nat.mul_eq, Int.ofNat_eq_natCast, natCast_two_pow, Int.mul_def, Int.mul_comm]

/-- `eval` is additive. -/
theorem eval_add (b : Int) : ∀ xs ys, eval b (add xs ys) = eval b xs + eval b ys
  | [], ys => by simp [add, eval]
  | x :: xs, [] => by simp [add, eval]
  | x :: xs, y :: ys => by simp only [add, eval, eval_add b xs ys]; grind

/-- `eval` commutes with scaling. -/
theorem eval_smul (b c : Int) (xs : List Int) : eval b (smul c xs) = c * eval b xs := by
  induction xs with
  | nil => simp [smul, eval]
  | cons x xs ih =>
      simp only [smul, List.map_cons, eval] at *
      rw [ih]; grind

/-- `eval` takes differences to differences. -/
theorem eval_sub (b : Int) (xs ys : List Int) : eval b (sub xs ys) = eval b xs - eval b ys := by
  simp only [sub, eval_add, eval_smul]; grind

/-- Kronecker substitution: the value of the Cauchy product is the product of the values. -/
theorem eval_conv (b : Int) : ∀ xs ys, eval b (conv xs ys) = eval b xs * eval b ys
  | [], ys => by simp [conv, eval]
  | x :: xs, ys => by simp only [conv, eval_add, eval_smul, eval, eval_conv b xs ys]; grind

/-- Negating the value negates every entry. -/
theorem neg_eval (b : Int) (xs : List Int) : -eval b xs = eval b (xs.map fun x => -x) := by
  have := eval_smul b (-1) xs
  simp only [smul] at this
  rw [show (xs.map fun x => -x) = xs.map ((-1) * ·) by simp, this]; omega

/-- `l1` of a cons. -/
theorem l1_cons (x : Int) (xs : List Int) : l1 (x :: xs) = x.natAbs + l1 xs := by simp [l1]

/-- The triangle inequality for `l1`. -/
theorem l1_add_le : ∀ xs ys, l1 (add xs ys) ≤ l1 xs + l1 ys
  | [], ys => by simp [add, l1]
  | x :: xs, [] => by simp [add, l1]
  | x :: xs, y :: ys => by
      simp only [add, l1_cons]
      have := l1_add_le xs ys
      have := Int.natAbs_add_le x y
      omega

/-- `l1` is homogeneous. -/
theorem l1_smul (c : Int) (xs : List Int) : l1 (smul c xs) = c.natAbs * l1 xs := by
  induction xs with
  | nil => simp [smul, l1]
  | cons x xs ih =>
      simp only [smul, List.map_cons] at *
      rw [l1_cons, l1_cons, ih, Int.natAbs_mul, Nat.mul_add]

/-- The triangle inequality for differences. -/
theorem l1_sub_le (xs ys : List Int) : l1 (sub xs ys) ≤ l1 xs + l1 ys := by
  have h1 := l1_add_le xs (smul (-1) ys)
  rw [l1_smul] at h1
  simpa [sub] using h1

/-- `l1` is submultiplicative: the lanes of a product are bounded before it is formed. -/
theorem l1_conv_le : ∀ xs ys, l1 (conv xs ys) ≤ l1 xs * l1 ys
  | [], ys => by simp [conv, l1]
  | x :: xs, ys => by
      simp only [conv]
      have h1 := l1_add_le (smul x ys) (0 :: conv xs ys)
      have h2 := l1_conv_le xs ys
      rw [l1_smul, l1_cons] at h1
      rw [l1_cons, Nat.add_mul]
      simp at h1
      omega

/-- Sums of nonnegative rows are nonnegative. -/
theorem nonneg_of_mem_add : ∀ {xs ys : List Int}, (∀ x ∈ xs, 0 ≤ x) → (∀ y ∈ ys, 0 ≤ y) →
    ∀ z ∈ add xs ys, 0 ≤ z
  | [], _, _, hy => by simpa [add] using hy
  | _ :: _, [], hx, _ => by simpa [add] using hx
  | x :: xs, y :: ys, hx, hy => by
      intro z hz
      simp only [add, List.mem_cons] at hz
      rcases hz with rfl | hz
      · have := hx x (by simp); have := hy y (by simp); omega
      · exact nonneg_of_mem_add (fun a ha => hx a (by simp [ha])) (fun a ha => hy a (by simp [ha]))
          z hz

/-- The Cauchy product of nonnegative rows is nonnegative. -/
theorem nonneg_of_mem_conv : ∀ {xs ys : List Int}, (∀ x ∈ xs, 0 ≤ x) → (∀ y ∈ ys, 0 ≤ y) →
    ∀ z ∈ conv xs ys, 0 ≤ z
  | [], _, _, _ => by simp [conv]
  | x :: xs, ys, hx, hy => by
      simp only [conv]
      apply nonneg_of_mem_add
      · intro z hz
        simp only [smul, List.mem_map] at hz
        obtain ⟨y, hy', rfl⟩ := hz
        exact Int.mul_nonneg (hx x (by simp)) (hy y hy')
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Int.le_refl 0
        · exact nonneg_of_mem_conv (fun a ha => hx a (by simp [ha])) hy z hz

/-- Reversal leaves `l1` unchanged. -/
theorem l1_reverse (xs : List Int) : l1 xs.reverse = l1 xs := by
  simp [l1, List.map_reverse, List.sum_reverse]

/-- The `l1` norm of a concatenation is the sum of the two norms. -/
theorem l1_append (xs ys : List Int) : l1 (xs ++ ys) = l1 xs + l1 ys := by
  simp [l1, List.map_append, List.sum_append]

/-- A row of zeros has `l1` norm zero. -/
@[simp] theorem l1_zeros (k : Nat) : l1 (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, l1_cons, ih]

/-- Each entry is bounded by `l1`. -/
theorem natAbs_le_l1 {x : Int} : ∀ {xs : List Int}, x ∈ xs → x.natAbs ≤ l1 xs
  | [], h => by simp at h
  | y :: ys, h => by
      rw [l1_cons]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := natAbs_le_l1 h; omega

/-- Entries whose `l1` is below `2 ^ (w - 1)` fit width `w`. -/
theorem fits_of_l1_lt {w : Nat} {xs : List Int} (h : l1 xs < 2 ^ (w - 1)) :
    ∀ x ∈ xs, Fits w x := by
  intro x hx
  have h1 := natAbs_le_l1 hx
  have e := natCast_two_pow (w - 1)
  constructor <;> omega

/-- `l1` of entries in `[-2 ^ g, 2 ^ g)`. -/
theorem l1_le_of_bound {g : Nat} : ∀ {xs : List Int}, (∀ x ∈ xs, -2 ^ g ≤ x ∧ x < 2 ^ g) →
    l1 xs ≤ xs.length * 2 ^ g
  | [], _ => by simp [l1]
  | x :: xs, h => by
      have ih := l1_le_of_bound (xs := xs) (fun y hy => h y (by simp [hy]))
      have hx := h x (by simp)
      have e := natCast_two_pow g
      rw [l1_cons, List.length_cons, Nat.succ_mul]
      omega

/-- The sum of two rows is as long as the longer one. -/
theorem length_add {α : Type} [Add α] :
    ∀ xs ys : List α, (add xs ys).length = max xs.length ys.length
  | [], ys => by simp [add]
  | x :: xs, [] => by simp [add]
  | x :: xs, y :: ys => by simp [add, length_add xs ys, Nat.succ_max_succ]

/-- The Cauchy product of two nonempty rows has `xs.length + ys.length - 1` entries. -/
theorem length_conv {ys : List Int} (hys : ys ≠ []) :
    ∀ {xs : List Int}, xs ≠ [] → (conv xs ys).length = xs.length + ys.length - 1
  | [x], _ => by
      have : 1 ≤ ys.length := List.length_pos_iff.mpr hys
      simp [conv, length_add, smul]; omega
  | x :: x' :: xs, _ => by
      have ih := length_conv hys (xs := x' :: xs) (by simp)
      have : 1 ≤ ys.length := List.length_pos_iff.mpr hys
      simp only [conv] at ih ⊢
      simp only [length_add, smul, List.length_map, List.length_cons] at ih ⊢
      omega

/-- A length bound for the Cauchy product that holds for empty rows too: `conv xs []` is a row of
`xs.length` zeros and `conv [] ys` is empty. -/
theorem length_conv_le : ∀ xs ys, (conv xs ys).length ≤ xs.length + (ys.length - 1)
  | [], ys => by simp [conv]
  | x :: xs, ys => by
      have ih := length_conv_le xs ys
      simp only [conv, length_add, smul, List.length_map, List.length_cons]
      omega

/-- What a passing `linked` says, entry by entry. -/
theorem linked_sound {w d u : Nat} : ∀ {k : Nat} {xs : List Rat}, linked w d u k xs = true →
    ∀ i (hi : i < xs.length), xs[i].num * d = entry w (k + i) u * xs[i].den
  | _, [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k, x :: xs, h, i, hi => by
      simp only [linked, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero => simpa [Int.mul_def] using h.1
      | succ i =>
          have := linked_sound h.2 i (by simpa using hi)
          rwa [show k + 1 + i = k + (i + 1) by omega] at this

end FloatLib.Numerics.Packed
