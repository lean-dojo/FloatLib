/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Interval.Constraints.Search
public meta import FloatLib.Util.Polynomial
public meta import Mathlib.Tactic.Positivity
public meta import Mathlib.Tactic.Ring

/-!
# Quadratic forms of comparisons

A comparison `a ≤ b` that holds outright gives the form atom `Q ≤ 0` once `a - b` is written as a
quadratic form `Q` in shifted variables. This module finds such a form and proves the identity.

The difference is expanded as a polynomial with rational coefficients in generators: the atoms
that are coordinates, shifted by their centers, and every subterm that is not arithmetic, such as
a function value or the inverse of a denominator. Each monomial is assigned to one entry of the
matrix: to a diagonal entry when a coordinate occurs squared, to an off-diagonal entry otherwise,
and to the row of the constant one when it has fewer than two coordinates. A coordinate is the
shifted atom itself, or its square where the form starts at degree four in that atom. What is
left of the monomial is the entry, so an entry is a polynomial in the generators, enclosed by
intervals on a box. `ring` proves that the form with these entries is the difference, and the
entries are reified like every other expression.

The same construction serves a combination `a - b + μ * (c - d)` of two comparisons with a
multiplier `μ ≥ 0`, and the bound of a variable on a sublevel set (`deriveBounds`), where the
form of `a - b - λ * (x ^ 2 - e ^ 2)` with the constant one among its coordinates is positive
definite on the whole space.

## Main definitions

* `expand`: expansion in the sparse polynomials of `FloatLib.Util.Polynomial`.
* `FormData`, `FormData.ofPoly`: a form as coordinates and polynomial entries.
* `FormData.screen`: an untrusted test of definiteness from enclosures of the generators.
* `formPiece`: the form atom of a combination of comparisons, with its proof.
* `simplest`: the rational of least denominator in an interval, the center of a stuck box.
-/

public meta section

open Lean Meta Qq FloatLib.Util.Polynomial

namespace FloatLib.Numerics.Interval.Tactic.Constraints


/-- The generators of an expansion: their real terms, and the coordinate of each atom that is
one, as its center and the generator of the shifted atom. -/
structure Generators where
  /-- The real term of each generator. -/
  terms : Array Q(ℝ) := #[]
  /-- For an atom that is a coordinate: its center and the generator of the atom minus it. -/
  shifted : Std.HashMap Nat (ℚ × Nat) := {}

/-- The generator of a real term, added when it is new. -/
def generator (e : Q(ℝ)) : StateRefT Generators MetaM Nat := do
  let state ← get
  if let some i := state.terms.findIdx? (· == e) then return i
  set { state with terms := state.terms.push e }
  return state.terms.size

/-- A rational as a real numeral. -/
def ratTerm (c : ℚ) : MetaM Q(ℝ) := do
  let num : Q(ℝ) ← mkNumeral q(ℝ) c.num.natAbs
  let num : Q(ℝ) := if c.num < 0 then q(-$num) else num
  if c.den == 1 then return num
  let den : Q(ℝ) ← mkNumeral q(ℝ) c.den
  return q($num / $den)

/-- Make the atoms with the given centers coordinates: each gets the generator of the atom
minus its center. -/
def shiftAtoms (atoms : Array Q(ℝ)) (centers : Array (Nat × ℚ)) :
    StateRefT Generators MetaM Unit := do
  for (i, center) in centers do
    let some (atom : Q(ℝ)) := atoms[i]? | continue
    let literal ← ratTerm center
    let index ← generator q($atom - $literal)
    modify fun state => { state with shifted := state.shifted.insert i (center, index) }

/--
Expand a real term as a polynomial in generators. Sums, differences, products, natural powers,
negations and divisions by numerals are expanded; a division by another term multiplies by the
generator of its inverse; an atom that is a coordinate is its shifted generator plus its center;
any other term is a generator.
-/
partial def expand (atoms : Array Q(ℝ)) (e : Q(ℝ)) : StateRefT Generators MetaM Poly :=
  withIncRecDepth do
    let e : Q(ℝ) ← instantiateMVars e
    have e : Q(ℝ) := e.consumeMData
    if let some i := atoms.findIdx? (· == e) then
      match (← get).shifted[i]? with
      | some (center, index) => return (Poly.gen index).add (Poly.const center)
      | none => return Poly.gen (← generator e)
    if let some value ← rationalValue? e then return Poly.const value.value
    match e with
    | ~q($a + $b) => return (← expand atoms a).add (← expand atoms b)
    | ~q($a - $b) => return (← expand atoms a).add ((← expand atoms b).scale (-1))
    | ~q($a * $b) => return (← expand atoms a).mul (← expand atoms b)
    | ~q($a / $b) =>
      if let some value ← rationalValue? b then
        if value.value != 0 then return (← expand atoms a).scale value.value⁻¹
      return (← expand atoms a).mul (Poly.gen (← generator q($b⁻¹)))
    | ~q(-$a) => return (← expand atoms a).scale (-1)
    | ~q($a ^ ($n : ℕ)) =>
      match (← whnf n).rawNatLit? with
      | some n => return (← expand atoms a).pow n
      | none => return Poly.gen (← generator e)
    | _ => return Poly.gen (← generator e)

/-- The real term of a polynomial in generators. -/
def polyTerm (generators : Generators) (p : Poly) : MetaM Q(ℝ) := do
  let mut sum : Option Q(ℝ) := none
  for (monomial, coefficient) in p.monomials do
    let mut product : Option Q(ℝ) := none
    for (i, exponent) in monomial do
      let some (term : Q(ℝ)) := generators.terms[i]? | throwError "interval: unknown generator"
      have exponent' : Q(ℕ) := mkNatLit exponent
      let factor : Q(ℝ) := if exponent == 1 then term else q($term ^ $exponent')
      product := some (match product with
        | none => factor
        | some (previous : Q(ℝ)) => q($previous * $factor))
    let literal ← ratTerm coefficient
    let term : Q(ℝ) := match product with
      | none => literal
      | some (product : Q(ℝ)) => if coefficient == 1 then product else q($literal * $product)
    sum := some (match sum with
      | none => term
      | some (previous : Q(ℝ)) => q($previous + $term))
  return sum.getD q(0)

/-- A quadratic form as data: its coordinates, a power of an atom minus its center or the
constant one, and the upper triangle of its matrix as polynomials in the generators. -/
structure FormData where
  /-- The coordinates: an atom, its center and its power minus one, or `none` for the constant
  one. -/
  coordinates : Array (Option (Nat × ℚ × Nat))
  /-- The entries `(k, l)` with `k ≤ l`. -/
  entries : Std.HashMap (Nat × Nat) Poly

/-- Where the monomials of a polynomial go in the matrix of its form: the shifted generators,
the index of the constant one, and for each shifted generator the lowest degree that it has in a
monomial without another shifted generator. -/
structure Layout where
  /-- Generator of a shifted atom ↦ the atom and its center. -/
  shifted : Std.HashMap Nat (Nat × ℚ)
  /-- The index that stands for the constant one: past every generator. -/
  one : Nat
  /-- The lowest degree of each shifted generator in a monomial that has no other. -/
  lowest : Std.HashMap Nat Nat

/-- The layout of the form of a polynomial. It depends on the monomials of the polynomial and
not on their coefficients. -/
def Layout.of (generators : Generators) (p : Poly) : Layout := Id.run do
  let shifted : Std.HashMap Nat (Nat × ℚ) := generators.shifted.fold (init := {})
    fun acc atom (center, index) => acc.insert index (atom, center)
  let mut lowest : Std.HashMap Nat Nat := {}
  for (monomial, _) in p.monomials do
    if let [(i, e)] := monomial.filter fun (i, _) => shifted.contains i then
      lowest := lowest.insert i (min e (lowest.getD i e))
  return { shifted, one := generators.terms.size, lowest }

/-- The power of a shifted generator that is its coordinate. -/
def Layout.power (layout : Layout) (i : Nat) : Nat := max 1 ((layout.lowest.getD i 2 + 1) / 2)

/-- The entry of the matrix that a monomial goes to, as two generators or the constant one, and
what is left of the monomial there. -/
def Layout.place (layout : Layout) (monomial : Monomial) : (Nat × Nat) × Monomial :=
  let coordinates := monomial.filter fun (i, e) =>
    layout.shifted.contains i && layout.power i ≤ e
  let (k, l) : Nat × Nat :=
    match coordinates.find? fun (i, e) => 2 * layout.power i ≤ e with
    | some (i, _) => (i, i)
    | none =>
      match coordinates with
      | (i, _) :: (j, _) :: _ => (i, j)
      | [(i, _)] => (i, layout.one)
      | [] => (layout.one, layout.one)
  let remove (m : Monomial) (i : Nat) : Monomial := m.filterMap fun (j, e) =>
    if j == i then (if e ≤ layout.power i then none else some (j, e - layout.power i))
    else some (j, e)
  ((k, l), remove (remove monomial k) l)

/-- The generators and the constant one that some entries of a matrix use, in increasing order,
so that the constant one is last. -/
def Layout.used {α : Type} (raw : Std.HashMap (Nat × Nat) α) : Array Nat :=
  (raw.fold (init := #[]) fun acc (k, l) _ =>
    let acc := if acc.contains k then acc else acc.push k
    if acc.contains l then acc else acc.push l).qsort (· < ·)

/--
Write a polynomial as a quadratic form in powers of the shifted generators. The coordinate of a
shifted generator `d` is `d ^ p`, where `2 * p` is the lowest degree of `d` in the monomials that
contain no other shifted generator, rounded up (so `p = 1` when `d ^ 2` occurs, and `p = 2` when
`d ^ 4` is the lowest power). A monomial that contains the square of a coordinate goes to that
diagonal entry, one with two coordinates to their off-diagonal entry (halved, since the form
counts it twice), and one with fewer to the row of the constant one. What is left of the monomial
is the entry. Coordinates that no monomial uses are left out.
-/
def FormData.ofPoly (generators : Generators) (p : Poly) : FormData := Id.run do
  let layout := Layout.of generators p
  let mut raw : Std.HashMap (Nat × Nat) Poly := {}
  for (monomial, coefficient) in p.monomials do
    let ((k, l), rest) := layout.place monomial
    let share := if k == l then coefficient else coefficient / 2
    raw := raw.insert (k, l) ((raw.getD (k, l) {}).addMonomial rest share)
  -- the coordinates in use, the constant one last
  let used := Layout.used raw
  let position (i : Nat) : Nat := used.findIdx? (· == i) |>.getD 0
  let entries := raw.fold (init := {}) fun acc (k, l) q => acc.insert (position k, position l) q
  return { coordinates := used.map fun i => layout.shifted[i]?.map fun (atom, center) =>
    (atom, center, layout.power i - 1), entries }

/-- The enclosure of a polynomial from enclosures of its generators, by the exact rational
operations of the interval layer; there is none when a generator of the polynomial has none. -/
def polynomialRange (ranges : Array (Option (Interval ℚ))) (p : Poly) : Option (Interval ℚ) := do
  let B := Backend.rational {}
  let mut sum : Interval ℚ := ⟨0, 0⟩
  for (monomial, coefficient) in p.monomials do
    let mut product : Interval ℚ := ⟨coefficient, coefficient⟩
    for (i, exponent) in monomial do
      let factor ← B.unary? (.pow exponent) (← (ranges[i]?).join)
      product ← B.binary? .mul product factor
    sum ← B.binary? .add sum product
  return sum

/-- The smallest lower end of a pivot when an interval matrix is eliminated as `Form.definite`
does, up to the first pivot that it rejects: positive exactly when `Form.definite` accepts the
matrix, as positive definite when `strict` and semidefinite otherwise. A matrix without pivots
has the margin `10 ^ 30`, and one whose elimination fails `-10 ^ 30`. -/
partial def pivotMargin (strict : Bool) : List (List (Interval ℚ)) → ℚ
  | (a :: border) :: rows =>
    if 0 < a.lo then
      match Form.reduce (Backend.rational {}) a border rows with
      | none => -(10 : ℚ) ^ 30
      | some reduced => min a.lo (pivotMargin strict reduced)
    else if !strict && a.lo == 0 && border.all (fun t => t.lo == 0 && t.hi == 0) then
      pivotMargin strict rows
    else min a.lo (-(1 : ℚ) / 10 ^ 30)
  | [] => (10 : ℚ) ^ 30
  | [] :: _ => -(10 : ℚ) ^ 30

/-- The margin of definiteness of a form, given enclosures of the generators: `pivotMargin` of
its interval matrix, and `-10 ^ 30` when an entry has no enclosure. -/
def FormData.margin (data : FormData) (ranges : Array (Option (Interval ℚ))) (strict : Bool) :
    ℚ :=
  let n := data.coordinates.size
  let rows := (List.range n).mapM fun k => (List.range (n - k)).mapM fun offset =>
    polynomialRange ranges (data.entries.getD (k, k + offset) {})
  match rows with
  | some rows => pivotMargin strict rows
  | none => -(10 : ℚ) ^ 30

/-- An untrusted test that a form is positive definite, or semidefinite when not `strict`, given
enclosures of the generators: whether its margin is positive. -/
def FormData.screen (data : FormData) (ranges : Array (Option (Interval ℚ))) (strict : Bool) :
    Bool :=
  0 < data.margin ranges strict

/-- The enclosure of a monomial from enclosures of its generators, by the exact rational
operations of the interval layer. -/
def monomialRange (ranges : Array (Option (Interval ℚ))) (monomial : Monomial) :
    Option (Interval ℚ) := do
  let B := Backend.rational {}
  let mut product : Interval ℚ := ⟨1, 1⟩
  for (i, exponent) in monomial do
    let factor ← B.unary? (.pow exponent) (← (ranges[i]?).join)
    product ← B.binary? .mul product factor
  return product

/--
What the margin of definiteness of the form of `p + μ * q` needs at every `μ`, given enclosures
of the generators. A search for a multiplier asks for the margin at some two hundred values of
`μ`, so what does not depend on `μ` is computed once: the layout of the form, which is that of
the monomials of `p` and of `q` together as long as none of them cancels, and the enclosure of
what each monomial leaves in its entry. An entry is then a sum of these enclosures with the
coefficients `c + μ * d`.
-/
structure Margins where
  /-- The generators of `p` and `q`. -/
  generators : Generators
  /-- The polynomial that the multiplier does not scale. -/
  p : Poly
  /-- The polynomial that the multiplier scales. -/
  q : Poly
  /-- The enclosures of the generators. -/
  ranges : Array (Option (Interval ℚ))
  /-- Whether the form has to be positive definite, or semidefinite only. -/
  strict : Bool
  /-- The upper triangle of the matrix by rows: each entry as the monomials that are left in it,
  with their coefficients in `p` and in `q` and their enclosures. -/
  rows : List (List (Array (ℚ × ℚ × Option (Interval ℚ))))
  /-- The coefficients of the monomials that `p` and `q` share: these cancel at some `μ`. -/
  shared : Array (ℚ × ℚ)

/-- The table for the margins of the forms of `p + μ * q`. -/
def Margins.of (generators : Generators) (p q : Poly) (ranges : Array (Option (Interval ℚ)))
    (strict : Bool) : Margins :=
  let union : Poly := q.fold (init := p.fold (init := {}) fun acc m _ => acc.insert m 1)
    fun acc m _ => acc.insert m 1
  let layout := Layout.of generators union
  -- each entry: what its monomials leave, with the coefficients in `p` and in `q`
  let raw : Std.HashMap (Nat × Nat) (Std.HashMap Monomial (ℚ × ℚ)) :=
    union.fold (init := {}) fun acc m _ =>
      let (key, rest) := layout.place m
      let share (c : ℚ) : ℚ := if key.1 == key.2 then c else c / 2
      let terms := acc.getD key {}
      let (c, d) := terms.getD rest (0, 0)
      acc.insert key (terms.insert rest (c + share (p.getD m 0), d + share (q.getD m 0)))
  let used := Layout.used raw
  let n := used.size
  { generators, p, q, ranges, strict
    rows := (List.range n).map fun k => (List.range (n - k)).map fun offset =>
      ((raw.getD (used.getD k 0, used.getD (k + offset) 0) {}).toArray.map fun (rest, c, d) =>
        (c, d, monomialRange ranges rest))
    shared := p.fold (init := #[]) fun acc m c =>
      match q[m]? with
      | some d => acc.push (c, d)
      | none => acc }

/-- The margin of definiteness of the form of `p + μ * q`:
`(FormData.ofPoly generators (p.add (q.scale μ))).margin ranges strict`. At a `μ` where a
monomial cancels, and at zero, the form is built as it is defined; elsewhere its entries are
read off the table. -/
def Margins.at (table : Margins) (μ : ℚ) : ℚ :=
  if μ == 0 || table.shared.any (fun (c, d) => c + μ * d == 0) then
    (FormData.ofPoly table.generators (table.p.add (table.q.scale μ))).margin table.ranges
      table.strict
  else
    let entry (terms : Array (ℚ × ℚ × Option (Interval ℚ))) : Option (Interval ℚ) := do
      let B := Backend.rational {}
      let mut sum : Interval ℚ := ⟨0, 0⟩
      for (c, d, range?) in terms do
        let coefficient := c + μ * d
        if coefficient == 0 then continue
        let product ← B.binary? .mul ⟨coefficient, coefficient⟩ (← range?)
        sum ← B.binary? .add sum product
      return sum
    match table.rows.mapM fun row => row.mapM entry with
    | some rows => pivotMargin table.strict rows
    | none => -(10 : ℚ) ^ 30

/--
The multipliers between `lower` and `upper` that a search need look at: the range of the `μ`
that give every diagonal entry of the matrix a nonnegative lower end, or `none` when there is no
such `μ`. A pivot is at most its diagonal entry, so outside this range no form of `p + μ * q`
passes the test of definiteness. The lower end of a diagonal entry is a concave function of
`μ`, linear between the values at which a coefficient `c + μ * d` changes its sign, so its sign
is read off at these values. The range is the whole of `[lower, upper]` when an enclosure is
missing, and when a monomial cancels at some `μ` of it, where the form has another layout.
-/
def Margins.admits (table : Margins) (lower : ℚ := 1 / 2 ^ 12) (upper : ℚ := 2 ^ 12) :
    Option (ℚ × ℚ) := Id.run do
  if table.shared.any fun (c, d) => d != 0 && lower ≤ -c / d && -c / d ≤ upper then
    return some (lower, upper)
  -- the values of `μ` that the diagonal entries admit so far
  let mut low := lower
  let mut high := upper
  for row in table.rows do
    let some terms := row.head? | continue
    if terms.any fun (c, d, range?) => range?.isNone && (c != 0 || d != 0) then
      return some (lower, upper)
    let value (μ : ℚ) : ℚ := terms.foldl (init := 0) fun sum (c, d, range?) =>
      match range? with
      | some I =>
        let coefficient := c + μ * d
        sum + (if 0 ≤ coefficient then coefficient * I.lo else coefficient * I.hi)
      | none => sum
    let inside := (terms.filterMap fun (c, d, _) =>
      if d == 0 then none
      else if low < -c / d && -c / d < high then some (-c / d) else none).qsort (· < ·)
    let points := (#[low] ++ inside).push high
    let values := points.map value
    -- where the lower end passes zero between two neighbours, the first of which is negative
    let crossing (i j : Nat) : ℚ :=
      let (p, q, v, w) := (points.getD i 0, points.getD j 0, values.getD i 0, values.getD j 0)
      p + (q - p) * (-v) / (w - v)
    let some first := (List.range points.size).find? fun i => 0 ≤ values.getD i 0
      | return none
    let some last := (List.range points.size).reverse.find? fun i => 0 ≤ values.getD i 0
      | return none
    low := if first == 0 then points.getD 0 low else crossing (first - 1) first
    high := if last + 1 == points.size then points.getD last high else crossing (last + 1) last
    if high < low then return none
  return some (low, high)

/-- The rational of least denominator in a closed interval of rationals. -/
partial def simplest (lo hi : ℚ) : ℚ :=
  if lo ≤ 0 ∧ 0 ≤ hi then 0
  else if hi < 0 then -(simplest (-hi) (-lo))
  else
    let whole : ℚ := (Rat.ceil lo : ℤ)
    if whole ≤ hi then whole
    else
      let floor : ℚ := (Rat.floor lo : ℤ)
      floor + (simplest (hi - floor)⁻¹ (lo - floor)⁻¹)⁻¹

/--
A multiplier `μ > 0` at which a margin is positive, if the search finds one in the given range:
the best of the powers `2 ^ (k / 4)` between `2 ^ (-12)` and `2 ^ 12` that the range holds (or
its middle, when it holds none), refined between its neighbours by ternary search. For two
quadratics the set of such `μ` is an interval, which may be narrow, and one point when the two
sets touch: the simplest rational that the search leaves is tried after 48 steps of the
refinement, and again every 16 steps up to 112, by when the bracket has singled out a rational
with a denominator of five digits. The refinement ends early when its values do not come
closer to zero as the bracket narrows: sixteen steps narrow it 650 times, and a margin whose
maximum is zero or more gains more than a factor of 64 from that.
-/
def bestMultiplier (value : ℚ → ℚ) (range : ℚ × ℚ := (1 / 2 ^ 12, 2 ^ 12)) : Option ℚ :=
    Id.run do
  -- quarter powers of two as rationals: 2 ^ (k / 4) is about 2 ^ ⌊k / 4⌋ times 1, 1.19, 1.41, 1.68
  let powers : List ℚ := (List.range 97).map fun k =>
    (2 : ℚ) ^ ((k / 4 : Nat) - 12 : ℤ) * [1, 19 / 16, 181 / 128, 27 / 16].getD (k % 4) 1
  let inside := powers.filter fun μ => range.1 ≤ μ && μ ≤ range.2
  let grid := if inside.isEmpty then [(range.1 + range.2) / 2] else inside
  -- the multiplier one first, as long as the range holds it
  let mut index := (grid.findIdx? (· == 1)).getD 0
  let mut best : ℚ := grid.getD index 1
  let mut bestValue : ℚ := value best
  for μ in grid, k in [0:grid.length] do
    let v := value μ
    if bestValue < v then
      best := μ
      bestValue := v
      index := k
  if 0 < bestValue then return some best
  let mut low := if index == 0 then range.1 else grid.getD (index - 1) best
  let mut high := if index + 1 == grid.length then range.2 else grid.getD (index + 1) best
  let mut reference : Option ℚ := none
  for step in [0:112] do
    -- Two sets that touch admit one multiplier only: the simplest rational that is left, tried
    -- after 48 steps and then every 16, as the bracket leaves out more of the simpler ones.
    if 48 ≤ step && step % 16 == 0 then
      let last := simplest low high
      if 0 < value last then return some last
    let first := (2 * low + high) / 3
    let second := (low + 2 * high) / 3
    let (vFirst, vSecond) := (value first, value second)
    if 0 < vFirst then return some first
    if 0 < vSecond then return some second
    -- values that stay where they were sixteen steps ago are those of a negative maximum
    if step % 16 == 0 then
      let current := max vFirst vSecond
      if reference.any fun previous => current * 64 < previous then return none
      reference := some current
    if vFirst < vSecond then low := first else high := second
  let last := simplest low high
  if 0 < value last then return some last
  return none

/-- A real term with the value of an expression at the atoms, and the proof that they agree. -/
structure Valued where
  /-- The term as stated. -/
  source : Q(ℝ)
  /-- The value of the reified term. -/
  value : Q(ℝ)
  /-- `source = value`. -/
  proof : Lean.Expr

/-- Apply a binary operation to two valued terms. -/
def Valued.binary (f : Q(ℝ → ℝ → ℝ)) (a b : Valued) : Valued :=
  have sa : Q(ℝ) := a.source
  have va : Q(ℝ) := a.value
  have sb : Q(ℝ) := b.source
  have vb : Q(ℝ) := b.value
  have pa : Q($sa = $va) := a.proof
  have pb : Q($sb = $vb) := b.proof
  ⟨q($f $sa $sb), q($f $va $vb), q(congrArg₂ $f $pa $pb)⟩

/-- A term that is its own value. -/
def Valued.same (e : Q(ℝ)) : Valued := ⟨e, e, q(Eq.refl $e)⟩

/-- A form with the proof that it is a combination `a - b + μ * (c - d)`. -/
structure FormIdentity where
  /-- The form for the search. -/
  form : Form
  /-- The form as a term. -/
  quoted : Q(Form)
  /-- The multiplier `μ` as a term. -/
  multiplier : Q(ℝ)
  /-- A proof of `a - b + μ * (c - d) = Form.eval quoted values functions`. -/
  equation : BuildM Lean.Expr

/-- The form atom of a combination of comparisons that hold outright, ready to be assembled. -/
structure FormPiece where
  /-- The form for the search. -/
  form : Form
  /-- The piece: the constraint and its proof. -/
  piece : Piece

/-- The expansions of the differences of one or two comparisons in common generators. -/
structure Expansion where
  /-- The comparison `a ≤ b` or `a < b`. -/
  first : Literal
  /-- The comparison `c ≤ d` or `c < d` that a multiplier adds, if any. -/
  second : Option Literal
  /-- The generators. -/
  generators : Generators
  /-- `a - b`. -/
  firstPoly : Poly
  /-- `c - d`, or zero. -/
  secondPoly : Poly

/-- Expand the differences of one or two comparisons, with the given centers for the atoms that
are coordinates. -/
def Expansion.of (atoms : Array Q(ℝ)) (first : Literal) (second : Option Literal)
    (centers : Array (Nat × ℚ)) : MetaM Expansion := do
  have a : Q(ℝ) := first.lhs
  have b : Q(ℝ) := first.rhs
  let ((firstPoly, secondPoly), generators) ← (do
    shiftAtoms atoms centers
    let p ← expand atoms q($a - $b)
    let q ← match second with
      | some other =>
        have c : Q(ℝ) := other.lhs
        have d : Q(ℝ) := other.rhs
        expand atoms q($c - $d)
      | none => pure {}
    return (p, q)).run {}
  return { first, second, generators, firstPoly, secondPoly }

/-- The form of `a - b + μ * (c - d)`. -/
def Expansion.data (expansion : Expansion) (multiplier : ℚ) : FormData :=
  FormData.ofPoly expansion.generators
    (expansion.firstPoly.add (expansion.secondPoly.scale multiplier))

/-- The table for the margins of definiteness of the forms of `a - b + μ * (c - d)`, given
enclosures of the generators: `Margins.at` is the margin of `expansion.data μ`. -/
def Expansion.margins (expansion : Expansion) (ranges : Array (Option (Interval ℚ)))
    (strict : Bool) : Margins :=
  Margins.of expansion.generators expansion.firstPoly expansion.secondPoly ranges strict

/-- Whether a difference is a bound on one generator: it has no product of generators and at
most one generator. -/
def Expansion.isBound (expansion : Expansion) : Bool :=
  expansion.firstPoly.monomials.all (fun (monomial, _) =>
    monomial.length ≤ 1 && monomial.all (·.2 ≤ 1)) &&
    (expansion.firstPoly.monomials.filter (!·.1.isEmpty)).size ≤ 1

/-- Whether a difference is a polynomial of degree at most two in the coordinates with rational
coefficients, so that its form has a constant matrix. -/
def Expansion.isQuadratic (expansion : Expansion) : Bool :=
  let coordinates := expansion.generators.shifted.fold (init := #[]) fun acc _ (_, g) => acc.push g
  expansion.firstPoly.monomials.all fun (monomial, _) =>
    monomial.all (fun (g, _) => coordinates.contains g) &&
      monomial.foldl (fun degree (_, e) => degree + e) 0 ≤ 2

/-- Whether a difference has degree at most two in the coordinates, so that the entries of the
matrix of its form contain no coordinate. -/
def Expansion.degreeTwo (expansion : Expansion) : Bool :=
  let coordinates := expansion.generators.shifted.fold (init := #[]) fun acc _ (_, g) => acc.push g
  expansion.firstPoly.monomials.all fun (monomial, _) =>
    (monomial.filter fun (g, _) => coordinates.contains g).foldl
      (fun degree (_, e) => degree + e) 0 ≤ 2

/-- The enclosures of the generators on a box, by reifying their terms: `none` for a generator
that the box does not enclose. -/
def Expansion.ranges (expansion : Expansion) (oracle : Oracle) :
    StateRefT ReifyState MetaM (Array (Option (Interval ℚ))) := do
  let mut ranges := #[]
  for term in expansion.generators.terms do
    let expression ← reify term
    ranges := ranges.push (oracle.range (← Diagnostics.readExpr expression true))
  return ranges

/-- The comparison `0 ≤ 0`, the second comparison of a form of one comparison alone. -/
def Literal.trivial : Literal := ⟨false, q(0), q(0), q(le_refl (0 : ℝ))⟩

/--
The form of `a - b + μ * (c - d)` with given coordinates and entries, with the proof of the
identity. `entry k l` is the real term of the entry `(k, l)` for `k ≤ l`. The entries are reified
in the current state, and `ring` proves that the form with these entries is the combination. The
result is `none` when `ring` fails.
-/
def formIdentityOf (atoms : Array Q(ℝ)) (first second : Literal) (multiplier : ℚ)
    (shape : Array (Option (Nat × ℚ × Nat))) (entry : Nat → Nat → MetaM Q(ℝ)) :
    StateRefT ReifyState MetaM (Option FormIdentity) := do
  have a : Q(ℝ) := first.lhs
  have b : Q(ℝ) := first.rhs
  have c : Q(ℝ) := second.lhs
  have d : Q(ℝ) := second.rhs
  let μ ← ratTerm multiplier
  let combination : Q(ℝ) := q($a - $b + $μ * ($c - $d))
  let n := shape.size
  -- the coordinates
  let mut shifts : Array Shift := #[]
  let mut quotedShifts : Array Q(Shift) := #[]
  let mut coordinates : Array (MetaM Valued) := #[]
  for coordinate in shape do
    match coordinate with
    | none =>
      shifts := shifts.push .one
      quotedShifts := quotedShifts.push q(Shift.one)
      coordinates := coordinates.push (pure (Valued.same q(1)))
    | some (i, center, extra) =>
      let some (atom : Q(ℝ)) := atoms[i]? | return none
      let literal ← ratTerm center
      let some value ← rationalValue? literal | return none
      have rational : Q(ℚ) := value.rational
      have index : Q(ℕ) := mkNatLit i
      have less : Q(ℕ) := mkNatLit extra
      have equality : Q($literal = ($rational : ℝ)) := value.equality
      shifts := shifts.push (.var i center extra)
      quotedShifts := quotedShifts.push q(Shift.var $index $rational $less)
      coordinates := coordinates.push (pure ⟨q(($atom - $literal) ^ ($less + 1)),
        q(($atom - ($rational : ℝ)) ^ ($less + 1)),
        q(congrArg (fun t => ($atom - t) ^ ($less + 1)) $equality)⟩)
  -- the entries, reified
  let mut rows : Array (Array (Q(ℝ) × Q(Interval.Expr) × Interval.Expr)) := #[]
  for k in [0:n] do
    let mut row := #[]
    for l in [k:n] do
      let term ← entry k l
      let expression ← reify term
      row := row.push (term, expression, ← Diagnostics.readExpr expression true)
    rows := rows.push row
  let form : Form := ⟨shifts.toList, rows.toList.map fun row => row.toList.map (·.2.2)⟩
  have quotedCoordinates : Q(List Shift) := quotedShifts.foldr
    (fun (s : Q(Shift)) (rest : Q(List Shift)) => q($s :: $rest)) q([])
  have quotedRows : Q(List (List Interval.Expr)) := rows.foldr
    (fun row (rest : Q(List (List Interval.Expr))) =>
      have quotedRow : Q(List Interval.Expr) := row.foldr
        (fun entry (tail : Q(List Interval.Expr)) =>
          have expression : Q(Interval.Expr) := entry.2.1
          q($expression :: $tail)) q([])
      q($quotedRow :: $rest)) q([])
  have quotedForm : Q(Form) := q(Form.mk $quotedCoordinates $quotedRows)
  -- the form as a real term, in the shape that `Form.quad` unfolds to
  let assemble (entry : Nat → Nat → MetaM Valued) : MetaM Valued := do
    let add : Q(ℝ → ℝ → ℝ) := q(HAdd.hAdd)
    let mul : Q(ℝ → ℝ → ℝ) := q(HMul.hMul)
    let mut total := Valued.same q(0)
    for k' in [0:n] do
      let k := n - 1 - k'
      let dk ← coordinates.getD k (pure (Valued.same q(1)))
      let mut dot := Valued.same q(0)
      for l' in [k + 1:n] do
        let l := n + k - l'
        let dl ← coordinates.getD l (pure (Valued.same q(1)))
        dot := Valued.binary add (Valued.binary mul (← entry k l) dl) dot
      have sd : Q(ℝ) := dk.source
      have vd : Q(ℝ) := dk.value
      have pd : Q($sd = $vd) := dk.proof
      let square : Valued := ⟨q($sd ^ 2), q($vd ^ 2), q(congrArg (fun t => t ^ 2) $pd)⟩
      let diagonal := Valued.binary mul (← entry k k) square
      let cross := Valued.binary mul (Valued.binary mul (Valued.same q(2)) dk) dot
      total := Valued.binary add (Valued.binary add diagonal cross) total
    return total
  let entryAt (k l : Nat) : Q(ℝ) × Q(Interval.Expr) × Interval.Expr :=
    (rows.getD k #[]).getD (l - k) (q(0), q(Interval.Expr.const 0), .const 0)
  let stated ← assemble fun k l => return Valued.same (entryAt k l).1
  have statedTerm : Q(ℝ) := stated.source
  let goal ← mkFreshExprMVar q($combination = $statedTerm)
  try
    Mathlib.Tactic.AtomM.run .reducible (Mathlib.Tactic.Ring.proveEq goal.mvarId!)
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none
  let identity ← instantiateMVars goal
  return some {
    form, quoted := quotedForm, multiplier := μ
    equation := do
      let ctx ← read
      have values : Q(Nat → ℝ) := ctx.values
      have functions : Q(Nat → List ℝ → ℝ) := ctx.functions
      let valued ← assemble fun k l => do
        let (term, expression, _) := entryAt k l
        return ⟨term, q(Interval.Expr.eval $expression $values $functions),
          ← evalEquality term expression values ctx.cache functions⟩
      mkExpectedTypeHint (← mkEqTrans identity valued.proof)
        q($a - $b + $μ * ($c - $d) = Form.eval $quotedForm $values $functions) }

/--
The form of `a - b + μ * (c - d)` for an expansion and a rational `μ`, with the proof of the
identity: the coordinates and entries of `FormData.ofPoly`. A combination that is identically
zero is the form without coordinates.
-/
def formIdentity (atoms : Array Q(ℝ)) (expansion : Expansion) (multiplier : ℚ) :
    StateRefT ReifyState MetaM (Option FormIdentity) := do
  let data := expansion.data multiplier
  formIdentityOf atoms expansion.first (expansion.second.getD .trivial) multiplier
    data.coordinates fun k l => polyTerm expansion.generators (data.entries.getD (k, l) {})

/--
The form atom of a form that is `a - b + μ * (c - d)`, from comparisons `a ≤ b` (or `a < b`) and
`c ≤ d` that hold outright and `μ ≥ 0`: the piece proves the atom from the two comparisons and
the identity.
-/
def FormIdentity.piece (identity : FormIdentity) (first other : Literal) : FormPiece :=
  have a : Q(ℝ) := first.lhs
  have b : Q(ℝ) := first.rhs
  have c : Q(ℝ) := other.lhs
  have d : Q(ℝ) := other.rhs
  have μ : Q(ℝ) := identity.multiplier
  have quotedForm : Q(Form) := identity.quoted
  let strict := first.strict
  have quotedStrict : Q(Bool) := if strict then q(true) else q(false)
  let source := m!"{if strict then q($a < $b) else q($a ≤ $b)}"
  { form := identity.form, piece := {
    constraint := q(Constraint.form $quotedStrict $quotedForm)
    tree := .form strict identity.form source
    prove := fun _ _ => do
      let ctx ← read
      have values : Q(Nat → ℝ) := ctx.values
      have functions : Q(Nat → List ℝ → ℝ) := ctx.functions
      have heq : Q($a - $b + $μ * ($c - $d) = Form.eval $quotedForm $values $functions) :=
        ← identity.equation
      let some hμ ← positivityProof? q((0 : ℝ) ≤ $μ)
        | throwError "interval: the multiplier {μ} of a combination is not nonnegative"
      have h' : Q($c ≤ $d) := if other.strict then
        (have h : Q($c < $d) := other.proof; q(le_of_lt $h)) else other.proof
      if strict then
        have h : Q($a < $b) := first.proof
        return q(Constraint.holds_form_of_lt $heq $h $hμ $h')
      else
        have h : Q($a ≤ $b) := first.proof
        return q(Constraint.holds_form_of_le $heq $h $hμ $h') } }

/-- The form atom of `a - b + μ * (c - d)` for an expansion and a rational `μ ≥ 0`. -/
def formPiece (atoms : Array Q(ℝ)) (expansion : Expansion) (multiplier : ℚ) :
    StateRefT ReifyState MetaM (Option FormPiece) := do
  let some identity ← formIdentity atoms expansion multiplier | return none
  return some (identity.piece expansion.first (expansion.second.getD .trivial))

end FloatLib.Numerics.Interval.Tactic.Constraints
