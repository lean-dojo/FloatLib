/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Coeff.Bound
public meta import FloatLib.Numerics.Packed.Literal
public meta import Mathlib.Tactic.NormNum.Core
public meta import Mathlib.Tactic.Ring

/-!
# Reading a goal as series for `interval`

The coefficient route of `interval` needs the polynomial side of a goal as one or two coefficient
lists against a basis, `Coeff.series f xs`, together with a proof that the goal's term equals that
canonical form. This module does the reading. A term is read as a linear form in *atoms*: blocks
`∑ k ∈ Finset.range n, a k * f k` with the coefficient on either side or none, monomials such as
`Real.cos (2 * u)`, `Real.sin u`, `x ^ 3`, `x`, `(T ℝ 2).eval y` or `z`, and constants, combined by
sums, differences, negations and rational multiples (Gaussian rational multiples for `ℂ`).

For example, `1/2 + Real.cos u + Real.cos (2 * u) / 2` has the constant `1/2` and the atoms
`Real.cos u` and `Real.cos (2 * u)`, read as the lists `[0, 1]` and `[0, 0, 1]`. Its canonical form
is `series (fun k => Real.cos (k * u)) L + series (fun k => Real.sin (k * u)) []`, where `L` is
the `Packed.add` of `smul (1/2) [1]`, `[0, 1]` and `smul (1/2) [0, 0, 1]`. The kernel evaluates
`L` to `[1/2, 1, 1/2]` while it links the coefficients to their packed row, so the tactic never
has to normalize the list itself.

## Main definitions

* `Basis`: cosines, sines, powers or Chebyshev polynomials.
* `Domain`: the circle `∀ u : ℝ`, an interval `∀ x ∈ Set.Icc lo hi` or the unit circle of `ℂ`,
  with the bound variable.
* `basisFun dom b point`: the basis as a function `ℕ → ℝ` or `ℕ → ℂ` of the domain's variable.
* `Form`: a polynomial side read off a goal, with its lists, its canonical value and the proof.
* `read? dom e`: the reader itself, `none` when `e` is not a linear form in atoms of the domain.
* `proveBy` and `ratOf`: small tactic steps, shared with the coefficient route in
  `FloatLib.Numerics.Automation.Interval.Coeff`.

## Implementation notes

The equation `e = F` is proved in two steps. First every atom is replaced by its series by
congruence, so the proof never rewrites inside the goal. That matters when an atom is the bare
variable `x`: rewriting `x` to `series (fun k => x ^ k) [0, 1]` would also rewrite the `x` inside
that series. Then `simp only [Coeff.series_*]`, `push_cast` and `ring` close the equation between
the substituted term and the canonical form, which is linear in the lists.

A block whose coefficient is `(xs.getD k 0 : ℝ)` for a closed list `xs` uses `xs` itself, so the
kernel links the goal's own list, with nothing recomputed. Any other coefficient is read as
`(List.range n).map` of its rational value, and its length enters the kernel check as a side
condition.
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Coeff

open FloatLib.Numerics FloatLib.Numerics.Packed

/-! ### Small tactic steps -/

/-- A proof of `ty` by the tactic `tac`, without error recovery, or the error `msg`. The reader and
the goal code use it for small side facts, such as an equation that `norm_num` closes, so that a
failure becomes one plain message instead of a stuck goal. -/
def proveBy (ty : Expr) (tac : TSyntax `tactic) (msg : MessageData) : TacticM Expr := do
  let m ← mkFreshExprMVar ty
  let ok ← try pure (← Lean.Elab.Tactic.run m.mvarId! (withoutRecover (evalTactic tac))).isEmpty
    catch _ => pure false
  unless ok do throwError msg
  instantiateMVars m

/-- A real or complex constant as a rational, with a proof that the term equals its cast. This is
how a bound such as `-1/4` or `2.9798074e12` in a goal becomes the rational of a check. -/
def ratOf (e : Expr) : TacticM (ℚ × Expr) := do
  let ty ← inferType e
  let r ← Mathlib.Meta.NormNum.derive (u := Level.zero) (α := ty) e
  let some q := r.toRat | throwError "interval: {e} is not a rational number"
  let eq ← mkEq e (← mkAppOptM ``Rat.cast #[ty, none, toExpr q])
  return (q, ← proveBy eq (← `(tactic| norm_num)) m!"interval: could not prove {eq}")

/-! ### Atoms and linear forms -/

/-- The bases a series can use. The main part of a goal is in cosines, powers or Chebyshev
polynomials, and a second part in sines on the circle. -/
inductive Basis where
  /-- `Real.cos (k * u)` -/
  | cos
  /-- `Real.sin (k * u)` -/
  | sin
  /-- `x ^ k` -/
  | pow
  /-- `(Polynomial.Chebyshev.T ℝ k).eval y` -/
  | cheb
  deriving BEq

/-- One atom of a goal: a block `∑ k ∈ Finset.range n, …` or a monomial, as a list of rationals
against a basis, with a proof that the atom is `series f list`. -/
private structure Atom where
  /-- The subterm of the goal. -/
  term : Expr
  /-- The basis. -/
  basis : Basis
  /-- The coefficients, a closed `List ℚ` term. -/
  list : Expr
  /-- A proof of `term = series f list`. -/
  proof : Expr

/-- The domain of a goal, with its bound variable as a free variable of the local context. -/
inductive Domain where
  /-- `∀ u : ℝ`: trigonometric polynomials. -/
  | circle (u : Expr)
  /-- `∀ x ∈ Set.Icc lo hi`: power series and Chebyshev series. -/
  | interval (x : Expr)
  /-- `∀ z : ℂ, ‖z‖ = 1`: polynomials in `z`. -/
  | sphere (z : Expr)

/-- The variable of a domain. -/
def Domain.var : Domain → Expr
  | .circle u | .interval u | .sphere u => u

/-- Whether the values live in `ℂ`. -/
def Domain.complex : Domain → Bool
  | .sphere _ => true
  | _ => false

/-- The state of the reader: the atoms so far and the point of a Chebyshev series. -/
private structure ReadState where
  /-- The atoms. -/
  atoms : Array Atom := #[]
  /-- The point `y` of the Chebyshev polynomials, once one is seen. -/
  point : Option Expr := none
  /-- Closed side conditions for the kernel check, such as the length of a coefficient list. -/
  closed : Array Expr := #[]

/-- The reader's monad. -/
private abbrev ReadM := StateRefT ReadState TacticM

/-- The basis function of `b` as a lambda in the domain's variable: `fun k => Real.cos (k * u)`. -/
def basisFun (dom : Domain) (b : Basis) (point : Option Expr) : MetaM Expr := do
  let v := dom.var
  match b, dom.complex with
  | .cos, _ => do let u : Q(ℝ) := v; pure q(fun k : ℕ => Real.cos (k * $u))
  | .sin, _ => do let u : Q(ℝ) := v; pure q(fun k : ℕ => Real.sin (k * $u))
  | .pow, false => do let x : Q(ℝ) := v; pure q(fun k : ℕ => $x ^ k)
  | .pow, true => do let z : Q(ℂ) := v; pure q(fun k : ℕ => $z ^ k)
  | .cheb, _ => do
      let some y := point | throwError "interval: a Chebyshev series without a point"
      let y : Q(ℝ) := y
      pure q(fun k : ℕ => (Polynomial.Chebyshev.T ℝ k).eval $y)

/-- The value of a natural-number numeral, if `e` is one: a numeral of `ℕ`, or of `ℤ` or `ℝ` with a
natural value, such as the `2` of `Real.cos (2 * u)`. -/
private def natNumeral? (e : Expr) : TacticM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  if ← isDefEq (← inferType e) q(ℕ) then return (← (evalNat e).run)
  try
    let r ← Mathlib.Meta.NormNum.derive (u := Level.zero) (α := ← inferType e) e
    let some q := r.toRat | return none
    if q.den = 1 && 0 ≤ q.num then return some q.num.toNat else return none
  catch _ => return none

/-- If `e` is a basis term of index `k` (the summation variable), its basis. -/
private def basisAt? (dom : Domain) (e k : Expr) : ReadM (Option Basis) := do
  let isK (a : Expr) : Bool := match a.getAppFnArgs with
    | (``Nat.cast, #[_, _, k']) => k' == k
    | _ => false
  match dom, e.getAppFnArgs with
  | .circle u, (``Real.cos, #[arg]) | .circle u, (``Real.sin, #[arg]) =>
      let_expr HMul.hMul _ _ _ _ kc u' := arg | return none
      unless isK kc && u' == u do return none
      return some (if e.isAppOf ``Real.cos then .cos else .sin)
  | .interval x, (``HPow.hPow, #[_, _, _, _, x', k']) =>
      return if x' == x && k' == k then some .pow else none
  | .sphere z, (``HPow.hPow, #[_, _, _, _, z', k']) =>
      return if z' == z && k' == k then some .pow else none
  | .interval _, (``Polynomial.eval, #[_, _, y, p]) =>
      let_expr Polynomial.Chebyshev.T _ _ kz := p | return none
      unless isK kz && !y.containsFVar k.fvarId! do return none
      match (← get).point with
      | some y' => unless ← isDefEq y y' do
          throwError "interval: the Chebyshev polynomials are taken at {y'} and at {y}"
      | none => modify fun s => { s with point := some y }
      return some .cheb
  | _, _ => return none

/-- If `e` is a monomial, such as `Real.cos (2 * u)`, `x ^ 3`, `x` or `(T ℝ 2).eval y`, its basis
and its index. -/
private def monomial? (dom : Domain) (e : Expr) : ReadM (Option (Basis × Nat)) := do
  let v := dom.var
  match dom, e.getAppFnArgs with
  | .circle u, (``Real.cos, #[arg]) | .circle u, (``Real.sin, #[arg]) =>
      let b := if e.isAppOf ``Real.cos then Basis.cos else .sin
      if arg == u then return some (b, 1)
      let_expr HMul.hMul _ _ _ _ l r := arg | return none
      let c? ← if r == u then natNumeral? l else if l == u then natNumeral? r else pure none
      return c?.map (b, ·)
  | .interval _, (``Polynomial.eval, #[_, _, y, p]) =>
      let_expr Polynomial.Chebyshev.T _ _ m := p | return none
      let some m ← natNumeral? m | return none
      match (← get).point with
      | some y' => unless ← isDefEq y y' do
          throwError "interval: the Chebyshev polynomials are taken at {y'} and at {y}"
      | none => modify fun s => { s with point := some y }
      return some (.cheb, m)
  | _, (``HPow.hPow, #[_, _, _, _, b, m]) =>
      if b != v then return none
      return (← natNumeral? m).map (.pow, ·)
  | _, _ => return if e == v && !(dom matches .circle _) then some (.pow, 1) else none

/-- The coefficient list of a block whose term at `k` is `c` times a basis function: `xs` itself
for `c = (xs.getD k 0 : ℝ)`, and `(List.range n).map` of the coefficient as a rational otherwise.
Returns the list and whether the term matches `(xs.getD k 0) * f k` by `rfl`. -/
private def blockList (dom : Domain) (n : Nat) (k c : Expr) : TacticM (Expr × Bool) := do
  let ratTy := mkConst ``Rat
  let mapped (r : Expr) : MetaM Expr := do
    mkAppM ``List.map #[← mkLambdaFVars #[k] r, ← mkAppM ``List.range #[mkNatLit n]]
  match c.getAppFnArgs with
  | (``Rat.cast, #[_, _, q]) =>
      if let (``List.getD, #[_, xs, k', dflt]) := q.getAppFnArgs then
        if k' == k && !xs.containsFVar k.fvarId! && (← isDefEq dflt (toExpr (0 : ℚ))) then
          let len := (← Packed.listValues xs).size
          if len ≤ n then return (xs, true)
          return (← mkAppM ``List.take #[mkNatLit n, xs], false)
      return (← mapped q, false)
  | (``Int.cast, #[_, _, z]) => return (← mapped (← mkAppOptM ``Int.cast #[ratTy, none, z]), false)
  | (``Nat.cast, #[_, _, m]) => return (← mapped (← mkAppOptM ``Nat.cast #[ratTy, none, m]), false)
  | _ =>
      if c.containsFVar k.fvarId! || c.containsFVar dom.var.fvarId! then
        throwError "interval: the coefficient {c} is not a rational, an integer or a natural \
          number cast to {if dom.complex then "ℂ" else "ℝ"}"
      let (q, _) ← ratOf c
      return (← mkAppM ``List.replicate #[mkNatLit n, toExpr q], false)

/-- The index of the atom `e`, reading it as a block or a monomial, or `none`. -/
private def atom? (dom : Domain) (e : Expr) : ReadM (Option Nat) := do
  if let some i := (← get).atoms.findIdx? (·.term == e) then return some i
  let carrier : Expr := if dom.complex then q(ℂ) else q(ℝ)
  let some (basis, list, proof) ← (do
      if let some (b, m) ← monomial? dom e then
        let list ← mkAppM ``HAppend.hAppend
          #[← mkAppM ``List.replicate #[mkNatLit m, toExpr (0 : ℚ)],
            ← mkListLit (mkConst ``Rat) [toExpr (1 : ℚ)]]
        let f ← basisFun dom b (← get).point
        let eq ← mkEq e (← mkAppOptM ``Coeff.series #[carrier, none, f, list])
        let pf ← proveBy eq (← `(tactic| (rw [Coeff.series_single]; (try push_cast); try ring_nf)))
          m!"interval: could not read {e} as a monomial"
        return some (b, list, pf)
      let_expr Finset.sum ι _ _ s body := e | return none
      unless ← isDefEq ι (mkConst ``Nat) do return none
      let_expr Finset.range nE := s | return none
      let some n ← (evalNat nE).run | return none
      let found ← lambdaTelescope body fun ks t => do
        let #[k] := ks | return none
        let pieces : Array (Expr × Expr) ← match t.getAppFnArgs with
          | (``HMul.hMul, #[_, _, _, _, l, r]) => pure #[(l, r), (r, l)]
          | _ => pure #[(← mkNumeral carrier 1, t)]
        for (c, f) in pieces do
          if let some b ← basisAt? dom f k then
            let (list, direct) ← blockList dom n k c
            return some (b, list, direct)
        return none
      let some (b, list, direct) := found | return none
      let f ← basisFun dom b (← get).point
      let hl ← mkFreshExprMVar (← mkAppM ``LE.le #[← mkAppM ``List.length #[list], mkNatLit n])
      modify fun s => { s with closed := s.closed.push hl }
      let hty ← withLocalDeclD `k (mkConst ``Nat) fun k => do
        let lt ← mkAppM ``LT.lt #[k, mkNatLit n]
        let lhs := body.beta #[k]
        let coeff ← mkAppOptM ``Rat.cast #[carrier, none,
          ← mkAppM ``List.getD #[list, k, toExpr (0 : ℚ)]]
        let rhs ← mkAppM ``HMul.hMul #[coeff, f.beta #[k]]
        mkForallFVars #[k] (← mkArrow lt (← mkEq lhs rhs))
      let tac ← if direct then `(tactic| exact fun _ _ => rfl) else
        `(tactic| (intro k hk; simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hk, List.getElem?_take, hk, ite_true, List.getElem?_replicate,
          Option.map_some, Option.getD_some]; (try push_cast); try ring_nf))
      let h ← proveBy hty tac m!"interval: could not match the coefficients of {e} with {list}"
      let pf ← mkAppOptM ``Coeff.sum_eq_series #[carrier, none, f, mkNatLit n, list, none, hl, h]
      return some (b, list, pf)) | return none
  modify fun s => { s with atoms := s.atoms.push ⟨e, basis, list, proof⟩ }
  return some ((← get).atoms.size - 1)

/-- A Gaussian rational `a + b i`; real goals have `b = 0`. -/
private abbrev G := ℚ × ℚ

/-- A constant without the variable, as a Gaussian rational written linearly in `I`. -/
private partial def constant? (dom : Domain) (e : Expr) : TacticM (Option G) := do
  if e.containsFVar dom.var.fvarId! then return none
  unless dom.complex do
    try return some ((← ratOf e).1, 0) catch _ => return none
  if e.isConstOf ``Complex.I then return some (0, 1)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      let some (a, a') ← constant? dom a | return none
      let some (b, b') ← constant? dom b | return none
      return some (a + b, a' + b')
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      let some (a, a') ← constant? dom a | return none
      let some (b, b') ← constant? dom b | return none
      return some (a - b, a' - b')
  | (``Neg.neg, #[_, _, a]) =>
      let some (a, a') ← constant? dom a | return none
      return some (-a, -a')
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      let some (a, a') ← constant? dom a | return none
      let some (b, b') ← constant? dom b | return none
      if a' ≠ 0 && b' ≠ 0 then return none
      return some (a * b - a' * b', a * b' + a' * b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
      let some (a, a') ← constant? dom a | return none
      let some (b, b') ← constant? dom b | return none
      if b' ≠ 0 || b = 0 then return none
      return some (a / b, a' / b)
  | _ => try return some ((← ratOf e).1, 0) catch _ => return none

/-- A linear form read off a term `e`: `∑ cᵢ atomᵢ + c₀`, the term `e'` with every atom replaced
by its series, and a proof of `e = e'` by congruence. -/
private structure Lin where
  /-- The scaled atoms. -/
  terms : Array (G × Nat)
  /-- The constant term. -/
  const : G
  /-- The term with every atom replaced by its series. -/
  sub : Expr
  /-- A proof of `e = sub`. -/
  proof : Expr

/-- `e` as a linear form with Gaussian rational coefficients, or `none` if it is not a linear
combination of basis terms. -/
private partial def linear (dom : Domain) (e : Expr) : ReadM (Option Lin) := do
  if let some c ← constant? dom e then return some ⟨#[], c, e, ← mkEqRefl e⟩
  let mul (x y : G) : G := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)
  let scale (c : G) (r : Array (G × Nat)) : Array (G × Nat) := r.map fun (a, i) => (mul c a, i)
  let addG (x y : G) : G := (x.1 + y.1, x.2 + y.2)
  -- the same head on the substituted arguments, by congruence
  let binary (f : Expr) (r s : Lin) (terms : Array (G × Nat)) (const : G) : MetaM Lin := do
    return ⟨terms, const, mkApp2 f r.sub s.sub, ← mkCongr (← mkCongrArg f r.proof) s.proof⟩
  let atom (e : Expr) : ReadM (Option Lin) := do
    let some i ← atom? dom e | return none
    let some a := (← get).atoms[i]? | return none
    let f ← basisFun dom a.basis (← get).point
    let carrier : Expr := if dom.complex then q(ℂ) else q(ℝ)
    return some ⟨#[((1, 0), i)], (0, 0), ← mkAppOptM ``Coeff.series #[carrier, none, f, a.list],
      a.proof⟩
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[α, β, γ, inst, a, b]) =>
      let some r ← linear dom a | return none
      let some s ← linear dom b | return none
      binary (mkAppN (mkConst ``HAdd.hAdd e.getAppFn.constLevels!) #[α, β, γ, inst]) r s
        (r.terms ++ s.terms) (addG r.const s.const)
  | (``HSub.hSub, #[α, β, γ, inst, a, b]) =>
      let some r ← linear dom a | return none
      let some s ← linear dom b | return none
      binary (mkAppN (mkConst ``HSub.hSub e.getAppFn.constLevels!) #[α, β, γ, inst]) r s
        (r.terms ++ scale (-1, 0) s.terms) (addG r.const (mul (-1, 0) s.const))
  | (``Neg.neg, #[α, inst, a]) =>
      let some r ← linear dom a | return none
      let f := mkAppN (mkConst ``Neg.neg e.getAppFn.constLevels!) #[α, inst]
      return some ⟨scale (-1, 0) r.terms, mul (-1, 0) r.const, mkApp f r.sub,
        ← mkCongrArg f r.proof⟩
  | (``HMul.hMul, #[α, β, γ, inst, a, b]) =>
      let f := mkAppN (mkConst ``HMul.hMul e.getAppFn.constLevels!) #[α, β, γ, inst]
      if let some c ← constant? dom a then
        let some s ← linear dom b | return none
        return some (← binary f ⟨#[], c, a, ← mkEqRefl a⟩ s (scale c s.terms) (mul c s.const))
      if let some c ← constant? dom b then
        let some r ← linear dom a | return none
        return some (← binary f r ⟨#[], c, b, ← mkEqRefl b⟩ (scale c r.terms) (mul c r.const))
      atom e
  | (``HDiv.hDiv, #[α, β, γ, inst, a, b]) =>
      let some (c, c') ← constant? dom b | return none
      if c' ≠ 0 || c = 0 then return none
      let some r ← linear dom a | return none
      let f := mkAppN (mkConst ``HDiv.hDiv e.getAppFn.constLevels!) #[α, β, γ, inst]
      return some (← binary f r ⟨#[], (c, 0), b, ← mkEqRefl b⟩ (scale (1 / c, 0) r.terms)
        (mul (1 / c, 0) r.const))
  | _ => atom e

/-- A polynomial side read off a goal: the coefficient lists of each part, the canonical value `F`
in `Coeff.series` form and a proof of `e = F`. -/
structure Form where
  /-- The basis of the main part: cosines, powers or Chebyshev polynomials. -/
  basis : Basis
  /-- The coefficients of the main part. -/
  main : Expr
  /-- The coefficients of the second part: sines, or the imaginary part. -/
  second : Expr
  /-- The Chebyshev point. -/
  point : Option Expr
  /-- The canonical value. -/
  value : Expr
  /-- A proof of `e = value`. -/
  proof : Expr
  /-- Closed side conditions of the reading, for the kernel check. -/
  closed : Array Expr

/-- `∑ cᵢ xsᵢ` as one list: `add` of the scaled lists, or `[]`. -/
private def combine (parts : Array (ℚ × Expr)) : MetaM Expr := do
  let mut acc : Option Expr := none
  for (c, xs) in parts do
    if c = 0 then continue
    let term ← if c = 1 then pure xs else mkAppM ``Packed.smul #[toExpr c, xs]
    acc ← match acc with
      | none => pure (some term)
      | some a => some <$> mkAppM ``Packed.add #[a, term]
  return acc.getD (mkApp (mkConst ``List.nil [0]) (mkConst ``Rat))

/-- Read `e` as series on the domain: a trigonometric polynomial, a power or Chebyshev series, or
a polynomial in `z`. -/
def read? (dom : Domain) (e : Expr) : TacticM (Option Form) := do
  let (some lin, st) ← (linear dom e).run {} | return none
  let terms := lin.terms
  let c₀ := lin.const
  if st.atoms.isEmpty then return none
  let carrier : Expr := if dom.complex then q(ℂ) else q(ℝ)
  let atoms := st.atoms
  let mainBasis : Basis := match dom with
    | .circle _ => .cos
    | .sphere _ => .pow
    | .interval _ => if atoms.any (·.basis == .cheb) then .cheb else .pow
  if atoms.any (fun a => a.basis != mainBasis && a.basis != .sin) ||
      (atoms.any (·.basis == .sin) && !(dom matches .circle _)) then
    throwError "interval: {e} mixes the power basis and Chebyshev polynomials"
  let one ← mkAppM ``HAppend.hAppend #[← mkAppM ``List.replicate #[mkNatLit 0, toExpr (0 : ℚ)],
    ← mkListLit (mkConst ``Rat) [toExpr (1 : ℚ)]]
  let mut main : Array (ℚ × Expr) := #[(c₀.1, one)]
  let mut second : Array (ℚ × Expr) := #[]
  if dom.complex then second := second.push (c₀.2, one)
  for ((a, b), i) in terms do
    let some atom := atoms[i]? | throwError "interval: lost the atom {i} of {e}"
    if atom.basis == .sin then
      second := second.push (a, atom.list)
    else
      main := main.push (a, atom.list)
      if dom.complex then second := second.push (b, atom.list)
  let mainList ← combine main
  -- a series needs one coefficient, so the zero polynomial is the row `[0]`
  let zero ← mkAppM ``HAppend.hAppend #[← mkAppM ``List.replicate #[mkNatLit 0, toExpr (0 : ℚ)],
    ← mkListLit (mkConst ``Rat) [toExpr (0 : ℚ)]]
  let mainList ← if (← Packed.kernelWhnf mainList).isAppOf ``List.nil then
    mkAppM ``Packed.add #[mainList, zero]
    else pure mainList
  let secondList ← combine second
  let fMain ← basisFun dom mainBasis st.point
  let sMain ← mkAppOptM ``Coeff.series #[carrier, none, fMain, mainList]
  let value ← match dom with
    | .circle _ => do
        let fSin ← basisFun dom .sin none
        mkAppM ``HAdd.hAdd #[sMain, ← mkAppOptM ``Coeff.series #[carrier, none, fSin, secondList]]
    | .sphere _ => do
        let sIm ← mkAppOptM ``Coeff.series #[carrier, none, fMain, secondList]
        mkAppM ``HAdd.hAdd #[sMain, ← mkAppM ``HMul.hMul #[q(Complex.I), sIm]]
    | .interval _ => pure sMain
  -- `e = e'` by congruence, then `e' = value`: the canonical lists expanded, then `ring`
  let goal ← mkFreshExprMVar (← mkEq lin.sub value)
  let rest ← Lean.Elab.Tactic.run goal.mvarId! (withoutRecover (evalTactic (← `(tactic|
    (simp only [Coeff.series_add, Coeff.series_smul, Coeff.series_single, Coeff.series_nil,
        Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, Real.cos_zero, pow_zero, pow_one,
        Polynomial.Chebyshev.T_zero, Polynomial.eval_one]
     try push_cast
     try ring)))))
  unless rest.isEmpty do
    throwError "interval: could not write {e} in the canonical form {value}"
  let proof ← mkEqTrans lin.proof (← instantiateMVars goal)
  return some ⟨mainBasis, mainList, secondList, st.point, value, proof, st.closed⟩

end FloatLib.Numerics.Interval.Tactic.Coeff
