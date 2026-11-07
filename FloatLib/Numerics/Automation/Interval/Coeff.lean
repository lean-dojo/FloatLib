/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Coeff.Bound
public meta import FloatLib.Numerics.Automation.Interval.Series
public meta import FloatLib.Numerics.Packed.Horner
public meta import FloatLib.Numerics.Packed.Literal
public meta import FloatLib.Numerics.Packed.Sos
public meta import FloatLib.Numerics.Packed.Window
public meta import Mathlib.Tactic.Linarith
public meta import Mathlib.Tactic.NormNum.Core
public meta import Mathlib.Tactic.Ring

/-!
# The coefficient route of `interval`

Some bounds are about a whole domain at once, and splitting the domain into boxes is hopeless for
them: a 200-term cosine polynomial within `4e-7` of its maximum on all of `[0, 2π]`, or a
denominator whose margin is `1e-10`. `interval` proves these goals from the coefficients, before it
tries any box:

* `∀ u : ℝ, lo ≤ S u`, `S u ≤ hi` or `|S u| ≤ c`, strict versions too, for a real trigonometric
  polynomial `S` with cosine and sine terms;
* `∀ x ∈ Set.Icc lo hi, …` for a polynomial `∑ aₖ xᵏ` in the power basis on any interval, or a
  Chebyshev series `∑ aₖ Tₖ(y)` at a point `y` that `linarith` places in `[-1, 1]`;
* `∀ z : ℂ, ‖z‖ = 1 → ‖p z‖ ≤ c` or `c ≤ ‖p z‖` for a polynomial `p` with Gaussian rational
  coefficients.

The polynomial side may be any sum and rational multiple of blocks
`∑ k ∈ Finset.range n, a k * f k`, monomials such as `Real.cos (2 * u)`, `x ^ 3` or `z`, and
constants, and either side of `≤` may be a polynomial: `P u ≤ Q u` is `0 ≤ Q u - P u`. A
coefficient `a k` is a rational, an integer or a natural number cast to `ℝ` or `ℂ`, such as an
entry `(xs.getD k 0 : ℝ)` of a list, an entry of a packed row or the decoded value of a binary64
number.

```lean
example : ∀ u : ℝ, |∑ k ∈ Finset.range 3, (([0, 2, -1] : List ℚ).getD k 0 : ℝ) *
    Real.sin (k * u)| ≤ 3 := by
  interval
example : ∀ u : ℝ, -1/4 ≤ 1/2 + Real.cos u + Real.cos (2 * u) / 2 := by
  interval (lower := [1, 1, 1])
```

## Main definitions

* `Certs`: the options `(lower := h)` and `(upper := h)`, one certificate for each side.
* `run goal certs verify`: the route on a goal that starts with `∀ u : ℝ`, `∀ x ∈ Set.Icc lo hi`
  or `∀ z : ℂ, ‖z‖ = 1`. It closes the goal or says `Outcome.notMine`, and `interval` then goes on
  to the boxes.
* `runFree goal certs verify`: the same for a trigonometric polynomial in a free variable `u`,
  which `interval` tries when the boxes find no bounds for `u`.

## Main statements

The route proves nothing itself. It applies `Coeff.trig_sos`, `Coeff.norm_sos` or
`Coeff.power_sos`, one of the bound lemmas such as `Coeff.bound_le_of_sos`, and for a Chebyshev
series `Coeff.forall_Icc_chebyshev`, all from `FloatLib.Numerics.Coeff.Bound`.

## Implementation notes

The goal is first read as `series f xs` for each basis it uses, by
`FloatLib.Numerics.Automation.Interval.Series`, and the coefficients are packed as integers at one
common denominator. Without a certificate every side of the goal gets the bound that the
coefficients alone give, the constant term plus or minus the sum of the absolute values of the
others: no certificate, no search, and fully automatic. A sharp bound takes a sum-of-squares
certificate `(lower := h)` or `(upper := h)`, a factor `h` of integers given as a list or a file
next to the source, or a pair `(p, q)` for a factor `p + i q` with complex coefficients.
`scripts/coeff_cert.py` finds them.

Then Lean's kernel checks one closed proposition with `decide`: the link between the coefficients
and their rows, the range checks and one sum-of-squares check per side. Nothing computed outside
the kernel is trusted. The certificate check also runs in the tactic first, on plain integer
arrays, so a wrong certificate fails with a message that says by how much, and the tactic picks
the power of two that scales the factor against the target there, trying the five nearest.

The lane width is the smallest that the headroom conditions allow, computed from the bit sizes of
the target, the factor and the scales, so every product and every defect fits its lanes. A strict
bound lowers the constant `kc` by one, the smallest step an integer check can see.

The coefficient route follows the same proof construction as the box evaluator: reify the goal,
verify a closed Boolean check in the kernel, and apply its soundness theorem. Here the check uses
packed integer operations instead of evaluating subdivisions of the domain.

## References

* Bogdan Dumitrescu, *Positive Trigonometric Polynomials and Signal Processing Applications*,
  Springer (2007), <https://doi.org/10.1007/978-1-4020-5125-8>, for sum-of-squares certificates of
  trigonometric polynomials.
* Siegfried M. Rump, *Verification methods: rigorous results using floating-point arithmetic*,
  Acta Numerica 19 (2010), 287–449, <https://doi.org/10.1017/S096249291000005X>.

## Tags

interval, tactic, coefficient bound, sum of squares, kernel check
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Coeff

open FloatLib.Numerics FloatLib.Numerics.Packed

/-! ### Options -/

/-- The certificates of `interval (lower := h)` and `interval (upper := h)`. -/
structure Certs where
  /-- The certificate for the lower side of the goal. -/
  lower : Option Term := none
  /-- The certificate for the upper side of the goal. -/
  upper : Option Term := none

/-- Whether no certificate was given. -/
def Certs.isEmpty (c : Certs) : Bool := c.lower.isNone && c.upper.isNone

/-! ### Small helpers -/

/-- The number of bits `g` with `-2 ^ g ≤ x < 2 ^ g` for every `x`. -/
private def guardBits (xs : Array Int) : Nat :=
  xs.foldl (fun g x => max g (Nat.log2 x.natAbs + 1)) 0

/-- The entries of a row given as a string, a file of integers next to the source file, or as a
`List ℤ` term. -/
private def rowEntries (stx : Term) : TacticM (Array Int) := do
  match stx.raw.isStrLit? with
  | some path =>
      match ← Packed.readEntries path with
      | .ok xs => pure xs
      | .error err => throwErrorAt stx "interval: {err}"
  | none =>
      let e ← elabTermEnsuringType stx (mkApp (mkConst ``List [0]) (mkConst ``Int))
      (← Packed.listValues (← instantiateMVars e)).mapM fun x => Packed.intValue x

/-- A factor `p + i q`: one row for a real factor, a pair of rows `(p, q)` otherwise. -/
private def factorOf (stx : Term) : TacticM (Array Int × Array Int) := do
  match stx with
  | `(($p, $q)) => return (← rowEntries p, ← rowEntries q)
  | _ => return (← rowEntries stx, #[])

/-- The packed row of integer entries in lanes of width `w`, as a raw literal. -/
private def rowLiteral (w : Nat) (xs : Array Int) : MetaM Expr := do
  match Packed.rowLanes w true xs with
  | .ok lanes => return mkRawNatLit (Packed.packSlice w lanes 0 lanes.size)
  | .error e => throwError "interval: {e}"

/-- Apply the theorem `thm` to `args`, with a fresh metavariable for every `none`. Returns the
application and the metavariables, whose types are the hypotheses still to prove. -/
private def applyWithHoles (thm : Name) (args : Array (Option Expr)) :
    MetaM (Expr × Array Expr) := do
  let c ← mkConstWithFreshMVarLevels thm
  let mut ty ← inferType c
  let mut e := c
  let mut holes := #[]
  for a in args do
    let .forallE _ dom body _ := ty | throwError "interval: too many arguments for {thm}"
    let v ← match a with
      | some v => pure v
      | none => do
          let m ← mkFreshExprMVar dom
          holes := holes.push m
          pure m
    e := mkApp e v
    ty := body.instantiate1 v
  return (e, holes)

/-- Split a proof of `p₁ ∧ … ∧ pₖ` into its `k` parts. -/
private def splitAnd (h : Expr) : Nat → MetaM (Array Expr)
  | 0 => return #[]
  | 1 => return #[h]
  | k + 1 => do
      let rest ← splitAnd (← mkAppM ``And.right #[h]) k
      return #[← mkAppM ``And.left #[h]] ++ rest

/-- Rewrite the goal `P a` to `P b` along `eq : a = b`: from a proof of `P b`, a proof of `P a`. -/
private def transport (goal : Expr) (a : Expr) (eq : Expr) (proof : Expr) : MetaM Expr := do
  let motive ← kabstract goal a
  unless motive.hasLooseBVars do throwError "interval: could not find {a} in the goal"
  let P := Expr.lam `t (← inferType a) motive .default
  mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[P, eq], proof]

/-! ### Sum-of-squares data -/

/-- The integers of one check: `kT (T - i S) + kc - kH |p + i q|²`. -/
private structure Sos where
  /-- The multiplier of the target. -/
  kT : Int
  /-- The constant. -/
  kc : Int
  /-- The multiplier of the square. -/
  kH : Nat
  /-- The real part of the factor. -/
  p : Array Int
  /-- The imaginary part of the factor. -/
  q : Array Int

/-- A row padded with zeros to `len` entries. -/
private def padTo (len : Nat) (xs : List Int) : Array Int :=
  xs.toArray ++ Array.replicate (len - xs.length) 0

/-- The full rows of `|p + i q|²`, `2 n - 1` entries centred at `n - 1`. -/
private def squareRows (n : Nat) (p q : Array Int) : Array Int × Array Int :=
  let r := Packed.normSq n p.toList q.toList
  (padTo (2 * n - 1) r.1, padTo (2 * n - 1) r.2)

/-- The centre of the real row of `kT (T - i S) + kc - kH (H - i K)` and the sum of the absolute
values of all its other entries, real and imaginary. -/
private def defect (n : Nat) (T S Hr Hi : Array Int) (kT kc : Int) (kH : Nat) : Int × Nat :=
  let c := n - 1
  let er := (Array.range (2 * n - 1)).map fun i =>
    kT * T[i]! + (if i = c then kc else 0) - (kH : Int) * Hr[i]!
  let ei := (Array.range (2 * n - 1)).map fun i => kT * S[i]! - (kH : Int) * Hi[i]!
  let rest := (er.toList.eraseIdx c).foldl (fun a x => a + x.natAbs) 0 +
    ei.foldl (fun a x => a + x.natAbs) 0
  (er[c]!, rest)

/-- Find the power of two that the factor `(p, q)` certifies for `kT₀ (T - i S) + kc₀`, and check
the certificate in compiled code. A strict side lowers `kc` by one. -/
private def findSos (n : Nat) (T S : Array Int) (kT₀ kc₀ : Int) (p q : Array Int) (strict : Bool) :
    Except String Sos := do
  if p.size > n || q.size > n then
    throw s!"the factor has more entries than the {n} of half the target"
  let c₀ := kT₀ * T[n - 1]! + kc₀
  if c₀ < 0 || (c₀ = 0 && strict) then
    throw "the bound is on the wrong side of the mean of the polynomial, so it is false"
  let (Hr, Hi) := squareRows n p q
  let lower : Int := if strict then 1 else 0
  if p.all (· = 0) && q.all (· = 0) then
    let (centre, rest) := defect n T S Hr Hi kT₀ (kc₀ - lower) 1
    if (rest : Int) ≤ centre then return ⟨kT₀, kc₀ - lower, 1, #[], #[]⟩
    throw ""
  if c₀ = 0 then
    throw "a nonzero square cannot certify a target with zero mean"
  let acc := Hr[n - 1]!
  if acc ≤ 0 then throw "the factor is zero"
  let s₀ : Int := (Nat.log2 acc.toNat : Int) - (Nat.log2 c₀.toNat : Int)
  let mut best : Option (Int × Nat) := none
  let mut tight := false
  for ds in [0, -1, 1, 2, -2] do
    let s := s₀ + ds
    let (kT, kc, kH) := if 0 ≤ s then (kT₀ * 2 ^ s.toNat, kc₀ * 2 ^ s.toNat, 1)
      else (kT₀, kc₀, 2 ^ (-s).toNat)
    let (centre, rest) := defect n T S Hr Hi kT (kc - lower) kH
    if (rest : Int) ≤ centre then return ⟨kT, kc - lower, kH, p, q⟩
    if strict then
      let (centre, rest) := defect n T S Hr Hi kT kc kH
      if (rest : Int) ≤ centre then tight := true
    if best.isNone then best := some (centre, rest)
  if tight then
    throw "the certificate proves the bound with equality somewhere, so not the strict bound"
  let (centre, rest) := best.getD (0, 0)
  throw s!"the certificate fails: the centre entry {centre} of the defect is below the sum \
    {rest} of the absolute values of the others"

/-! ### The three families -/

/-- What a family contributes to the checks: the target, the scale `K` of
`0 ≤ kT (K F) + kc`, the headroom it needs, and how to apply its theorem for one side. -/
private structure Family where
  /-- Half the length of the target. -/
  n : Nat
  /-- The real row of the target, `2 n - 1` entries. -/
  T : Array Int
  /-- The imaginary row of the target. -/
  S : Array Int
  /-- The scale `K`. -/
  scale : Nat
  /-- The range bound of the coefficient rows. -/
  g : Nat
  /-- A number the family needs below `2 ^ (w - 1)`. -/
  need : Nat
  /-- What the bounds are about, for messages. -/
  what : String
  /-- The theorem for lane width `w`, target bits `gt`, factor bits `gh`, factor lengths,
  `kH`, factor rows and `kT`, `kc`: the proof of `0 ≤ kT (K F) + kc` and the holes, those the
  sides share and the side's own. -/
  prove : Nat → Nat → Nat → Nat → Nat → Nat → Expr → Expr → Int → Int →
    MetaM (Expr × Array Expr × Array Expr)

/-- The rationals of a closed list term, read by kernel reduction. -/
private def intRow (list : Expr) : MetaM (Array ℚ) := do
  (← Packed.listValues list).mapM Packed.ratValue

/-- The two-sided row of `n` entries moved up to centre `n` of `2 n - 1` lanes. -/
private def centred (n k : Nat) (row : List Int) : Array Int :=
  padTo (2 * n - 1) (List.replicate (n - k) 0 ++ row)

/-- Trigonometric polynomials: cosine and sine rows on the circle, scale `2 d`. -/
private def trigFamily (rd : Form) (u : Expr) : MetaM Family := do
  let qa ← intRow rd.main
  let qb ← intRow rd.second
  let d := Packed.commonDen #[qa, qb]
  let A := Packed.numerators d qa
  let B := Packed.numerators d qb
  let na := A.size
  let nb := B.size
  let n := max (max na nb) 1
  let g := guardBits (A ++ B)
  let T := centred n na (Packed.mirror A.toList)
  let S := centred n nb (Packed.mirror B.toList true)
  let prove w gt gh m m' kH p q kT kc := do
    let (pf, holes) ← applyWithHoles ``Coeff.trig_sos #[mkNatLit w, mkNatLit g, mkNatLit gt,
      mkNatLit gh, mkNatLit na, mkNatLit nb, mkNatLit n, mkNatLit m, mkNatLit m', mkNatLit d,
      mkNatLit kH, ← rowLiteral w A, ← rowLiteral w B, p, q, toExpr kT, toExpr kc, rd.main,
      rd.second, none, none, none, none, none, none, u]
    return (pf, holes.extract 0 5, holes.extract 5 6)
  return { n, T, S, scale := 2 * d, g, need := 0, what := "the polynomial", prove }

/-- Polynomials in `z` on the unit circle: the rows of `|A + i B|²`, scale `d ^ 2`. -/
private def sphereFamily (rd : Form) (z hz : Expr) : MetaM Family := do
  let qa ← intRow rd.main
  let qb ← intRow rd.second
  let d := Packed.commonDen #[qa, qb]
  let A := Packed.numerators d qa
  let B := Packed.numerators d qb
  let na := A.size
  let nb := B.size
  let n := max (max na nb) 1
  let g := guardBits (A ++ B)
  let (T, S) := squareRows n A B
  let prove w gt gh m m' kH p q kT kc := do
    let (pf, holes) ← applyWithHoles ``Coeff.norm_sos #[mkNatLit w, mkNatLit g, mkNatLit gt,
      mkNatLit gh, mkNatLit na, mkNatLit nb, mkNatLit n, mkNatLit m, mkNatLit m', mkNatLit d,
      mkNatLit kH, ← rowLiteral w A, ← rowLiteral w B, p, q, toExpr kT, toExpr kc, rd.main,
      rd.second, none, none, none, none, none, none, z, hz]
    return (pf, holes.extract 0 5, holes.extract 5 6)
  let need := (na + nb) * 2 ^ g * ((na + nb) * 2 ^ g)
  return { n, T, S, scale := d ^ 2, g, need, what := "the square of the norm", prove }

/-- Power series on `[lo, hi]`: the row of Horner's rule in `x = (M + R cos u) / D`, scale
`d (2 D) ^ (n - 1)`. -/
private def powerFamily (rd : Form) (x hx : Expr) (lo hi : ℚ) : MetaM Family := do
  let qa ← intRow rd.main
  let d := Packed.commonDen #[qa]
  let A := Packed.numerators d qa
  let n := A.size
  let g := guardBits A
  let mid := (lo + hi) / 2
  let rad := (hi - lo) / 2
  let D := Nat.lcm mid.den rad.den
  let M : Int := mid.num * ((D / mid.den : Nat) : Int)
  let R : Int := rad.num * ((D / rad.den : Nat) : Int)
  let K := max (2 * D) (2 * R.natAbs + 2 * M.natAbs)
  let T := padTo (2 * n - 1) (Packed.compose [0, 2 * (D : Int)] [R, 2 * M, R] A.toList).1
  let S := Array.replicate (2 * n - 1) 0
  let prove w gt gh m m' kH p q kT kc := do
    let (pf, holes) ← applyWithHoles ``Coeff.power_sos #[mkNatLit w, mkNatLit g, mkNatLit gt,
      mkNatLit gh, mkNatLit n, mkNatLit m, mkNatLit m', mkNatLit d, mkNatLit D, mkNatLit K,
      mkNatLit kH, ← rowLiteral w A, p, q, toExpr M, toExpr R, toExpr kT, toExpr kc, rd.main,
      toExpr lo, toExpr hi, none, none, none, none, none, none, none, x, hx]
    return (pf, holes.extract 0 6, holes.extract 6 7)
  let need := n * 2 ^ g * K ^ (n - 1)
  return { n, T, S, scale := d * (2 * D) ^ (n - 1), g, need, what := "the polynomial", prove }

/-! ### Sides -/

/-- One side of a goal: `b ≤ F` (`lower`) or `F ≤ b`, possibly strict, for the value `F` of the
family theorem, with the rational bound and a proof that the bound term is its cast. -/
private structure Side where
  /-- Whether the bound is below `F`. -/
  lower : Bool
  /-- Whether the inequality is strict. -/
  strict : Bool
  /-- The bound as a real term. -/
  term : Expr
  /-- The bound as a rational. -/
  value : ℚ
  /-- A proof of `term = value`. -/
  eq : Expr
  /-- The certificate, if one was given. -/
  cert : Option Term

/-- Decimal digits for messages. -/
private def show? (q : ℚ) : String :=
  if q.den = 1 then toString q.num else toString (Float.ofInt q.num / Float.ofNat q.den)

/-- Prove every side of a goal on one family with one kernel check: find each check's integers,
pick the lane width, apply the family theorem and the bound lemma, and decide all closed
hypotheses at once. Returns one proof per side, of `b ≤ F'`, `b < F'`, `F' ≤ b` or `F' < b` for
the family's value `F'`. -/
private def proveSides (fam : Family) (sides : Array Side) (extra : Array Expr)
    (verify : Expr → TacticM Expr) : TacticM (Array Expr) := do
  let n := fam.n
  let mut data := #[]
  for side in sides do
    let σ : Int := if side.lower then 1 else -1
    let kT₀ := σ * side.value.den
    let kc₀ := -σ * fam.scale * side.value.num
    let (p, q) ← match side.cert with
      | some c => factorOf c
      | none => pure (#[], #[])
    match findSos n fam.T fam.S kT₀ kc₀ p q side.strict with
    | .ok sos => data := data.push sos
    | .error err =>
        if let some c := side.cert then throwErrorAt c "interval: {err}"
        unless err.isEmpty do throwError "interval: {err}"
        -- the coefficients alone: the centre plus or minus the other entries, over `K`
        let c := fam.T[n - 1]!
        let r : Nat := (fam.T.toList.eraseIdx (n - 1)).foldl (fun a x => a + x.natAbs) 0 +
          fam.S.foldl (fun a x => a + x.natAbs) 0
        throwError "interval: the coefficients alone give the range [{show? (mkRat (c - r)
          fam.scale)}, {show? (mkRat (c + r) fam.scale)}] for {fam.what}, which does not prove \
          the goal; a sharp bound takes a sum-of-squares certificate \
          `({if side.lower then "lower" else "upper"} := h)`, which `scripts/coeff_cert.py` finds"
  -- one lane width for every side: enough bits for the target, the factors and the products
  let gt := guardBits (fam.T ++ fam.S)
  let gh := data.foldl (fun g s => max g (guardBits (s.p ++ s.q))) 0
  let mut need := fam.need
  for s in data do
    need := max need (s.kT.natAbs * (2 * n - 1) * 2 ^ gt + s.kc.natAbs +
      s.kH * ((s.p.size + s.q.size) * 2 ^ gh) ^ 2)
  let w := max (max (fam.g + 3) (max (gt + 2) (gh + 2))) (Nat.log2 need + 2)
  let mut closed := extra
  let mut shared := #[]
  let mut proofs := #[]
  for side in sides, s in data do
    let (pf, famHoles, sideHoles) ← fam.prove w gt gh s.p.size s.q.size s.kH
      (← rowLiteral w s.p) (← rowLiteral w s.q) s.kT s.kc
    -- the link and range checks of the coefficient rows are the same for both sides, so the
    -- second side reuses the proofs of the first
    if proofs.isEmpty then closed := closed ++ famHoles else shared := shared ++ famHoles
    closed := closed ++ sideHoles
    -- `0 ≤ kT * (K * F) + kc`
    let ty ← whnfR (← instantiateMVars (← inferType pf))
    let_expr LE.le _ _ _ rhs := ty | throwError "interval: unexpected conclusion {ty}"
    let_expr HAdd.hAdd _ _ _ _ m _ := rhs | throwError "interval: unexpected conclusion {ty}"
    let_expr HMul.hMul _ _ _ _ _ kf := m | throwError "interval: unexpected conclusion {ty}"
    let_expr HMul.hMul _ _ _ _ kE F := kf | throwError "interval: unexpected conclusion {ty}"
    let_expr Nat.cast _ _ K := kE | throwError "interval: unexpected conclusion {ty}"
    let thm := match side.lower, side.strict with
      | true, false => ``Coeff.bound_le_of_sos
      | true, true => ``Coeff.bound_lt_of_sos
      | false, false => ``Coeff.le_bound_of_sos
      | false, true => ``Coeff.lt_bound_of_sos
    let (bound, holes) ← applyWithHoles thm #[F, side.term, toExpr s.kT, toExpr s.kc, K,
      toExpr side.value, pf, none, none, none, side.eq]
    closed := closed ++ holes
    proofs := proofs.push bound
  -- every closed hypothesis of every side in one conjunction, so the kernel sees each row once
  let tys ← closed.mapM fun h => do instantiateMVars (← inferType h)
  let conj ← tys.pop.foldrM (fun t acc => mkAppM ``And #[t, acc]) tys.back!
  let parts ← splitAnd (← verify conj) closed.size
  for h in closed, p in parts do h.mvarId!.assign p
  for h in shared, p in parts.extract extra.size parts.size do h.mvarId!.assign p
  proofs.mapM instantiateMVars

/-! ### Goals -/

/-- The bound `b` of a side as a rational with its proof. -/
private def sideOf (lower strict : Bool) (b : Expr) (cert : Option Term) : TacticM Side := do
  let (q, eq) ← ratOf b
  return ⟨lower, strict, b, q, eq, cert⟩

/-- Read an inequality `a ≤ b`, `a < b`, `a ≥ b` or `a > b` as `(a, b, strict)`. -/
private def inequality? (ty : Expr) : Option (Expr × Expr × Bool) :=
  match ty.getAppFnArgs with
  | (``LE.le, #[_, _, a, b]) => some (a, b, false)
  | (``LT.lt, #[_, _, a, b]) => some (a, b, true)
  | (``GE.ge, #[_, _, a, b]) => some (b, a, false)
  | (``GT.gt, #[_, _, a, b]) => some (b, a, true)
  | _ => none

/-- The result of the coefficient route. -/
inductive Outcome where
  /-- The goal is closed. -/
  | proved
  /-- The goal is not a bound on a series over its whole domain. -/
  | notMine

/-- The polynomial side of a real goal and the sides of the bound. -/
private inductive Shape where
  /-- `|e| ≤ c` or `|e| < c` -/
  | abs (e c : Expr) (strict : Bool)
  /-- `b ≤ e` or `b < e` -/
  | lower (e b : Expr) (strict : Bool)
  /-- `e ≤ b` or `e < b` -/
  | upper (e b : Expr) (strict : Bool)
  /-- `a ≤ b` or `a < b` with the variable on both sides, read as `0 ≤ b - a` -/
  | diff (a b : Expr) (strict : Bool)

/-- The shape of a real goal in the variable `v`. -/
private def shape? (target : Expr) (v : FVarId) : Option Shape := do
  let (lhs, rhs, strict) ← inequality? target
  if lhs.isAppOfArity ``abs 4 && lhs.appArg!.containsFVar v && !rhs.containsFVar v then
    return .abs lhs.appArg! rhs strict
  match lhs.containsFVar v, rhs.containsFVar v with
  | false, true => return .lower rhs lhs strict
  | true, false => return .upper lhs rhs strict
  | true, true => return .diff lhs rhs strict
  | false, false => none

/-- The certificate options must match the sides of the goal. -/
private def checkCerts (certs : Certs) (lower upper : Bool) : TacticM Unit := do
  if let some c := certs.lower then
    unless lower do throwErrorAt c "interval: the goal has no lower bound for `lower`"
  if let some c := certs.upper then
    unless upper do throwErrorAt c "interval: the goal has no upper bound for `upper`"

/-- A real goal on the family of `rd`, proved at the value `X` of the family: the sides of
`shape`, then `|X| ≤ c` from both sides or the single side itself. -/
private def proveShape (shape : Shape) (certs : Certs) (fam : Family) (X : Expr)
    (extra : Array Expr) (verify : Expr → TacticM Expr) : TacticM Expr := do
  match shape with
  | .abs _ c strict =>
      checkCerts certs true true
      let ps ← proveSides fam #[← sideOf true strict (← mkAppM ``Neg.neg #[c]) certs.lower,
        ← sideOf false strict c certs.upper] extra verify
      let iff ← if strict then mkAppOptM ``abs_lt #[q(ℝ), none, none, none, X, c, none]
        else mkAppOptM ``abs_le #[q(ℝ), none, none, none, X, c]
      mkAppM ``Iff.mpr #[iff, ← mkAppM ``And.intro #[ps[0]!, ps[1]!]]
  | .lower _ b strict =>
      checkCerts certs true false
      return (← proveSides fam #[← sideOf true strict b certs.lower] extra verify)[0]!
  | .upper _ b strict =>
      checkCerts certs false true
      return (← proveSides fam #[← sideOf false strict b certs.upper] extra verify)[0]!
  | .diff _ _ strict =>
      checkCerts certs true false
      return (← proveSides fam #[← sideOf true strict q((0 : ℝ)) certs.lower] extra verify)[0]!

/-- The polynomial expression of a shape. -/
private def Shape.poly : Shape → MetaM Expr
  | .abs e .. | .lower e .. | .upper e .. => pure e
  | .diff a b _ => mkAppM ``HSub.hSub #[b, a]

/-- The goal that a shape proves about its polynomial `e`: the target itself, or `0 ≤ b - a`. -/
private def Shape.goal (shape : Shape) (target : Expr) : MetaM Expr := do
  match shape with
  | .diff a b strict => mkAppM (if strict then ``LT.lt else ``LE.le) #[q((0 : ℝ)), ← mkAppM
      ``HSub.hSub #[b, a]]
  | _ => pure target

/-- From the proof of `Shape.goal`, the proof of the target. -/
private def Shape.finish (shape : Shape) (p : Expr) : MetaM Expr := do
  match shape with
  | .diff _ _ strict => mkAppM (if strict then ``lt_of_sub_pos else ``le_of_sub_nonneg) #[p]
  | _ => pure p

/-- Prove a real goal on the circle, at the variable `u`. -/
private def proveCircle (target : Expr) (u : Expr) (certs : Certs)
    (verify : Expr → TacticM Expr) : TacticM (Option Expr) := do
  let some shape := shape? target u.fvarId! | return none
  let e ← shape.poly
  let some rd ← read? (.circle u) e | return none
  let goal ← shape.goal target
  let pF ← proveShape shape certs (← trigFamily rd u) rd.value rd.closed verify
  shape.finish (← transport goal e rd.proof pF)

/-- Prove a real goal on `[lo, hi]` at the variable `x` with `hx : x ∈ Set.Icc lo hi`: a power
series through Horner's rule, or a Chebyshev series through the cosine polynomial with the same
coefficients. -/
private def proveInterval (target x lo hi hx : Expr) (certs : Certs)
    (verify : Expr → TacticM Expr) : TacticM (Option Expr) := do
  let some shape := shape? target x.fvarId! | return none
  let e ← shape.poly
  let dom := Domain.interval x
  let some rd ← read? dom e | return none
  let goal ← shape.goal target
  let pF ← match rd.basis, rd.point with
    | .cheb, some y => do
        -- `∀ u, P (∑ aₖ cos (k u))`, then `Coeff.forall_Icc_chebyshev` at `y`
        let P := Expr.lam `t q(ℝ) (← kabstract goal e) .default
        let h ← withLocalDeclD `u q(ℝ) fun u => do
          let empty := mkApp (mkConst ``List.nil [0]) (mkConst ``Rat)
          let rd' : Form := { rd with basis := .cos, second := empty, point := none }
          let cosF ← mkAppOptM ``Coeff.series #[q(ℝ), none, ← basisFun (.circle u) .cos none,
            rd.main]
          let sinF ← mkAppOptM ``Coeff.series #[q(ℝ), none, ← basisFun (.circle u) .sin none,
            rd'.second]
          let value ← mkAppM ``HAdd.hAdd #[cosF, sinF]
          let pV ← proveShape shape certs (← trigFamily rd' u) value rd.closed verify
          let eq ← proveBy (← mkEq value cosF)
            (← `(tactic| simp only [Coeff.series_nil, add_zero]))
            m!"interval: could not drop the empty sine part"
          let pV ← mkAppM ``Eq.mp #[← mkAppM ``congrArg #[P, eq], pV]
          mkLambdaFVars #[u] pV
        let one := q((1 : ℝ))
        let hy ← proveBy (← mkAppM ``Membership.mem #[← mkAppM ``Set.Icc #[q((-1 : ℝ)), one], y])
          (← `(tactic| (simp only [Set.mem_Icc] at *; constructor <;> linarith)))
          m!"interval: could not prove that {y} lies in [-1, 1]"
        let a ← withLocalDeclD `k q(ℕ) fun k => do
          mkLambdaFVars #[k] (← mkAppOptM ``Rat.cast #[q(ℝ), none,
            ← mkAppM ``List.getD #[rd.main, k, toExpr (0 : ℚ)]])
        let thm ← mkAppOptM ``Coeff.forall_Icc_chebyshev
          #[a, ← mkAppM ``List.length #[rd.main], P, h]
        pure (mkAppN thm #[y, hy])
    | _, _ => do
        let (qlo, elo) ← ratOf lo
        let (qhi, ehi) ← ratOf hi
        -- `x ∈ Set.Icc ↑qlo ↑qhi` from `hx`
        let h1 ← mkAppM ``le_of_eq_of_le #[← mkAppM ``Eq.symm #[elo], ← mkAppM ``And.left #[hx]]
        let h2 ← mkAppM ``le_of_le_of_eq #[← mkAppM ``And.right #[hx], ehi]
        let hx' ← mkAppM ``And.intro #[h1, h2]
        proveShape shape certs (← powerFamily rd x hx' qlo qhi) rd.value rd.closed verify
  shape.finish (← transport goal e rd.proof pF)

/-- Prove `‖e‖ ≤ c`, `‖e‖ < c`, `c ≤ ‖e‖` or `c < ‖e‖` on the unit circle, at `z` with
`hz : ‖z‖ = 1`, from a bound on `‖e‖²`. -/
private def proveSphere (target z hz : Expr) (certs : Certs)
    (verify : Expr → TacticM Expr) : TacticM (Option Expr) := do
  let some (lhs, rhs, strict) := inequality? target | return none
  let v := z.fvarId!
  let norm? (t : Expr) : Option Expr :=
    if t.isAppOfArity ``Norm.norm 3 && t.appArg!.containsFVar v then some t.appArg! else none
  let (e, c, upper) ← match norm? lhs, norm? rhs with
    | some e, none => if rhs.containsFVar v then return none else pure (e, rhs, true)
    | none, some e => if lhs.containsFVar v then return none else pure (e, lhs, false)
    | _, _ => return none
  let some rd ← read? (.sphere z) e | return none
  checkCerts certs (!upper) upper
  let (q, _) ← ratOf c
  let X := rd.value
  let nonneg ← mkAppM ``norm_nonneg #[X]
  let two := q((2 : ℕ))
  let two0 ← proveBy (← mkAppM ``Ne #[two, q((0 : ℕ))]) (← `(tactic| norm_num))
    m!"interval: could not prove that 2 is not 0"
  let pF ← if !upper && (q < 0 || (q = 0 && !strict)) then do
      -- `c ≤ 0 ≤ ‖X‖`, with only the side conditions of the reading for the kernel
      unless rd.closed.isEmpty do
        let tys ← rd.closed.mapM fun h => do instantiateMVars (← inferType h)
        let conj ← tys.pop.foldrM (fun t acc => mkAppM ``And #[t, acc]) tys.back!
        let parts ← splitAnd (← verify conj) rd.closed.size
        for h in rd.closed, p in parts do h.mvarId!.assign p
      let hc ← proveBy (← mkAppM (if strict then ``LT.lt else ``LE.le) #[c, q((0 : ℝ))])
        (← `(tactic| norm_num)) m!"interval: could not prove that {c} is at most zero"
      mkAppM (if strict then ``lt_of_lt_of_le else ``le_trans) #[hc, nonneg]
    else do
      if q < 0 then throwError "interval: the bound {c} is negative, so the goal is false"
      let hc0 ← proveBy (← mkAppM ``LE.le #[q((0 : ℝ)), c]) (← `(tactic| norm_num))
        m!"interval: could not prove that {c} is nonnegative"
      let c2 ← mkAppM ``HPow.hPow #[c, two]
      let (q2, e2) ← ratOf c2
      let fam ← sphereFamily rd z hz
      let side : Side := ⟨!upper, strict, c2, q2, e2, if upper then certs.upper else certs.lower⟩
      let h := (← proveSides fam #[side] rd.closed verify)[0]!
      let iff ← mkAppM (if strict then ``pow_lt_pow_iff_left₀ else ``pow_le_pow_iff_left₀)
        (if upper then #[nonneg, hc0, two0] else #[hc0, nonneg, two0])
      mkAppM ``Iff.mp #[iff, h]
  transport target e rd.proof pF

/-- Prove the goal if it bounds a polynomial or series over its whole domain: `∀ u : ℝ, …`,
`∀ x ∈ Set.Icc lo hi, …` or `∀ z : ℂ, ‖z‖ = 1 → …`. The answer is `.notMine` when the goal has
another shape or its polynomial side is not a series in the bound variable, and then `interval`
goes on to the boxes; `verify` proves a closed proposition in the kernel. -/
def run (goal : MVarId) (certs : Certs) (verify : Expr → TacticM Expr) : TacticM Outcome := do
  let saved ← saveState
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let .forallE _ dom _ _ := ty | return .notMine
  let real ← isDefEq dom q(ℝ)
  let complex ← if real then pure false else isDefEq dom q(ℂ)
  unless real || complex do return .notMine
  let (v, g) ← goal.intro1P
  let proved ← g.withContext do
    let vE := mkFVar v
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if real then
      if let .forallE _ mem _ _ := ty then
        let_expr Membership.mem _ _ _ s x := mem | return false
        let_expr Set.Icc _ _ lo hi := s | return false
        unless x == vE do return false
        let (h, g') ← g.intro1P
        g'.withContext do
          let some pf ← proveInterval (← g'.getType) vE lo hi (mkFVar h) certs verify
            | return false
          g'.assign pf
          return true
      else
        let some pf ← proveCircle ty vE certs verify | return false
        g.assign pf
        return true
    else
      let .forallE _ hzTy _ _ := ty | return false
      let_expr Eq _ nz one := hzTy | return false
      unless nz.isAppOfArity ``Norm.norm 3 && nz.appArg! == vE do return false
      unless ← isDefEq one q((1 : ℝ)) do return false
      let (h, g') ← g.intro1P
      g'.withContext do
        let some pf ← proveSphere (← g'.getType) vE (mkFVar h) certs verify | return false
        g'.assign pf
        return true
  if proved then return .proved
  saved.restore
  return .notMine

/-- The first real variable under a cosine or a sine in `e`. -/
private def trigVar? (e : Expr) : MetaM (Option Expr) := do
  let some t := e.find? fun t => t.isAppOfArity ``Real.cos 1 || t.isAppOfArity ``Real.sin 1
    | return none
  for fv in (collectFVars {} t.appArg!).fvarIds do
    if ← isDefEq (← fv.getType) q(ℝ) then return some (mkFVar fv)
  return none

/-- A trigonometric polynomial in a free variable `u`: prove the bound for every `u` and apply it.
`.notMine` when the goal is not of this form. -/
def runFree (goal : MVarId) (certs : Certs) (verify : Expr → TacticM Expr) : TacticM Outcome :=
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let some u ← trigVar? ty | return .notMine
    let all ← mkForallFVars #[u] ty
    let m ← mkFreshExprMVar all
    match ← run m.mvarId! certs verify with
    | .proved => goal.assign (mkApp (← instantiateMVars m) u); return .proved
    | .notMine => return .notMine

end FloatLib.Numerics.Interval.Tactic.Coeff
