/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Interval.Constraints.Reify
public meta import FloatLib.Numerics.Enclosure.Expression.Extensions

/-!
# The search for a refutation

The search evaluates a reified constraint on a box with three values. An atom fails on the whole
box, holds on the whole box, or is undecided, and a part that is decided is kept for every box
inside: what fails or holds on a box does so on each of its parts. A box on which the constraint is
undecided is cut in half along the coordinate whose two halves leave the least to refute, and a
box on which a nonpositive form is positive definite is replaced by the point where the form
vanishes. The result is a `Refutation`, which the kernel checks afterwards, so nothing here has to
be trusted, and the search may use any heuristic.

The enclosures are those of the check itself, run as compiled code: `oracle` evaluates an
expression, and the matrix of a form, with a backend on a box.

## Main definitions

* `Work`: the three-valued state of a constraint on a box.
* `Oracle`: what the search asks about one box.
* `descend`, `cutThenDescend`, `isolateThenDescend`: the search, the search after the cuts that
  the user gave, and the search around a ball that the user gave.
* `Stuck`, `stuckMessage`: the box where a search stopped and its report.
* `quoteRefutation`: a certificate as a term.
-/

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Constraints

/-- The state of a constraint on a box, in three values. -/
inductive Work where
  /-- The constraint has no point in the box, by this certificate. -/
  | refuted (r : Refutation)
  /-- The constraint holds at every point of the box. -/
  | holds
  /-- An undecided atom with its last enclosure, if the backend gave one. -/
  | atom (a : Atom) (range : Option (Interval ℚ))
  /-- An undecided form atom. -/
  | form (strict : Bool) (f : Form) (source : MessageData)
  /-- The states of both conjuncts. -/
  | and (left right : Work)
  /-- The states of both disjuncts. -/
  | or (left right : Work)

/-- Every atom undecided. -/
def Work.ofTree : Tree → Work
  | .atom a => .atom a none
  | .form strict f source => .form strict f source
  | .and l r => .and (Work.ofTree l) (Work.ofTree r)
  | .or l r => .or (Work.ofTree l) (Work.ofTree r)

/-- The nonpositive forms among the conjuncts of a constraint, with their paths: the forms that
can pin a box to a point. -/
def Tree.pins (tree : Tree) (path : List Bool := []) (acc : Array (List Bool × Form) := #[]) :
    Array (List Bool × Form) :=
  match tree with
  | .form false f _ => acc.push (path.reverse, f)
  | .and l r => r.pins (true :: path) (l.pins (false :: path) acc)
  | _ => acc

/-- What the search asks about one box. -/
structure Oracle where
  /-- The enclosure of an expression, or `none` when the backend gives none. -/
  range : Interval.Expr → Option (Interval ℚ)
  /-- Whether the matrix of a form is positive definite (`true`) or semidefinite. -/
  definite : Bool → Form → Bool
  /-- Whether some coordinate of a form cannot vanish. -/
  excluded : Form → Bool

/--
Evaluate the undecided atoms on a box and combine. Decided parts are kept: what fails or holds on
a box fails or holds on every box inside it. A negative form fails where its matrix is positive
semidefinite, and a nonpositive form where its matrix is positive definite and a coordinate
cannot vanish.
-/
def Work.eval (oracle : Oracle) : Work → Work
  | .atom a _ =>
    match oracle.range a.expr with
    | none => .atom a none
    | some I =>
      if a.relation.check I.hi then .refuted (.atom 0)
      else if (match a.relation with
        | .negative => decide (0 ≤ I.lo)
        | .nonpositive => decide (0 < I.lo)) then .holds
      else .atom a (some I)
  | .form true f source =>
    if oracle.definite false f then .refuted .definite else .form true f source
  | .form false f source =>
    if oracle.excluded f && oracle.definite true f then .refuted .definite
    else .form false f source
  | .and l r =>
    match l.eval oracle, r.eval oracle with
    | .refuted p, _ => .refuted (.left p)
    | _, .refuted p => .refuted (.right p)
    | .holds, .holds => .holds
    | l, r => .and l r
  | .or l r =>
    match l.eval oracle, r.eval oracle with
    | .refuted p, .refuted q => .refuted (.both p q)
    | .holds, _ => .holds
    | _, .holds => .holds
    | l, r => .or l r
  | work => work

/-- How far a constraint is from refuted on its box: zero when refuted, `none` for no bound. -/
def Work.gap : Work → Option ℚ
  | .refuted _ => some 0
  | .holds => none
  | .atom _ none => none
  | .atom _ (some I) => some (max I.hi 0)
  | .form .. => none
  | .and l r =>
    match l.gap, r.gap with
    | some a, some b => some (min a b)
    | some a, none => some a
    | none, b => b
  | .or l r =>
    match l.gap, r.gap with
    | some a, some b => some (a + b)
    | _, _ => none

/-- The variables of the undecided atoms. -/
def Work.vars (work : Work) (acc : Array Nat := #[]) : Array Nat :=
  match work with
  | .atom a _ => a.vars.foldl (fun acc i => if acc.contains i then acc else acc.push i) acc
  | .and l r => r.vars (l.vars acc)
  | .or l r => r.vars (l.vars acc)
  | _ => acc

/-- The undecided atoms with their last enclosures. -/
def Work.undecided (work : Work) (acc : Array (Atom × Option (Interval ℚ)) := #[]) :
    Array (Atom × Option (Interval ℚ)) :=
  match work with
  | .atom a range => acc.push (a, range)
  | .and l r => r.undecided (l.undecided acc)
  | .or l r => r.undecided (l.undecided acc)
  | _ => acc

/-- The undecided form atoms, by the propositions they were derived from. -/
def Work.undecidedForms (work : Work) (acc : Array MessageData := #[]) : Array MessageData :=
  match work with
  | .form _ _ source => acc.push source
  | .and l r => r.undecidedForms (l.undecidedForms acc)
  | .or l r => r.undecidedForms (l.undecidedForms acc)
  | _ => acc

/-- Why the search stopped at a box. -/
inductive StuckReason where
  /-- The constraints hold at every point of the box. -/
  | satisfied
  /-- The cuts along this branch reached the limit. -/
  | depth
  /-- The search evaluated as many boxes as it may. -/
  | budget
  /-- No coordinate of an undecided constraint has positive width. -/
  | point

/-- A box that the search could not refute. -/
structure Stuck where
  /-- The box. -/
  box : Box
  /-- The state of the constraint there. -/
  work : Work
  /-- What stopped the search. -/
  reason : StuckReason
  /-- The cuts above the box. -/
  cuts : Nat
  /-- The boxes evaluated so far. -/
  boxes : Nat

/-- The search monad: a count of evaluated boxes, and the box where the search stopped. -/
abbrev SearchM := StateRefT Nat (ExceptT Stuck MetaM)

/-- The limits and the evaluator of a search. -/
structure Search where
  /-- The oracle of a box, or `none` when the box cannot be enclosed. -/
  oracle : Box → Option Oracle
  /-- The boxes that the search may evaluate. -/
  boxes : Nat
  /-- The nonpositive forms among the conjuncts, with their paths. -/
  pins : Array (List Bool × Form) := #[]
  /-- The widths of the coordinates of the box that the search started from. -/
  widths : Array ℚ := #[]

/-- Evaluate the undecided atoms on a box and count it. -/
def Search.eval (search : Search) (work : Work) (box : Box) : SearchM Work := do
  modify (· + 1)
  return match search.oracle box with
    | none => work
    | some oracle => work.eval oracle

/-- The first nonpositive form that is positive definite on a box and may vanish there, with
its path and the part of the box where it vanishes, when that part is smaller than the box. -/
def Search.pin? (search : Search) (box : Box) : Option (List Bool × Box) := do
  let oracle ← search.oracle box
  search.pins.findSome? fun (path, f) =>
    let pinned := f.pinned box
    if !oracle.excluded f && pinned != box && oracle.definite true f then some (path, pinned)
    else none

/-- The sum of two gaps, `none` being no bound. -/
def addGap : Option ℚ → Option ℚ → Option ℚ
  | some a, some b => some (a + b)
  | _, _ => none

/-- Whether the first score is strictly better than the second. -/
def betterGap : Option ℚ → Option ℚ → Bool
  | some a, some b => a < b
  | some _, none => true
  | none, _ => false

/--
Refute an undecided constraint on a box. If a nonpositive form is positive definite on the box,
the search continues on the point where it vanishes. Otherwise the box is cut in half, at most
`depth` times along a branch. The candidates are the coordinates of the undecided atoms whose
width, relative to the box that the search started from, is at least a quarter of the largest,
so no coordinate is left behind; each is tried, widest first, and the cut whose halves have the
smallest gaps is taken.
-/
partial def descend (search : Search) (work : Work) (box : Box) (depth cuts : Nat) :
    SearchM Refutation := do
  match work with
  | .refuted r => return r
  | .holds => throwThe Stuck ⟨box, work, .satisfied, cuts, ← get⟩
  | _ =>
    if depth == 0 then throwThe Stuck ⟨box, work, .depth, cuts, ← get⟩
    if (← get) ≥ search.boxes then throwThe Stuck ⟨box, work, .budget, cuts, ← get⟩
    liftM (m := MetaM) (checkSystem "interval constraint search")
    if let some (path, pinned) := search.pin? box then
      let work ← search.eval work pinned
      return .pin path (← descend search work pinned (depth - 1) (cuts + 1))
    let width (i : Nat) : ℚ := match box[i]? with
      | some I => I.hi - I.lo
      | none => 0
    let relative (i : Nat) : ℚ := match search.widths[i]? with
      | some initial => if initial == 0 then 0 else width i / initial
      | none => width i
    let cuttable := work.vars.filter fun i => 0 < width i
    let largest := cuttable.foldl (fun m i => max m (relative i)) 0
    let candidates := (cuttable.filter fun i => largest ≤ 4 * relative i).qsort
      (fun i j => width j < width i)
    let mut best : Option (Nat × Work × Work × Box × Box × Option ℚ) := none
    for i in candidates do
      let some (lower, upper) := box.halve i | continue
      let wl ← search.eval work lower
      let wu ← search.eval work upper
      let score := addGap wl.gap wu.gap
      match best with
      | none => best := some (i, wl, wu, lower, upper, score)
      | some (_, _, _, _, _, old) =>
        if betterGap score old then best := some (i, wl, wu, lower, upper, score)
    let some (i, wl, wu, lower, upper, _) := best
      | throwThe Stuck ⟨box, work, .point, cuts, ← get⟩
    let l ← descend search wl lower (depth - 1) (cuts + 1)
    let u ← descend search wu upper (depth - 1) (cuts + 1)
    return .bisect i l u

/-- Apply the cuts that the user gave, in order, then search each part. -/
partial def cutThenDescend (search : Search) (points : List (Nat × ℚ)) (work : Work) (box : Box)
    (depth cuts : Nat) : SearchM Refutation := do
  match points with
  | [] => descend search work box depth cuts
  | (i, point) :: rest =>
    match box[i]?, box.cut i point with
    | some I, some (lower, upper) =>
      if I.lo < point ∧ point < I.hi then
        let wl ← search.eval work lower
        let wu ← search.eval work upper
        let l ← cutThenDescend search rest wl lower depth (cuts + 1)
        let u ← cutThenDescend search rest wu upper depth (cuts + 1)
        return .cut i point l u
      else cutThenDescend search rest work box depth cuts
    | _, _ => cutThenDescend search rest work box depth cuts

/--
Cut a ball out of the box, then search each part. The ball is given by an interval for each of
some coordinates; the parts of the box below and above each interval are searched with the cuts
of the user, and what remains inside every interval is searched last, where a form around the
center of the ball is expected to decide.
-/
partial def isolateThenDescend (search : Search) (ball : List (Nat × ℚ × ℚ))
    (points : List (Nat × ℚ)) (work : Work) (box : Box) (depth cuts : Nat) :
    SearchM Refutation := do
  let outside := fun work box cuts => cutThenDescend search points work box depth cuts
  match ball with
  | [] => descend search work box depth cuts
  | (i, lower, upper) :: rest =>
    let inside := fun work box cuts => isolateThenDescend search rest points work box depth cuts
    -- Cut at `point`, when it is inside the interval, and continue on each side.
    let cutAt (point : ℚ) (work : Work) (box : Box) (cuts : Nat)
        (below above : Work → Box → Nat → SearchM Refutation) : SearchM Refutation := do
      match box[i]?, box.cut i point with
      | some I, some (lowerBox, upperBox) =>
        if point ≤ I.lo then above work box cuts
        else if I.hi ≤ point then below work box cuts
        else
          let l ← below (← search.eval work lowerBox) lowerBox (cuts + 1)
          let u ← above (← search.eval work upperBox) upperBox (cuts + 1)
          return .cut i point l u
      | _, _ => above work box cuts
    cutAt lower work box cuts outside fun work box cuts =>
      cutAt upper work box cuts inside outside

/-- The oracle of a backend on a box: its enclosures with decoded endpoints, and the checks of
`Form` on the box. -/
def oracle {α : Type} (B : Backend α) (box : Box) : Option Oracle := do
  let intervals ← box.enclose? B
  pure {
    range := fun e => do
      let I ← e.evalZero? B (fun i => intervals[i]?)
      let lo ← B.decode I.lo
      let hi ← B.decode I.hi
      pure ⟨lo, hi⟩
    definite := fun strict f => f.definiteOn B strict box
    excluded := fun f => f.excluded box }

/-- The registrations of `Functions` whose real function is a unary operation of the expression
language, with that operation. -/
def unaryRegistrations : List (Name × UnaryOp) :=
  [ (``exp_extension_sound, .exp), (``log_extension_sound, .log)
  , (``sin_extension_sound, .sin), (``cos_extension_sound, .cos)
  , (``tan_extension_sound, .tan), (``arcsin_extension_sound, .asin)
  , (``arccos_extension_sound, .acos), (``arctan_extension_sound, .atan)
  , (``sinh_extension_sound, .sinh), (``cosh_extension_sound, .cosh)
  , (``tanh_extension_sound, .tanh), (``sqrt_extension_sound, .sqrt) ]

/-- The executable enclosure of each registration of `Functions`, for the search. -/
def compiledExtension? (registration : Name) : Option Extension :=
  match unaryRegistrations.lookup registration with
  | some op => some (Backend.elementaryExtension op)
  | none =>
    [ (``arsinh_extension_sound, Backend.asinhExtension)
    , (``arcosh_extension_sound, Backend.acoshExtension)
    , (``artanh_extension_sound, Backend.atanhExtension)
    , (``rpow_extension_sound, Backend.rpowExtension)
    , (``logb_extension_sound, Backend.logbExtension)
    ].lookup registration

/-! ## Messages -/

/-- A rational for a message: exact when short, and to six significant digits otherwise. -/
def ratText (q : ℚ) : String :=
  if q.den ≤ 100000 ∧ q.num.natAbs ≤ 10000000 then toString q
  else
    let value := Float.ofInt q.num / Float.ofNat q.den
    let exponent := (Float.log10 value.abs).floor
    let mantissa := value / Float.pow 10 exponent
    let digits := (mantissa * 100000).round / 100000
    if exponent.abs < 4 then s!"{(value * 1000000).round / 1000000}"
    else s!"{digits}e{exponent.toInt64}"

/-- A box for a message, at most eight coordinates. -/
def boxText (atoms : Array Lean.Expr) (box : Box) : MessageData :=
  let entries := box.take 8 |>.zipIdx |>.map fun (I, i) =>
    let atom : MessageData := match atoms[i]? with
      | some atom => m!"{atom}"
      | none => m!"x[{i}]"
    if I.lo == I.hi then m!"{atom} = {ratText I.lo}"
    else m!"{atom} ∈ [{ratText I.lo}, {ratText I.hi}]"
  let rest := if box.length ≤ 8 then [] else [m!"… ({box.length - 8} more)"]
  MessageData.joinSep (entries ++ rest) ", "

/-- The message for a box that the search could not refute. -/
def stuckMessage (atoms : Array Lean.Expr) (stuck : Stuck) (depth boxes : Nat)
    (unread : Array MessageData := #[]) : MessageData :=
  let reason : MessageData := match stuck.reason with
    | .satisfied =>
      if unread.isEmpty then m!"Every constraint holds at every point of this box, so the \
        constraints have a common point and the goal is false as stated."
      else m!"Every constraint that was read holds at every point of this box. Not read as \
        constraints, since they are not combinations of real comparisons:\n\
        {MessageData.joinSep (unread.toList.take 4 |>.map fun hypothesis => m!"  {hypothesis}")
          "\n"}"
    | .depth => m!"The limit of {depth} cuts along a branch was reached \
        ({stuck.boxes} boxes evaluated); `(depth := n)` raises it."
    | .budget => m!"The limit of {boxes} boxes was reached after {stuck.cuts} cuts on this \
        branch; `(boxes := n)` raises it."
    | .point => m!"No coordinate of an undecided constraint can be cut further \
        ({stuck.cuts} cuts on this branch, {stuck.boxes} boxes evaluated)."
  let undecided := stuck.work.undecided.toList.take 6 |>.map fun (atom, range) =>
    let needs := match atom.relation with
      | .negative => "negative"
      | .nonpositive => "nonpositive"
    let source := MessageData.nestD (MessageData.group m!"{atom.source}")
    match range with
    | some I => m!"  {source}\n    right side minus left side is in \
        [{ratText I.lo}, {ratText I.hi}]; it fails on the box once the upper end is {needs}"
    | none => m!"  {source}\n    the backend returned no enclosure on this box \
        (a division by an enclosure that contains zero, or a function outside its domain)"
  let forms := stuck.work.undecidedForms.toList.take 3 |>.map fun source =>
    m!"  the quadratic form of {source}: its matrix is not positive definite on this box"
  let undecided := undecided ++ forms
  let list := if undecided.isEmpty then m!"" else
    m!"\nUndecided there:\n{MessageData.joinSep undecided "\n"}"
  m!"interval could not refute the constraints on the box\n  {boxText atoms stuck.box}\n\
    {reason}{list}"

/-! ## Certificates as terms -/

/-- A rational as a term that the kernel evaluates with `Kernel.Q.mk`. -/
def quoteRat (q : ℚ) : Q(ℚ) :=
  have num : Q(Int) := match q.num with
    | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
    | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)
  have den : Q(Nat) := mkRawNatLit q.den
  q(Kernel.Q.mk $num $den)

/-- A certificate as a term. -/
partial def quoteRefutation : Refutation → Lean.Expr
  | .atom depth => mkApp (mkConst ``Refutation.atom) (mkRawNatLit depth)
  | .left r => mkApp (mkConst ``Refutation.left) (quoteRefutation r)
  | .right r => mkApp (mkConst ``Refutation.right) (quoteRefutation r)
  | .both l r => mkApp2 (mkConst ``Refutation.both) (quoteRefutation l) (quoteRefutation r)
  | .bisect i l u =>
    mkApp3 (mkConst ``Refutation.bisect) (mkRawNatLit i) (quoteRefutation l) (quoteRefutation u)
  | .cut i point l u =>
    mkApp4 (mkConst ``Refutation.cut) (mkRawNatLit i) (quoteRat point) (quoteRefutation l)
      (quoteRefutation u)
  | .definite => mkConst ``Refutation.definite
  | .pin path r =>
    have path : Q(List Bool) := path.foldr
      (fun (side : Bool) (rest : Q(List Bool)) =>
        if side then q(true :: $rest) else q(false :: $rest)) q([])
    mkApp2 (mkConst ``Refutation.pin) path (quoteRefutation r)

/-- The leaves of a certificate. -/
partial def leaves : Refutation → Nat
  | .bisect _ l u => leaves l + leaves u
  | .cut _ _ l u => leaves l + leaves u
  | .pin _ r => leaves r
  | _ => 1
end FloatLib.Numerics.Interval.Tactic.Constraints
