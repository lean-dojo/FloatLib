/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public import FloatLib.Numerics.Enclosure.Expression.Form

/-!
# Soundness of the definiteness check of quadratic forms

`Form.eval` is the real value of a form at an assignment of its variables. A form that
`Form.definiteOn` accepts on a box is nonnegative at every real assignment of the box
(`Form.nonneg_of_definiteOn`), and with the strict check it is nonpositive only where every
coordinate vanishes (`Form.vanishes_of_definiteOn`), which is nowhere when the constant one is a
coordinate.

The proof follows the check. The real Schur complement (`Form.reduceReal`) of a matrix inside the
interval matrix lies inside the interval complement (`Form.reduce_sound`), the form is the pivot
times a square plus the form of the complement (`Form.quad_reduceReal`), and induction on the
number of rows gives the sign (`Form.definite_sound`). The statements hold in any dimension.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

variable {functions : Nat → List ℝ → ℝ}

/-- The real value of a coordinate: a power of the variable minus its center, or one. -/
def Shift.eval (values : Nat → ℝ) : Shift → ℝ
  | .var i center extra => (values i - center) ^ (extra + 1)
  | .one => 1

namespace Form

/-- The sum of the products of two lists of reals, over their common length. -/
def dot : List ℝ → List ℝ → ℝ
  | m :: ms, d :: ds => m * d + dot ms ds
  | _, _ => 0

/-- The value at `ds` of the symmetric form whose upper triangle has the given rows:
`Σ M k k * d k ^ 2 + 2 * Σ_{k < l} M k l * d k * d l`. -/
def quad : List (List ℝ) → List ℝ → ℝ
  | (a :: border) :: rows, d :: ds => a * d ^ 2 + 2 * d * dot border ds + quad rows ds
  | _, _ => 0

/-- The real value of a form at an assignment of its variables. -/
noncomputable def eval (f : Form) (values : Nat → ℝ)
    (functions : Nat → List ℝ → ℝ := fun _ _ => 0) : ℝ :=
  quad (f.rows.map fun row => row.map fun e => e.eval values functions)
    (f.coordinates.map (Shift.eval values))

/-- `x - w * y` entry by entry on reals, or `none` when the lengths differ. -/
def eliminateReal (w : ℝ) : List ℝ → List ℝ → Option (List ℝ)
  | [], [] => some []
  | x :: xs, y :: ys => (eliminateReal w xs ys).map fun rest => (x - w * y) :: rest
  | _, _ => none

/-- The real Schur complement of the pivot `a` with border `border` in the remaining rows. -/
noncomputable def reduceReal (a : ℝ) : List ℝ → List (List ℝ) → Option (List (List ℝ))
  | [], [] => some []
  | t :: border, row :: rows =>
    (eliminateReal (t / a) row (t :: border)).bind fun first =>
      (reduceReal a border rows).map fun rest => first :: rest
  | _, _ => none

/-- A sum of products with zeros is zero. -/
theorem dot_eq_zero {ms ds : List ℝ} (h : ∀ d ∈ ds, d = 0) : dot ms ds = 0 := by
  induction ms generalizing ds with
  | nil => simp [dot]
  | cons m ms ih =>
    cases ds with
    | nil => simp [dot]
    | cons d ds =>
      rw [dot, h d (by simp), ih fun e he => h e (by simp [he])]
      ring

/-- A sum of products of zeros is zero. -/
theorem dot_zero_left {ms ds : List ℝ} (h : ∀ m ∈ ms, m = 0) : dot ms ds = 0 := by
  induction ms generalizing ds with
  | nil => simp [dot]
  | cons m ms ih =>
    cases ds with
    | nil => simp [dot]
    | cons d ds =>
      rw [dot, h m (by simp), ih fun e he => h e (by simp [he])]
      ring

/-- Elimination subtracts `w` times the second sum of products from the first. -/
theorem dot_eliminateReal {w : ℝ} {xs ys zs : List ℝ} (h : eliminateReal w xs ys = some zs)
    (ds : List ℝ) : dot zs ds = dot xs ds - w * dot ys ds := by
  induction xs generalizing ys zs ds with
  | nil =>
    cases ys with
    | nil =>
      cases Option.some.inj h
      simp [dot]
    | cons y ys => simp [eliminateReal] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [eliminateReal] at h
    | cons y ys =>
      simp only [eliminateReal, Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      cases ds with
      | nil => simp [dot]
      | cons d ds =>
        rw [dot, dot, dot, ih hrest ds]
        ring

/-- The form of the Schur complement is the form of the remaining rows minus the square of the
border's sum of products over the pivot. -/
theorem quad_reduceReal {a : ℝ} (ha : a ≠ 0) {border : List ℝ} {rows red : List (List ℝ)}
    (h : reduceReal a border rows = some red) (ds : List ℝ) :
    quad red ds = quad rows ds - dot border ds ^ 2 / a := by
  induction border generalizing rows red ds with
  | nil =>
    cases rows with
    | nil =>
      cases Option.some.inj h
      simp [quad, dot]
    | cons row rows => simp [reduceReal] at h
  | cons t border ih =>
    cases rows with
    | nil => simp [reduceReal] at h
    | cons row rows =>
      simp only [reduceReal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨first, hfirst, rest, hrest, rfl⟩ := h
      cases row with
      | nil => simp [eliminateReal] at hfirst
      | cons r row =>
        simp only [eliminateReal, Option.map_eq_some_iff] at hfirst
        obtain ⟨tail, htail, rfl⟩ := hfirst
        cases ds with
        | nil => simp [quad, dot]
        | cons d ds =>
          rw [quad, quad, dot, ih hrest ds, dot_eliminateReal htail ds]
          field_simp
          ring

/-- The Schur complement has one row for each remaining row. -/
theorem length_reduceReal {a : ℝ} {border : List ℝ} {rows red : List (List ℝ)}
    (h : reduceReal a border rows = some red) : red.length = rows.length := by
  induction border generalizing rows red with
  | nil =>
    cases rows with
    | nil =>
      cases Option.some.inj h
      rfl
    | cons row rows => simp [reduceReal] at h
  | cons t border ih =>
    cases rows with
    | nil => simp [reduceReal] at h
    | cons row rows =>
      simp only [reduceReal, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨first, -, rest, hrest, rfl⟩ := h
      simp [ih hrest]

variable {α : Type*} {B : Backend α}

/-- Interval elimination encloses real elimination. -/
theorem eliminate_sound (hB : B.Sound functions) {w : Interval α} {wr : ℝ}
    (hw : w.ContainsReal B.decode wr) {xs ys zs : List (Interval α)} {xr yr : List ℝ}
    (h : eliminate B w xs ys = some zs)
    (hx : List.Forall₂ (fun I x => I.ContainsReal B.decode x) xs xr)
    (hy : List.Forall₂ (fun I x => I.ContainsReal B.decode x) ys yr) :
    ∃ zr, eliminateReal wr xr yr = some zr ∧
      List.Forall₂ (fun I x => I.ContainsReal B.decode x) zs zr := by
  induction hx generalizing ys yr zs with
  | nil =>
    cases hy with
    | nil =>
      cases Option.some.inj h
      exact ⟨[], rfl, .nil⟩
    | cons _ _ => simp [eliminate] at h
  | @cons x xv xs xr hxv _ ih =>
    cases hy with
    | nil => simp [eliminate] at h
    | @cons y yv ys yr hyv hys =>
      rw [eliminate] at h
      cases hp : B.binary? .mul w y with
      | none => simp [hp] at h
      | some p =>
        cases hd : B.binary? .sub x p with
        | none => simp [hp, hd] at h
        | some d =>
          cases hrest : eliminate B w xs ys with
          | none => simp [hp, hd, hrest] at h
          | some rest =>
            simp only [hp, hd, hrest, Option.some.injEq] at h
            subst h
            obtain ⟨zr, hzr, hzs⟩ := ih hrest hys
            exact ⟨(xv - wr * yv) :: zr, by simp [eliminateReal, hzr],
              .cons (hB.binary hd hxv (hB.binary hp hw hyv)) hzs⟩

/-- The interval Schur complement encloses the real one. -/
theorem reduce_sound (hB : B.Sound functions) {a : Interval α} {ar : ℝ}
    (ha : a.ContainsReal B.decode ar) {border : List (Interval α)} {borderReal : List ℝ}
    (hborder : List.Forall₂ (fun I x => I.ContainsReal B.decode x) border borderReal)
    {rows red : List (List (Interval α))} {rowsReal : List (List ℝ)}
    (hrows : List.Forall₂ (List.Forall₂ fun I x => I.ContainsReal B.decode x) rows rowsReal)
    (h : reduce B a border rows = some red) :
    ∃ redReal, reduceReal ar borderReal rowsReal = some redReal ∧
      List.Forall₂ (List.Forall₂ fun I x => I.ContainsReal B.decode x) red redReal := by
  induction hborder generalizing rows rowsReal red with
  | nil =>
    cases hrows with
    | nil =>
      cases Option.some.inj h
      exact ⟨[], rfl, .nil⟩
    | cons _ _ => simp [reduce] at h
  | @cons t tv border borderReal htv hborder ih =>
    cases hrows with
    | nil => simp [reduce] at h
    | @cons row rowReal rows rowsReal hrow hrows =>
      rw [reduce] at h
      cases hw : B.binary? .div t a with
      | none => simp [hw] at h
      | some w =>
        cases hfirst : eliminate B w row (t :: border) with
        | none => simp [hw, hfirst] at h
        | some first =>
          cases hrest : reduce B a border rows with
          | none => simp [hw, hfirst, hrest] at h
          | some rest =>
            simp only [hw, hfirst, hrest, Option.some.injEq] at h
            subst h
            have hwr : w.ContainsReal B.decode (tv / ar) := hB.binary hw htv ha
            obtain ⟨firstReal, hfirstReal, hfirstIn⟩ :=
              eliminate_sound hB hwr hfirst hrow (.cons htv hborder)
            obtain ⟨restReal, hrestReal, hrestIn⟩ := ih hrows hrest
            exact ⟨firstReal :: restReal, by simp [reduceReal, hfirstReal, hrestReal],
              .cons hfirstIn hrestIn⟩

/-- A real inside an enclosure is at least its decoded lower endpoint. -/
theorem lower_le {I : Interval α} {x : ℝ} (hx : I.ContainsReal B.decode x) {lo : ℚ}
    (hlo : B.decode I.lo = some lo) : (lo : ℝ) ≤ x := by
  obtain ⟨a, _, ha, _, hax, _⟩ := hx
  have : (lo : ℝ) = a := by simpa [hlo] using ha
  rw [this]
  exact hax

/-- A real inside an enclosure that is the point zero is zero. -/
theorem eq_zero_of_isZero {I : Interval α} {x : ℝ} (hx : I.ContainsReal B.decode x)
    (h : isZero B I = true) : x = 0 :=
  Backend.eq_zero_of_isZero hx h

/-- Reals inside enclosures that are all the point zero are all zero. -/
theorem all_zero_of_isZero {border : List (Interval α)} {reals : List ℝ}
    (hin : List.Forall₂ (fun I x => I.ContainsReal B.decode x) border reals)
    (h : ∀ I ∈ border, isZero B I = true) : ∀ m ∈ reals, m = 0 := by
  induction hin with
  | nil => simp
  | @cons I x border reals hx _ ih =>
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact eq_zero_of_isZero hx (h I (by simp))
    · exact ih (fun J hJ => h J (by simp [hJ])) m hm

/-- With a positive pivot, a form is the pivot times a square plus the form of its Schur
complement, so it inherits the sign of the complement, and vanishes only where it does. -/
theorem quad_of_reduceReal {a : ℝ} (ha : 0 < a) {border : List ℝ} {rows red : List (List ℝ)}
    (h : reduceReal a border rows = some red) (d : ℝ) (ds : List ℝ) :
    quad ((a :: border) :: rows) (d :: ds) =
      a * (d + dot border ds / a) ^ 2 + quad red ds := by
  rw [quad, quad_reduceReal ha.ne' h ds]
  field_simp
  ring

/--
An accepted interval matrix contains only symmetric matrices whose form is nonnegative, and with
the strict check only matrices whose form vanishes at the zero vector alone.
-/
theorem definite_sound (hB : B.Sound functions) (strict : Bool) (fuel : Nat) :
    ∀ {rowsI : List (List (Interval α))} {rows : List (List ℝ)},
      definite B strict fuel rowsI = true →
      List.Forall₂ (List.Forall₂ fun I x => I.ContainsReal B.decode x) rowsI rows →
      ∀ ds : List ℝ, ds.length = rows.length →
        0 ≤ quad rows ds ∧ (strict = true → quad rows ds = 0 → ∀ d ∈ ds, d = 0) := by
  induction fuel with
  | zero =>
    intro rowsI rows h hrows ds hds
    cases hrows with
    | nil =>
      cases ds with
      | nil => simp [quad]
      | cons d ds => simp at hds
    | cons _ _ => simp [definite] at h
  | succ fuel ih =>
    intro rowsI rows h hrows ds hds
    cases hrows with
    | nil =>
      cases ds with
      | nil => simp [quad]
      | cons d ds => simp at hds
    | @cons rowI row restI rest hrow hrest =>
      cases hrow with
      | nil => simp [definite] at h
      | @cons aI a borderI border ha hborder =>
        cases ds with
        | nil => simp at hds
        | cons d ds =>
          have hlen : ds.length = rest.length := by simpa using hds
          rw [definite] at h
          cases hlo : B.decode aI.lo with
          | none => simp [hlo] at h
          | some lo =>
            simp only [hlo] at h
            by_cases hpos : Kernel.Q.lt 0 lo = true
            · rw [ite_eq_left hpos] at h
              have hapos : 0 < a := lt_of_lt_of_le
                (by exact_mod_cast (Kernel.Q.lt_iff 0 lo).1 hpos) (lower_le ha hlo)
              cases hred : reduce B aI borderI restI with
              | none => simp [hred] at h
              | some redI =>
                obtain ⟨red, hredReal, hredIn⟩ := reduce_sound hB ha hborder hrest hred
                obtain ⟨hnonneg, hzero⟩ := ih (by simpa [hred] using h) hredIn ds
                  (hlen.trans (length_reduceReal hredReal).symm)
                rw [quad_of_reduceReal hapos hredReal]
                have hsquare : 0 ≤ a * (d + dot border ds / a) ^ 2 := by positivity
                refine ⟨add_nonneg hsquare hnonneg, fun hstrict hq => ?_⟩
                have hparts := (add_eq_zero_iff_of_nonneg hsquare hnonneg).1 hq
                have hrest0 : ∀ e ∈ ds, e = 0 := hzero hstrict hparts.2
                have hsq : a * (d + dot border ds / a) ^ 2 = 0 := hparts.1
                rw [dot_eq_zero hrest0] at hsq
                have hd : d = 0 := by
                  have : (d + 0 / a) ^ 2 = 0 := by
                    rcases mul_eq_zero.1 hsq with h0 | h0
                    · exact absurd h0 hapos.ne'
                    · exact h0
                  simpa using this
                intro e he
                rcases List.mem_cons.1 he with rfl | he
                · exact hd
                · exact hrest0 e he
            · rw [ite_eq_right hpos] at h
              simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
                Kernel.Q.le_iff] at h
              obtain ⟨⟨⟨hstrict, hlo0⟩, hzeroBorder⟩, hrestDefinite⟩ := h
              have ha0 : 0 ≤ a := le_trans (by exact_mod_cast hlo0) (lower_le ha hlo)
              have hborder0 := all_zero_of_isZero hborder hzeroBorder
              obtain ⟨hnonneg, -⟩ := ih hrestDefinite hrest ds hlen
              rw [quad, dot_zero_left hborder0]
              have hsquare : 0 ≤ a * d ^ 2 := mul_nonneg ha0 (sq_nonneg d)
              refine ⟨by simpa using add_nonneg hsquare hnonneg, fun hs => ?_⟩
              rw [hstrict] at hs
              cases hs

/-- The enclosures of a row contain the real values of its entries. -/
theorem encloseRow_sound (hB : B.Sound functions) {intervals : List (Interval α)}
    {values : Nat → ℝ}
    (henv : ∀ (i : Nat) (I : Interval α), intervals[i]? = some I →
      I.ContainsReal B.decode (values i))
    {row : List Expr} {enclosed : List (Interval α)}
    (h : encloseRow B intervals row = some enclosed) :
    List.Forall₂ (fun I x => I.ContainsReal B.decode x) enclosed
      (row.map fun e => e.eval values functions) := by
  induction row generalizing enclosed with
  | nil =>
    cases Option.some.inj h
    exact .nil
  | cons e es ih =>
    rw [encloseRow] at h
    cases he : e.evalZero? B (fun i => Kernel.Seq.nth? intervals i) with
    | none => simp [he] at h
    | some I =>
      cases hrest : encloseRow B intervals es with
      | none => simp [he, hrest] at h
      | some rest =>
        simp only [he, hrest, Option.some.injEq] at h
        subst h
        refine .cons (e.containsReal_evalZero? hB (fun i J hJ => henv i J ?_) he) (ih hrest)
        simpa [Kernel.Seq.nth?_eq] using hJ

/-- The enclosures of the rows contain the real values of their entries. -/
theorem encloseRows_sound (hB : B.Sound functions) {intervals : List (Interval α)}
    {values : Nat → ℝ}
    (henv : ∀ (i : Nat) (I : Interval α), intervals[i]? = some I →
      I.ContainsReal B.decode (values i))
    {rows : List (List Expr)} {enclosed : List (List (Interval α))}
    (h : encloseRows B intervals rows = some enclosed) :
    List.Forall₂ (List.Forall₂ fun I x => I.ContainsReal B.decode x) enclosed
      (rows.map fun row => row.map fun e => e.eval values functions) := by
  induction rows generalizing enclosed with
  | nil =>
    cases Option.some.inj h
    exact .nil
  | cons row rows ih =>
    rw [encloseRows] at h
    cases hrow : encloseRow B intervals row with
    | none => simp [hrow] at h
    | some first =>
      cases hrest : encloseRows B intervals rows with
      | none => simp [hrow, hrest] at h
      | some rest =>
        simp only [hrow, hrest, Option.some.injEq] at h
        subst h
        exact .cons (encloseRow_sound hB henv hrow) (ih hrest)

/-- The sign statement of `definite_sound` for a form accepted on a box. -/
theorem definiteOn_sound (hB : B.Sound functions) {strict : Bool} {f : Form} {box : Box}
    (h : f.definiteOn B strict box = true) {values : Nat → ℝ} (hbox : box.ContainsReal values) :
    0 ≤ f.eval values functions ∧ (strict = true → f.eval values functions = 0 →
      ∀ s ∈ f.coordinates, s.eval values = 0) := by
  unfold definiteOn at h
  cases hintervals : box.enclose? B with
  | none => simp [hintervals] at h
  | some intervals =>
    cases hrows : encloseRows B intervals f.rows with
    | none => simp [hintervals, hrows] at h
    | some rows =>
      simp only [hintervals, hrows, Bool.and_eq_true, beq_iff_eq] at h
      have hin := encloseRows_sound hB (Box.containsReal_enclose? hB hintervals hbox) hrows
      have hlen : (f.coordinates.map (Shift.eval values)).length =
          (f.rows.map fun row => row.map fun e => e.eval values functions).length := by
        rw [List.length_map, h.1, List.Forall₂.length_eq hin]
      obtain ⟨hnonneg, hzero⟩ := definite_sound hB strict rows.length h.2 hin _ hlen
      exact ⟨hnonneg, fun hstrict hq s hs =>
        hzero hstrict hq _ (List.mem_map_of_mem hs)⟩

/-- A form accepted on a box is nonnegative at every real assignment of the box. -/
theorem nonneg_of_definiteOn (hB : B.Sound functions) {strict : Bool} {f : Form} {box : Box}
    (h : f.definiteOn B strict box = true) {values : Nat → ℝ} (hbox : box.ContainsReal values) :
    0 ≤ f.eval values functions :=
  (definiteOn_sound hB h hbox).1

/-- A form accepted by the strict check on a box is nonpositive, at a real assignment of the
box, only where every coordinate vanishes. -/
theorem vanishes_of_definiteOn (hB : B.Sound functions) {f : Form} {box : Box}
    (h : f.definiteOn B true box = true) {values : Nat → ℝ} (hbox : box.ContainsReal values)
    (hle : f.eval values functions ≤ 0) : ∀ s ∈ f.coordinates, s.eval values = 0 :=
  (definiteOn_sound hB h hbox).2 rfl (le_antisymm hle (nonneg_of_definiteOn hB h hbox))

/-- Where every coordinate vanishes, the assignment lies in the pinned box. -/
theorem containsReal_pinned {coordinates : List Shift} {box : Box} {values : Nat → ℝ}
    (hbox : box.ContainsReal values) (h : ∀ s ∈ coordinates, s.eval values = 0) :
    Box.ContainsReal (coordinates.foldl Shift.pin box) values := by
  induction coordinates generalizing box with
  | nil => exact hbox
  | cons s rest ih =>
    refine ih ?_ fun t ht => h t (by simp [ht])
    cases s with
    | one => exact hbox
    | var i center extra =>
      have hvalue : values i = center := by
        have := h (.var i center extra) (by simp)
        simpa [Shift.eval, sub_eq_zero] using this
      exact Box.containsReal_set hbox ((containsReal_some_iff _ _).2 (by simp [hvalue]))

end Form

/-- A coordinate that is excluded on a box vanishes at no real assignment of the box. -/
theorem Shift.excluded_sound {box : Box} {s : Shift} (h : s.excluded box = true)
    {values : Nat → ℝ} (hbox : box.ContainsReal values) : s.eval values ≠ 0 := by
  cases s with
  | one => simp [Shift.eval]
  | var i center extra =>
    simp only [Shift.excluded, Kernel.Seq.nth?_eq] at h
    cases hI : box[i]? with
    | none => simp [hI] at h
    | some I =>
      simp only [hI, Bool.or_eq_true, Kernel.Q.lt_iff] at h
      obtain ⟨hlo, hhi⟩ := (containsReal_some_iff I _).1 (hbox i I hI)
      intro hzero
      have hvalue : values i = center := by simpa [Shift.eval, sub_eq_zero] using hzero
      rw [hvalue] at hlo hhi
      rcases h with h | h
      · exact absurd hlo (not_le.2 (by exact_mod_cast h))
      · exact absurd hhi (not_le.2 (by exact_mod_cast h))

end FloatLib.Numerics.Interval
