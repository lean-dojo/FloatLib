/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Closed
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof

/-!
# Soundness of closed-expression enclosures

Every enclosure that `Expr.gridEnclosureWith?` returns contains the real value of the expression
at every assignment of its inputs within their intervals, whatever the precision and degree
(`Expr.contains_gridEnclosureWith?`). `Expr.contains_gridEnclosure?` is the case of a closed
expression.
-/

public section

namespace FloatLib.Numerics.Interval

/--
A returned enclosure contains the value of the expression at every assignment `values` whose
inputs lie in the given intervals.
-/
theorem Expr.contains_gridEnclosureWith? {e : Expr} {inputs : List RationalInterval}
    {values : Nat → ℝ} {precision degree : Nat} {interval : RationalInterval}
    (hinputs : ∀ (i : Nat) (I : RationalInterval), inputs[i]? = some I → I.Contains (values i))
    (h : e.gridEnclosureWith? inputs precision degree = some interval) :
    interval.Contains (e.eval values) := by
  unfold Expr.gridEnclosureWith? at h
  obtain ⟨grid, hgrid, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [Enclosure.BinaryGrid.contains_toRationalInterval]
  refine Expr.containsReal_eval? e
    (Backend.binaryGrid_sound { precision := precision, degree := degree })
    (fun i J hJ => ?_) hgrid
  obtain ⟨I, hI, rfl⟩ := Option.map_eq_some_iff.mp hJ
  obtain ⟨hlo, hhi⟩ := hinputs i I hI
  obtain ⟨a, -, ha, -, hal, -⟩ := BinaryGrid.containsReal_enclose precision I.lo
  obtain ⟨-, d, -, hd, -, hdh⟩ := BinaryGrid.containsReal_enclose precision I.hi
  exact ⟨a, d, ha, hd, hal.trans hlo, hhi.trans hdh⟩

/-- A returned enclosure of a closed expression contains its real value. -/
theorem Expr.contains_gridEnclosure? {e : Expr} {precision degree : Nat}
    {interval : RationalInterval} (h : e.gridEnclosure? precision degree = some interval) :
    interval.Contains (e.eval fun _ => 0) :=
  Expr.contains_gridEnclosureWith? (inputs := []) (fun i I hI => by simp at hI) h

end FloatLib.Numerics.Interval
