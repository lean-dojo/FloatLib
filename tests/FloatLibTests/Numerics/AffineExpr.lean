/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Affine.ExprProof
public import FloatLib.Numerics.Enclosure.Expression.Backends

meta import FloatLib.Numerics.Enclosure.Affine.Expr

/-!
# Affine ranges of interval expressions

Each example pins the exact affine range of a polynomial on a box, decided by Lean's kernel. The
first one shows what affine arithmetic gains over interval evaluation on `x * (1 - x)`. The others
cover powers, several variables, negation, constants and fused multiply-adds, then expressions
that have no affine range and two ranges computed by compiled code, and last the inclusion theorem
and the noise of a point.
-/

@[expose] public section

namespace FloatLibTests.Numerics.AffineExpr

open FloatLib.Numerics FloatLib.Numerics.Interval FloatLib.Numerics.Enclosure.Affine

/-- `x * (1 - x)`, whose range on `[0, 1]` is `[0, 1 / 4]`. -/
def parabola : Expr := .binary .mul (.var 0) (.binary .sub (.const 1) (.var 0))

/-- Interval evaluation of `x * (1 - x)` on `[0, 1]` gives `[0, 1]`, and the affine range is the
true range `[0, 1 / 4]`. -/
example : parabola.eval? (Backend.rational {}) (fun _ => some ⟨0, 1⟩) = some ⟨0, 1⟩ ∧
    Expr.affineRange? parabola [⟨0, 1⟩] = some ⟨0, 1 / 4⟩ := by
  decide +kernel

/-- A product and a power of `1 + ε / 2`: the variable on `[1 / 2, 3 / 2]`. -/
example : Expr.affineRange? (.binary .mul (.var 0) (.var 0)) [⟨1 / 2, 3 / 2⟩] = some ⟨0, 9 / 4⟩ ∧
    Expr.affineRange? (.unary (.pow 2) (.var 0)) [⟨1 / 2, 3 / 2⟩] = some ⟨0, 9 / 4⟩ := by
  decide +kernel

/-- Odd and even powers, by binary exponentiation, and a difference. -/
example :
    Expr.affineRange? (.binary .sub (.unary (.pow 3) (.var 0)) (.binary .mul (.const 2) (.var 0)))
      [⟨-1, 2⟩] = some ⟨-5, 31 / 4⟩ ∧
    Expr.affineRange? (.unary (.pow 4) (.var 0)) [⟨-1, 2⟩] = some ⟨-101 / 16, 16⟩ ∧
    Expr.affineRange? (.unary (.pow 7) (.var 0)) [⟨-1, 2⟩] = some ⟨-4087 / 64, 128⟩ ∧
    Expr.affineRange? (.unary (.pow 5) (.binary .add (.var 0) (.const (1 / 2)))) [⟨-1, 2⟩] =
      some ⟨-29, 3125 / 32⟩ ∧
    Expr.affineRange? (.unary (.pow 0) (.var 0)) [⟨-1, 2⟩] = some ⟨1, 1⟩ := by
  decide +kernel

/-- Several variables, a negation, a coordinate that is a point, and constants. -/
example :
    Expr.affineRange?
      (.binary .add (.binary .sub (.binary .mul (.var 0) (.var 1)) (.var 0))
        (.unary (.pow 2) (.var 1))) [⟨0, 1⟩, ⟨1, 2⟩] = some ⟨1 / 4, 5⟩ ∧
    Expr.affineRange?
      (.binary .mul (.unary .neg (.binary .sub (.var 0) (.var 1))) (.binary .add (.var 0) (.var 2)))
      [⟨-1, 1⟩, ⟨2, 3⟩, ⟨1 / 3, 1 / 3⟩] = some ⟨-3, 11 / 3⟩ ∧
    Expr.affineRange? (.binary .add (.const (-3 / 4)) (.const (-2))) [⟨-1, 2⟩] =
      some ⟨-11 / 4, -11 / 4⟩ := by
  decide +kernel

/-- A fused multiply-add is a product and a sum. -/
example :
    Expr.affineRange? (.ternary .fma (.var 0) (.var 1) (.var 2)) [⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 1⟩] =
      some ⟨-3 / 2, 3⟩ ∧
    Expr.affineRange? (.ternary .fma (.var 0) (.var 1) (.var 2)) [⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 1⟩] =
      Expr.affineRange? (.binary .add (.binary .mul (.var 0) (.var 1)) (.var 2))
        [⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 1⟩] := by
  decide +kernel

/-- A division, an operation outside the polynomial fragment, a registered call and a variable
that the box does not bound have no affine range. -/
example : Expr.affineRange? (.binary .div (.var 0) (.const 2)) [⟨-1, 2⟩] = none ∧
    Expr.affineRange? (.unary .exp (.var 0)) [⟨-1, 2⟩] = none ∧
    Expr.affineRange? (.call 0 []) [⟨-1, 2⟩] = none ∧
    Expr.affineRange? (.binary .add (.var 0) (.var 1)) [⟨-1, 2⟩] = none := by
  decide +kernel

/-- The compiler gives the same ranges: this one is computed by compiled code, not by the
kernel. -/
def compiledPower : Option (Interval ℚ) :=
  Expr.affineRange? (.unary (.pow 7) (.var 0)) [⟨-1, 2⟩]

#guard compiledPower == some ⟨-4087 / 64, 128⟩
#guard Expr.affineRange? parabola [⟨0, 1⟩] == some ⟨0, 1 / 4⟩

/-- The inclusion theorem on the range of `x * (1 - x)`: the bound `1 / 4` on `[0, 1]`. -/
example (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x * (1 - x) ≤ 1 / 4 := by
  have hbox : Box.ContainsReal [⟨0, 1⟩] (fun _ => x) :=
    Box.containsReal_cons ⟨by simpa using h0, by simpa using h1⟩ (Box.containsReal_nil _)
  have hrange : Expr.affineRange? parabola [⟨0, 1⟩] = some ⟨0, 1 / 4⟩ := by decide +kernel
  have h := ((containsReal_some_iff _ _).1
    (Expr.containsReal_affineRange? hrange hbox (fun _ _ => 0))).2
  simpa [parabola, Expr.eval, UnaryOp.eval, BinaryOp.eval] using h

/-- The noise of a point of a box: `3 / 4` on `[0, 1]` has the noise `1 / 2`, and recentering
gives the point back. -/
example : unitNoise [⟨0, 1⟩] (fun _ => 3 / 4) 0 = 1 / 2 ∧
    recenter [⟨0, 1⟩] (unitNoise [⟨0, 1⟩] (fun _ => 3 / 4)) 0 = 3 / 4 := by
  have hbox : Box.ContainsReal [⟨0, 1⟩] (fun _ => (3 / 4 : ℝ)) :=
    Box.containsReal_cons ⟨by norm_num, by norm_num⟩ (Box.containsReal_nil _)
  exact ⟨by norm_num [unitNoise], recenter_unitNoise_eq hbox rfl⟩

example : unitNoise [⟨2, 2⟩] (fun _ => 2) 0 = 0 ∧
    recenter [⟨2, 2⟩] (unitNoise [⟨2, 2⟩] (fun _ => 2)) 0 = 2 := by
  norm_num [unitNoise, recenter]

end FloatLibTests.Numerics.AffineExpr
