/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Generic
public import FloatLib.Floats.Formats.Flocq.Theory.Scalar.NF

/-!
# Grid Invariants for `NF`

You can build an `NF` from any raw real, which approximation proofs need, but the smart constructor
and the primitive arithmetic always round onto the declared format. This file proves the matching
`NF.IsRepresentable` closure properties. Keeping them here means the core scalar module doesn't
have to import the generic-format theory.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq.NF

open FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} {rnd : ℝ → ℤ}
variable [ValidExp fexp] [ValidRnd rnd]

/-- The smart constructor rounds its input onto the declared format grid. -/
theorem isRepresentable_ofReal (x : ℝ) :
    IsRepresentable (ofReal (β := β) (fexp := fexp) (rnd := rnd) x) := by
  exact generic_format_round rnd x

/-- Negation through the smart constructor remains on the declared format grid. -/
@[simp] theorem isRepresentable_neg (a : NF β fexp rnd) : IsRepresentable (-a) := by
  change IsRepresentable (ofReal (β := β) (fexp := fexp) (rnd := rnd) (-a.val))
  exact isRepresentable_ofReal _

/-- Addition through the smart constructor remains on the declared format grid. -/
@[simp] theorem isRepresentable_add (a b : NF β fexp rnd) : IsRepresentable (a + b) := by
  change IsRepresentable (ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val + b.val))
  exact isRepresentable_ofReal _

/-- Subtraction through the smart constructor remains on the declared format grid. -/
@[simp] theorem isRepresentable_sub (a b : NF β fexp rnd) : IsRepresentable (a - b) := by
  change IsRepresentable (ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val - b.val))
  exact isRepresentable_ofReal _

/-- Multiplication through the smart constructor remains on the declared format grid. -/
@[simp] theorem isRepresentable_mul (a b : NF β fexp rnd) : IsRepresentable (a * b) := by
  change IsRepresentable (ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val * b.val))
  exact isRepresentable_ofReal _

/-- Division through the smart constructor remains on the declared format grid. -/
@[simp] theorem isRepresentable_div (a b : NF β fexp rnd) : IsRepresentable (a / b) := by
  change IsRepresentable (ofReal (β := β) (fexp := fexp) (rnd := rnd) (a.val / b.val))
  exact isRepresentable_ofReal _

end FloatLib.Floats.Formats.Flocq.NF
