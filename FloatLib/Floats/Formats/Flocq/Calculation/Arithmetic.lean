/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Calculation.Operations
public import FloatLib.Floats.Formats.Flocq.Calculation.Round

/-!
# Rounded Arithmetic on Mantissa/Exponent Values

Rounded arithmetic on `FloatRep` values uses exact representation operations where finite radix
expansions suffice. Addition, subtraction, and multiplication first use their exact `FloatRep`
operations. Division and square root need not have finite radix expansions, so they are formed
over the reals and rounded directly into the selected format.

These definitions model finite rounded arithmetic. IEEE exceptional behavior for zero divisors,
negative square roots, infinities, and NaNs belongs to `FloatLib.Floats.ExecFloat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq
namespace FloatRep

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Exact addition followed by rounding into the selected format. -/
noncomputable def addRounded (rnd : ℝ → ℤ) (f g : FloatRep β) : FloatRep β :=
  roundedFloat (β := β) (fexp := fexp) rnd (toReal (addExact f g))

/-- Exact subtraction followed by rounding into the selected format. -/
noncomputable def subRounded (rnd : ℝ → ℤ) (f g : FloatRep β) : FloatRep β :=
  roundedFloat (β := β) (fexp := fexp) rnd (toReal (subExact f g))

/-- Exact multiplication followed by rounding into the selected format. -/
noncomputable def mulRounded (rnd : ℝ → ℤ) (f g : FloatRep β) : FloatRep β :=
  roundedFloat (β := β) (fexp := fexp) rnd (toReal (mulExact f g))

/-- Exact real division followed by rounding into the selected format. -/
noncomputable def divRounded (rnd : ℝ → ℤ) (f g : FloatRep β) : FloatRep β :=
  roundedFloat (β := β) (fexp := fexp) rnd (toReal f / toReal g)

/-- Exact real square root followed by rounding into the selected format. -/
noncomputable def sqrtRounded (rnd : ℝ → ℤ) (f : FloatRep β) : FloatRep β :=
  roundedFloat (β := β) (fexp := fexp) rnd (Real.sqrt (toReal f))

/-- Rounded addition denotes real addition followed by the selected format rounding. -/
@[simp] theorem toReal_addRounded (rnd : ℝ → ℤ) (f g : FloatRep β) :
    toReal (addRounded (fexp := fexp) rnd f g) =
      round (β := β) (fexp := fexp) rnd (toReal f + toReal g) := by
  unfold addRounded roundedFloat
  rw [toReal_addExact]
  rfl

/-- Rounded subtraction denotes real subtraction followed by the selected format rounding. -/
@[simp] theorem toReal_subRounded (rnd : ℝ → ℤ) (f g : FloatRep β) :
    toReal (subRounded (fexp := fexp) rnd f g) =
      round (β := β) (fexp := fexp) rnd (toReal f - toReal g) := by
  unfold subRounded roundedFloat
  rw [toReal_subExact]
  rfl

/-- Rounded multiplication denotes real multiplication followed by the selected format rounding. -/
@[simp] theorem toReal_mulRounded (rnd : ℝ → ℤ) (f g : FloatRep β) :
    toReal (mulRounded (fexp := fexp) rnd f g) =
      round (β := β) (fexp := fexp) rnd (toReal f * toReal g) := by
  unfold mulRounded roundedFloat
  rw [toReal_mulExact]
  rfl

/-- Rounded division denotes real division followed by the selected format rounding. -/
@[simp] theorem toReal_divRounded (rnd : ℝ → ℤ) (f g : FloatRep β) :
    toReal (divRounded (fexp := fexp) rnd f g) =
      round (β := β) (fexp := fexp) rnd (toReal f / toReal g) := by
  rfl

/-- Rounded square root denotes real square root followed by the selected format rounding. -/
@[simp] theorem toReal_sqrtRounded (rnd : ℝ → ℤ) (f : FloatRep β) :
    toReal (sqrtRounded (fexp := fexp) rnd f) =
      round (β := β) (fexp := fexp) rnd (Real.sqrt (toReal f)) := by
  rfl

end FloatRep
end FloatLib.Floats.Formats.Flocq
