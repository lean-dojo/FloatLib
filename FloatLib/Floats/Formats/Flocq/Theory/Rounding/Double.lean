/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Order
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Formats

/-!
# Double Rounding

Directed rounding through a finer intermediate format gives the same answer as direct rounding to
the coarser format.  The order-theoretic proof only needs inclusion of representable values, so it
applies beyond the standard FIX, FLX, and FLT families.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/-- Downward rounding through a containing format collapses to direct downward rounding. -/
theorem roundDownPoint_double {fine coarse : ℝ → Prop} {x fineValue coarseValue : ℝ}
    (hsubset : ∀ z, coarse z → fine z)
    (hf : RoundDownPoint fine x fineValue)
    (hc : RoundDownPoint coarse x coarseValue) :
    RoundDownPoint coarse fineValue coarseValue := by
  have hcoarseFine : coarseValue ≤ fineValue :=
    hf.2.2 coarseValue (hsubset coarseValue hc.1) hc.2.1
  refine ⟨hc.1, hcoarseFine, ?_⟩
  intro z hz hzFine
  exact hc.2.2 z hz (hzFine.trans hf.2.1)

/-- Upward rounding through a containing format collapses to direct upward rounding. -/
theorem roundUpPoint_double {fine coarse : ℝ → Prop} {x fineValue coarseValue : ℝ}
    (hsubset : ∀ z, coarse z → fine z)
    (hf : RoundUpPoint fine x fineValue)
    (hc : RoundUpPoint coarse x coarseValue) :
    RoundUpPoint coarse fineValue coarseValue := by
  have hFineCoarse : fineValue ≤ coarseValue :=
    hf.2.2 coarseValue (hsubset coarseValue hc.1) hc.2.1
  refine ⟨hc.1, hFineCoarse, ?_⟩
  intro z hz hFineZ
  exact hc.2.2 z hz (hf.2.1.trans hFineZ)

/-- Increasing FLX precision preserves every exactly representable value. -/
theorem generic_format_FLX_mono {coarsePrec finePrec : ℤ}
    (hcoarse : 0 < coarsePrec) (hfine : 0 < finePrec) (hprec : coarsePrec ≤ finePrec)
    {x : ℝ}
    (hx : @genericFormat β (flxExp coarsePrec)
      (flxValidExp coarsePrec hcoarse) x) :
    @genericFormat β (flxExp finePrec) (flxValidExp finePrec hfine) x := by
  let : ValidExp (flxExp coarsePrec) := flxValidExp coarsePrec hcoarse
  let : ValidExp (flxExp finePrec) := flxValidExp finePrec hfine
  apply generic_inclusion (fexp₁ := flxExp coarsePrec) (fexp₂ := flxExp finePrec)
  · intro e
    simp [flxExp]
    linarith
  · exact hx

/-- Downward FLX double rounding equals direct rounding to the coarser precision. -/
theorem round_floor_double_FLX {coarsePrec finePrec : ℤ}
    (hcoarse : 0 < coarsePrec) (hfine : 0 < finePrec) (hprec : coarsePrec ≤ finePrec)
    (x : ℝ) :
    @round β (flxExp coarsePrec) (flxValidExp coarsePrec hcoarse)
        floorRound
        (@round β (flxExp finePrec) (flxValidExp finePrec hfine)
          floorRound x) =
      @round β (flxExp coarsePrec) (flxValidExp coarsePrec hcoarse)
        floorRound x := by
  let : ValidExp (flxExp coarsePrec) := flxValidExp coarsePrec hcoarse
  let : ValidExp (flxExp finePrec) := flxValidExp finePrec hfine
  let fineValue := @round β (flxExp finePrec) (flxValidExp finePrec hfine)
    floorRound x
  let coarseValue := @round β (flxExp coarsePrec) (flxValidExp coarsePrec hcoarse)
    floorRound x
  have hf : RoundDownPoint
      (@genericFormat β (flxExp finePrec) (flxValidExp finePrec hfine)) x fineValue :=
    round_floor_point x
  have hc : RoundDownPoint
      (@genericFormat β (flxExp coarsePrec) (flxValidExp coarsePrec hcoarse)) x coarseValue :=
    round_floor_point x
  have hdouble := roundDownPoint_double
    (fun _ h => generic_format_FLX_mono hcoarse hfine hprec h) hf hc
  exact roundDownPoint_unique
    (round_floor_point (β := β) (fexp := flxExp coarsePrec) fineValue) hdouble

/-- Upward FLX double rounding equals direct rounding to the coarser precision. -/
theorem round_ceil_double_FLX {coarsePrec finePrec : ℤ}
    (hcoarse : 0 < coarsePrec) (hfine : 0 < finePrec) (hprec : coarsePrec ≤ finePrec)
    (x : ℝ) :
    @round β (flxExp coarsePrec) (flxValidExp coarsePrec hcoarse)
        ceilRound
        (@round β (flxExp finePrec) (flxValidExp finePrec hfine)
          ceilRound x) =
      @round β (flxExp coarsePrec) (flxValidExp coarsePrec hcoarse)
        ceilRound x := by
  let : ValidExp (flxExp coarsePrec) := flxValidExp coarsePrec hcoarse
  let : ValidExp (flxExp finePrec) := flxValidExp finePrec hfine
  let fineValue := @round β (flxExp finePrec) (flxValidExp finePrec hfine)
    ceilRound x
  let coarseValue := @round β (flxExp coarsePrec) (flxValidExp coarsePrec hcoarse)
    ceilRound x
  have hf : RoundUpPoint
      (@genericFormat β (flxExp finePrec) (flxValidExp finePrec hfine)) x fineValue :=
    round_ceil_point x
  have hc : RoundUpPoint
      (@genericFormat β (flxExp coarsePrec) (flxValidExp coarsePrec hcoarse)) x coarseValue :=
    round_ceil_point x
  have hdouble := roundUpPoint_double
    (fun _ h => generic_format_FLX_mono hcoarse hfine hprec h) hf hc
  exact roundUpPoint_unique
    (round_ceil_point (β := β) (fexp := flxExp coarsePrec) fineValue) hdouble

end FloatLib.Floats.Formats.Flocq
