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

Round down to a finer format and then to a coarser one, and you get the same answer as rounding
down to the coarser format at once. The same holds for every directed mode. The proof is
order-theoretic and needs only that every value representable in the coarse format is
representable in the fine one, so it applies beyond the standard FIX, FLX, and FLT families.
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

/--
Downward rounding through a finer generic format, one whose exponent function is pointwise no
larger, equals direct downward rounding to the coarser format.
-/
theorem round_floor_double {fexpFine fexpCoarse : ℤ → ℤ}
    [ValidExp fexpFine] [ValidExp fexpCoarse] (hexp : ∀ e, fexpFine e ≤ fexpCoarse e)
    (x : ℝ) :
    round (β := β) (fexp := fexpCoarse) floorRound
        (round (β := β) (fexp := fexpFine) floorRound x) =
      round (β := β) (fexp := fexpCoarse) floorRound x :=
  roundDownPoint_unique (round_floor_point _)
    (roundDownPoint_double (fun _ h => generic_inclusion hexp h)
      (round_floor_point (fexp := fexpFine) x) (round_floor_point x))

/--
Upward rounding through a finer generic format, one whose exponent function is pointwise no
larger, equals direct upward rounding to the coarser format.
-/
theorem round_ceil_double {fexpFine fexpCoarse : ℤ → ℤ}
    [ValidExp fexpFine] [ValidExp fexpCoarse] (hexp : ∀ e, fexpFine e ≤ fexpCoarse e)
    (x : ℝ) :
    round (β := β) (fexp := fexpCoarse) ceilRound
        (round (β := β) (fexp := fexpFine) ceilRound x) =
      round (β := β) (fexp := fexpCoarse) ceilRound x :=
  roundUpPoint_unique (round_ceil_point _)
    (roundUpPoint_double (fun _ h => generic_inclusion hexp h)
      (round_ceil_point (fexp := fexpFine) x) (round_ceil_point x))

/-- Increasing FLX precision keeps every representable value representable. -/
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
  exact round_floor_double (fun e => by simp [flxExp]; linarith) x

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
  exact round_ceil_double (fun e => by simp [flxExp]; linarith) x

end FloatLib.Floats.Formats.Flocq
