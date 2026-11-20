/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Saturation
public import FloatLib.Floats.Formats.DecimalInterchange.Scaling.Runtime

/-!
# Kernel path of decimal scaling and conversion

`Arithmetic.scale` (IEEE 754-2019 §5.3.3 `scaleB`), `Conversion.convertFormat` (§5.4.2) and
`Conversion.Integer.convertFromInt` (§5.4.1) each round one exact value of the form
`coefficient × 10 ^ exponent` with that exponent as the preferred quantum. That is the case
`KernelPath.project` computes on natural numbers, so their kernel forms are one call of it:

* `scale f mode x n` projects the coefficient of a finite `x` at its exponent plus `n`;
* `convertFormat target mode x` projects a finite `x` into the target format at its own
  exponent;
* `convertFromInt destination mode n` projects the magnitude of `n` at exponent zero.

`scale_eq`, `convertFormat_eq` and `convertFromInt_eq`, tagged `@[kernel_optimize]`, prove them
equal to the specified operations for every format, rounding direction and operand. The
specification never builds a power of ten beyond the range of the format. The kernel forms of
`scale` and `convertFormat` keep that property by leaving an exponent of magnitude above
`2 ^ 20` to the specification.

`Arithmetic.logB` (§5.3.3) of a nonzero finite datum is its quantum exponent plus its number of
digits less one. `logB` takes the number of digits from `decimalLength`, two comparisons with
powers of ten, where the specification computes `Nat.log 10`; `logB_eq`, tagged
`@[kernel_optimize]`, proves the two equal for every format and datum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

/-- Whether an exponent has a magnitude of at most `2 ^ 20`, the range in which the kernel forms
build powers of ten. -/
def moderate (exponent : Int) : Bool :=
  Nat.ble (Int.natAbs exponent) (Nat.pow 2 20)

/--
Kernel form of `Arithmetic.scale` (`scale_eq`): the coefficient of a finite datum is projected
at its exponent plus `n` when that exponent is moderate. Every other case is the specification.
-/
def scale (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q =>
      (fun exponent =>
        Bool.casesOn (motive := fun _ => Outcome) (moderate exponent)
          (Arithmetic.scale f mode x n) (project f mode s c exponent))
        (Int.add q n))
    (fun _ => Arithmetic.scale f mode x n) (fun _ _ _ => Arithmetic.scale f mode x n)

/--
Kernel form of `Conversion.convertFormat` (`convertFormat_eq`): a finite datum with a moderate
exponent is projected into the target format at its own exponent. Every other case is the
specification.
-/
def convertFormat (target : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q =>
      Bool.casesOn (motive := fun _ => Outcome) (moderate q)
        (Conversion.convertFormat target mode x) (project target mode s c q))
    (fun _ => Conversion.convertFormat target mode x)
    (fun _ _ _ => Conversion.convertFormat target mode x)

/--
Kernel form of `Conversion.Integer.convertFromInt` (`convertFromInt_eq`): the magnitude of the
integer is projected at exponent zero with its sign.
-/
def convertFromInt (destination : Format) (mode : RoundingMode) (source : Int) : Outcome :=
  Int.casesOn (motive := fun _ => Outcome) source
    (fun n => project destination mode false n 0)
    (fun n => project destination mode true (Nat.succ n) 0)

/--
Kernel form of `Arithmetic.logB` (`logB_eq`): the quantum exponent of a nonzero finite datum
plus its number of decimal digits less one. A zero, an infinity and a NaN are left to the
specification.
-/
def logB (f : Format) (x : Datum) : Arithmetic.DecimalExponentOutcome :=
  Datum.casesOn (motive := fun _ => Arithmetic.DecimalExponentOutcome) x
    (fun _ c q =>
      Bool.casesOn (motive := fun _ => Arithmetic.DecimalExponentOutcome) (Nat.beq c 0)
        { value := Int.add q (Int.ofNat (Nat.pred (decimalLength c))) } (Arithmetic.logB f x))
    (fun _ => Arithmetic.logB f x) (fun _ _ _ => Arithmetic.logB f x)

/-- Decimal `logB` is its kernel form, for every format and datum. -/
@[kernel_optimize] theorem logB_eq (f : Format) (x : Datum) :
    Arithmetic.logB f x = logB f x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  rcases c with _ | c
  · rfl
  · change ({ value := q + (Nat.log 10 (c + 1) : Int) } : Arithmetic.DecimalExponentOutcome) =
      { value := Int.add q (Int.ofNat (Nat.pred (decimalLength (c + 1)))) }
    rw [decimalLength_eq (Nat.succ_ne_zero c)]
    rfl

/-- Decimal `scaleB` is its kernel form, for every format, rounding direction, datum and scale. -/
@[kernel_optimize] theorem scale_eq (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    Arithmetic.scale f mode x n = scale f mode x n := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  change _ = Bool.casesOn (motive := fun _ => Outcome) (moderate (q + n))
    (Arithmetic.scale f mode (.finite s c q) n) (project f mode s c (q + n))
  cases moderate (q + n)
  · rfl
  · change projectScaled f mode s c (q + n) (q + n) = project f mode s c (q + n)
    rw [projectScaled_eq, project_eq]

/--
The conversion between decimal formats is its kernel form, for every target format, rounding
direction and datum.
-/
@[kernel_optimize] theorem convertFormat_eq (target : Format) (mode : RoundingMode) (x : Datum) :
    Conversion.convertFormat target mode x = convertFormat target mode x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  change _ = Bool.casesOn (motive := fun _ => Outcome) (moderate q)
    (Conversion.convertFormat target mode (.finite s c q)) (project target mode s c q)
  cases moderate q
  · rfl
  · exact project_finiteValue target mode s s c q (fun _ => rfl)

/--
The conversion of an integer to a decimal format is its kernel form, for every destination
format, rounding direction and integer.
-/
@[kernel_optimize] theorem convertFromInt_eq (destination : Format) (mode : RoundingMode)
    (source : Int) :
    Conversion.Integer.convertFromInt destination mode source =
      convertFromInt destination mode source := by
  rcases source with n | n
  · change DecimalInterchange.project destination mode ((Int.ofNat n : Int) : ℚ) 0 =
      project destination mode false n 0
    rw [← project_finiteValue destination mode false false n 0 (fun _ => rfl)]
    congr 1
    simp [Datum.finiteValue]
  · change DecimalInterchange.project destination mode ((Int.negSucc n : Int) : ℚ) 0 =
      project destination mode true (n + 1) 0
    rw [← project_finiteValue destination mode true false (n + 1) 0
      (fun h => absurd h (Nat.succ_ne_zero n))]
    congr 1
    simp [Datum.finiteValue, Int.negSucc_eq]

/-! ## Kernel shapes -/

kernel_shape moderate
kernel_shape scale
kernel_shape convertFormat
kernel_shape convertFromInt
kernel_shape logB

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
