/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Integral.Runtime
public import FloatLib.Numerics.Representations.FixedInt.Semantics.Basic

/-!
# Kernel path of rounding a decimal datum at a quantum

`quantize`, the integral roundings and the conversions to an integer.

Rounding the magnitude `c × 10 ^ q` at the quantum `r` drops the digits of `c` below `r`.
`roundAtQuantum` computes the rounded coefficient and the dropped digits on natural numbers: the
coefficient is scaled by the gap of the two exponents when `r` is the smaller one, and divided
with remainder by a power of ten when it is the larger one, and the remainder decides the
increment (`KernelPath.increment`). `roundAtQuantum_eq` proves that the coefficient is
`RoundingMode.roundAt`, and `roundAt_exact_iff` that the rounding is exact exactly when no
nonzero digit is dropped.

`convertToInteger` is the kernel form of `Conversion.Integer.convertToInteger`, the ten
conversions to an integer of IEEE 754-2019 §5.4.1 in one definition: a finite datum is rounded
at the quantum `1`, and the range of the integer format is tested on the sign and the magnitude
of the rounded integer (`inRange`, equal to the range test of the specification by
`inRange_eq`). `convertToInteger_eq`, tagged `@[kernel_optimize]`, proves it equal to the
specification for every integer format, rounding direction and datum.

`quantizeAt` rounds a magnitude at a quantum exponent into a format, with the range tests of
`Arithmetic.quantizeMagnitude` as comparisons of natural numbers (`fits`, `fits_eq`), and
`quantizeAt_eq` proves it equal to that specification. Two operations are built on it:

* `quantize` is the kernel form of `Arithmetic.quantize` (§5.3.2): a finite datum is rounded at
  the quantum of the second operand. `quantize_eq`, tagged `@[kernel_optimize]`, proves it equal
  to the specification for every format, rounding direction and pair of data.
* `roundToIntegral` is the kernel form of `Arithmetic.roundToIntegralExact` and of
  `Arithmetic.roundToIntegral` (§5.3.1), with and without the `inexact` signal: a finite datum is
  rounded at the quantum exponent `max q 0`. `roundToIntegralExact_eq` and `roundToIntegral_eq`,
  tagged `@[kernel_optimize]`, prove the two equal to it for every format, rounding direction
  and datum; the five members `roundToIntegralTiesToEven` to `roundToIntegralTowardNegative`
  are `Arithmetic.roundToIntegral` at one direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Representations

/--
The magnitude `c × 10 ^ q` rounded at the quantum `r` in `mode`, for a value of sign `negative`:
`k` receives the rounded coefficient and the digits that were dropped (`roundAtQuantum_eq`).
-/
def roundAtQuantum {α : Type} (mode : RoundingMode) (negative : Bool) (c : Nat) (q r : Int)
    (k : Nat → Nat → α) : α :=
  gaps q r fun above below =>
    (fun scaled denominator =>
      (fun lower remainder =>
        k (Nat.add lower (increment mode negative lower remainder denominator)) remainder)
        (Nat.div scaled denominator) (Nat.mod scaled denominator))
      (Nat.mul c (Nat.pow 10 above)) (Nat.pow 10 below)

/-- The digits of `c × 10 ^ q` below the quantum `r`, as a natural number. -/
def droppedAt (c : Nat) (q r : Int) : Nat :=
  c * 10 ^ (q - r).toNat % 10 ^ (r - q).toNat

/-- The coefficient of `c × 10 ^ q` rounded at the quantum `r`, from quotient and remainder. -/
theorem roundAt_eq_div_add (mode : RoundingMode) (negative : Bool) (c : Nat) (q r : Int) :
    mode.roundAt negative ((c : ℚ) * (10 : ℚ) ^ q) r =
      c * 10 ^ (q - r).toNat / 10 ^ (r - q).toNat +
        increment mode negative (c * 10 ^ (q - r).toNat / 10 ^ (r - q).toNat) (droppedAt c q r)
          (10 ^ (r - q).toNat) := by
  have hfine := Arithmetic.finer_grid_value c q (q - ((q - r).toNat : Int)) (by omega)
  have hexp : (q - (q - ((q - r).toNat : Int))).toNat = (q - r).toNat := by omega
  rw [hexp] at hfine
  rw [← hfine, roundAt_scaled_of_lt mode negative (c * 10 ^ (q - r).toNat)
    (k := (r - q).toNat) (by omega)]
  rfl

/-- `roundAtQuantum` passes on the specified rounded coefficient and the dropped digits. -/
theorem roundAtQuantum_eq {α : Type} (mode : RoundingMode) (negative : Bool) (c : Nat)
    (q r : Int) (k : Nat → Nat → α) :
    roundAtQuantum mode negative c q r k =
      k (mode.roundAt negative ((c : ℚ) * (10 : ℚ) ^ q) r) (droppedAt c q r) := by
  rw [roundAtQuantum, gaps_eq, roundAt_eq_div_add]
  rfl

/-- The rounding at a quantum is exact exactly when no nonzero digit is dropped. -/
theorem roundAt_exact_iff (mode : RoundingMode) (negative : Bool) (c : Nat) (q r : Int) :
    ((mode.roundAt negative ((c : ℚ) * (10 : ℚ) ^ q) r : Nat) : ℚ) * (10 : ℚ) ^ r =
        (c : ℚ) * (10 : ℚ) ^ q ↔ droppedAt c q r = 0 := by
  rw [roundAt_eq_div_add]
  unfold droppedAt
  generalize hscaled : c * 10 ^ (q - r).toNat = scaled
  generalize hden : 10 ^ (r - q).toNat = den
  have hdenpos : 0 < den := by
    rw [← hden]
    positivity
  have hrem : scaled % den < den := Nat.mod_lt _ hdenpos
  have hinc := increment_le_one mode negative (scaled / den) hrem
  have hzero : scaled % den = 0 →
      increment mode negative (scaled / den) (scaled % den) den = 0 := fun h => by
    rw [h]
    exact increment_zero mode negative (scaled / den) hdenpos
  have hsplit := Nat.div_add_mod scaled den
  generalize increment mode negative (scaled / den) (scaled % den) den = inc at hinc hzero
  -- Both sides at the finer of the two exponents.
  have hfine := Arithmetic.finer_grid_value c q (q - ((q - r).toNat : Int)) (by omega)
  have hexp : (q - (q - ((q - r).toNat : Int))).toNat = (q - r).toNat := by omega
  rw [hexp, hscaled] at hfine
  have hquantum := Arithmetic.finer_grid_value 1 r (q - ((q - r).toNat : Int)) (by omega)
  have hexp' : (r - (q - ((q - r).toNat : Int))).toNat = (r - q).toNat := by omega
  rw [hexp', Nat.one_mul, hden, Nat.cast_one, one_mul] at hquantum
  have hpow : (10 : ℚ) ^ (q - ((q - r).toNat : Int)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [← hfine, ← hquantum, ← mul_assoc, mul_left_inj' hpow]
  have hcast : (((scaled / den + inc : Nat) : ℚ) * (den : ℚ) = (scaled : ℚ)) ↔
      (scaled / den + inc) * den = scaled := by
    norm_cast
  rw [hcast]
  constructor
  · intro h
    have hmul : inc * den = scaled % den := by
      have hcomm : den * (scaled / den) = scaled / den * den := Nat.mul_comm _ _
      rw [Nat.add_mul] at h
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hinc with h0 | h1
    · rw [h0, Nat.zero_mul] at hmul
      exact hmul.symm
    · rw [h1, Nat.one_mul] at hmul
      omega
  · intro h
    rw [hzero h, Nat.add_zero]
    have hcomm : den * (scaled / den) = scaled / den * den := Nat.mul_comm _ _
    omega

/--
A selection by cases on a decided proposition is the conditional on that proposition: the form
in which a kernel definition states a range test of the specification.
-/
theorem casesOn_decide {α : Type} (p : Prop) [Decidable p] (otherwise value : α) :
    Bool.casesOn (motive := fun _ => α) (decide p) otherwise value =
      if p then value else otherwise := by
  by_cases h : p <;> simp [h]

/-! ## Conversion to an integer (§5.4.1) -/

/-- The integer of sign `negative` and magnitude `magnitude`. -/
def signedInteger (negative : Bool) (magnitude : Nat) : Int :=
  Bool.casesOn (motive := fun _ => Int) negative (magnitude : Int) (-(magnitude : Int))

/--
Whether the integer of sign `negative` and magnitude `magnitude` lies in the range of the
integer format `destination`, by one comparison of natural numbers (`inRange_eq`): below
`2 ^ (width - 1)` or `2 ^ width` when it is not negative, and at most `2 ^ width - 2 ^ (width - 1)`
or zero when it is.
-/
def inRange (destination : Conversion.Integer.IntegerFormat) (negative : Bool)
    (magnitude : Nat) : Bool :=
  IntegerFormat.casesOn (motive := fun _ => Bool) destination
    (fun width =>
      Bool.casesOn (motive := fun _ => Bool) negative
        (Nat.ble (Nat.succ magnitude) (Nat.pow 2 (Nat.pred width)))
        (Nat.ble magnitude (Nat.sub (Nat.pow 2 width) (Nat.pow 2 (Nat.pred width)))))
    (fun width =>
      Bool.casesOn (motive := fun _ => Bool) negative
        (Nat.ble (Nat.succ magnitude) (Nat.pow 2 width)) (Nat.beq magnitude 0))

/--
`inRange` decides the range of an integer format, signed or unsigned and of every width, at the
integer of a sign and a magnitude.
-/
theorem inRange_eq (destination : Conversion.Integer.IntegerFormat) (negative : Bool)
    (magnitude : Nat) :
    inRange destination negative magnitude =
      decide (destination.range.Contains (signedInteger negative magnitude)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  rcases destination with width | width
  · have hcast : (2 : Int) ^ (width - 1) = ((2 ^ (width - 1) : Nat) : Int) := by norm_cast
    have hmax : FixedInt.maxValue width = ((2 ^ (width - 1) : Nat) : Int) - 1 := by
      rw [FixedInt.maxValue_eq, hcast]
    have hmin : FixedInt.minValue width = -((2 ^ width - 2 ^ (width - 1) : Nat) : Int) := by
      rcases Nat.eq_zero_or_pos width with rfl | hwidth
      · rfl
      · have hdouble : 2 ^ width - 2 ^ (width - 1) = 2 ^ (width - 1) := by
          have hsucc : 2 ^ width = 2 * 2 ^ (width - 1) := by
            rw [← Nat.pow_succ']
            congr 1
            omega
          omega
        rw [FixedInt.minValue_eq hwidth, hcast, hdouble]
    have hpos : 0 < 2 ^ (width - 1) := Nat.pow_pos (by decide)
    cases negative
    · change (Nat.ble (magnitude + 1) (2 ^ (width - 1)) = true) ↔
        FixedInt.minValue width ≤ (magnitude : Int) ∧ (magnitude : Int) ≤ FixedInt.maxValue width
      rw [Nat.ble_eq, hmin, hmax]
      omega
    · change (Nat.ble magnitude (2 ^ width - 2 ^ (width - 1)) = true) ↔
        FixedInt.minValue width ≤ -(magnitude : Int) ∧
          -(magnitude : Int) ≤ FixedInt.maxValue width
      rw [Nat.ble_eq, hmin, hmax]
      omega
  · have hcast : (2 : Int) ^ width = ((2 ^ width : Nat) : Int) := by norm_cast
    have hpos : 0 < 2 ^ width := Nat.pow_pos (by decide)
    cases negative
    · change (Nat.ble (magnitude + 1) (2 ^ width) = true) ↔
        (0 : Int) ≤ (magnitude : Int) ∧ (magnitude : Int) ≤ (2 : Int) ^ width - 1
      rw [Nat.ble_eq, hcast]
      omega
    · change (Nat.beq magnitude 0 = true) ↔
        (0 : Int) ≤ -(magnitude : Int) ∧ -(magnitude : Int) ≤ (2 : Int) ^ width - 1
      rw [Nat.beq_eq, hcast]
      omega

/--
Kernel form of `Conversion.Integer.convertToInteger` (`convertToInteger_eq`): a finite datum is
rounded at the quantum `1` on natural numbers, the rounded integer is tested against the range
of the destination by `inRange`, and `inexact` is raised, when asked for, exactly when digits
were dropped. An infinity and a NaN are invalid.
-/
def convertToInteger (destination : Conversion.Integer.IntegerFormat) (mode : RoundingMode)
    (signalInexact : Bool) (source : Datum) : Conversion.Integer.IntegerOutcome :=
  Datum.casesOn (motive := fun _ => Conversion.Integer.IntegerOutcome) source
    (fun s c q =>
      roundAtQuantum mode s c q 0 fun magnitude dropped =>
        Bool.casesOn (motive := fun _ => Conversion.Integer.IntegerOutcome)
          (inRange destination s magnitude) Conversion.Integer.invalidOutcome
          { value := signedInteger s magnitude
            status := { inexact := signalInexact && !Nat.beq dropped 0 } })
    (fun _ => Conversion.Integer.invalidOutcome)
    (fun _ _ _ => Conversion.Integer.invalidOutcome)

/-- The integer rounding of a finite decimal value is the signed rounding at the quantum `1`. -/
theorem roundInteger_finiteValue (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) :
    Conversion.Integer.roundInteger mode (Datum.finiteValue s c q) =
      signedInteger s (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) 0) := by
  have hround : ∀ b : Bool, mode.roundAt b ((c : ℚ) * (10 : ℚ) ^ q) 0 =
      mode.roundMagnitude b ((c : ℚ) * (10 : ℚ) ^ q) := fun b => by
    simp [RoundingMode.roundAt]
  have hzero : ∀ b : Bool, mode.roundMagnitude b (0 : ℚ) = 0 := fun b => by
    simpa using RoundingMode.roundMagnitude_natCast mode b 0
  unfold Conversion.Integer.roundInteger
  simp only [Datum.finiteValue_abs, hround]
  by_cases hc : c = 0
  · subst hc
    cases s <;> simp [Datum.finiteValue, signedInteger, hzero]
  · have hpos : (0 : ℚ) < (c : ℚ) * (10 : ℚ) ^ q :=
      mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hc)) (zpow_pos (by norm_num) _)
    cases s
    · have hsign : ¬ Datum.finiteValue false c q < 0 := by
        simpa [Datum.finiteValue] using hpos.le
      simp [hsign, signedInteger]
    · have hsign : Datum.finiteValue true c q < 0 := by
        simpa [Datum.finiteValue] using hpos
      simp [hsign, signedInteger]

/-- The rounded integer differs from the value exactly when nonzero digits were dropped. -/
theorem signedInteger_ne_finiteValue_iff (mode : RoundingMode) (s : Bool) (c : Nat) (q : Int) :
    ((signedInteger s (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) 0) : Int) : ℚ) ≠
        Datum.finiteValue s c q ↔ droppedAt c q 0 ≠ 0 := by
  rw [Ne, Ne, ← roundAt_exact_iff mode s c q 0, zpow_zero, mul_one]
  cases s <;> simp [signedInteger, Datum.finiteValue]

/--
The conversion of a decimal datum to an integer is its kernel form, for every integer format,
rounding direction and datum, with and without the `inexact` signal.
-/
@[kernel_optimize] theorem convertToInteger_eq (destination : Conversion.Integer.IntegerFormat)
    (mode : RoundingMode) (signalInexact : Bool) (source : Datum) :
    Conversion.Integer.convertToInteger destination mode signalInexact source =
      convertToInteger destination mode signalInexact source := by
  rcases source with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  have hkernel : convertToInteger destination mode signalInexact (.finite s c q) =
      roundAtQuantum mode s c q 0 fun magnitude dropped =>
        Bool.casesOn (motive := fun _ => Conversion.Integer.IntegerOutcome)
          (inRange destination s magnitude) Conversion.Integer.invalidOutcome
          { value := signedInteger s magnitude
            status := { inexact := signalInexact && !Nat.beq dropped 0 } } := rfl
  rw [hkernel, roundAtQuantum_eq, inRange_eq, casesOn_decide]
  unfold Conversion.Integer.convertToInteger
  rw [Datum.toRat?_eq]
  simp only [IntegerRange.round?]
  rw [← Datum.finiteValue, roundInteger_finiteValue]
  have hexact := signedInteger_ne_finiteValue_iff mode s c q
  by_cases hrange : destination.range.Contains
      (signedInteger s (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) 0))
  · simp only [hrange, ↓reduceIte]
    by_cases hdropped : droppedAt c q 0 = 0
    · have hne : ¬ ((signedInteger s (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) 0) : Int) : ℚ) ≠
          Datum.finiteValue s c q := fun h => hexact.1 h hdropped
      simp [hne, hdropped]
    · have hne := hexact.2 hdropped
      have hbeq : Nat.beq (droppedAt c q 0) 0 = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]
        exact hdropped
      simp [hne, hbeq]
  · simp only [hrange, ↓reduceIte]

/-! ## Rounding at a quantum into a format -/

/-- The quotient of the coefficient bound by ten is the payload bound. -/
theorem coefficientBound_div_ten (f : Format) : f.coefficientBound / 10 = f.payloadBound := by
  rw [Format.coefficientBound]
  exact Nat.mul_div_cancel_left _ (by decide)

/--
Whether a coefficient at the quantum exponent `r` is a finite datum of the format `f`, by
comparisons of natural numbers (`fits_eq`): the biased exponent is not negative and below the
exponent bound, and the coefficient is below the coefficient bound.
-/
def fits (f : Format) (coefficient : Nat) (r : Int) : Bool :=
  offsets r f.bias fun biased below =>
    Bool.and (Nat.beq below 0)
      (Bool.and (Nat.ble (Nat.succ biased) (Nat.mul 3 (Nat.pow 2 f.exponentBits)))
        (Nat.ble (Nat.succ coefficient) (Nat.pow 10 (Nat.succ (Nat.mul 3 f.declets)))))

/-- `fits` decides the quantum range and the precision of a format, for every format. -/
theorem fits_eq (f : Format) (coefficient : Nat) (r : Int) :
    fits f coefficient r =
      decide (f.minQuantum ≤ r ∧ r ≤ f.maxQuantum ∧ coefficient < f.coefficientBound) := by
  have hbound : 3 * 2 ^ f.exponentBits = f.exponentBound := rfl
  have hfull : 10 ^ (3 * f.declets + 1) = f.coefficientBound := (Format.coefficientBound_eq f).symm
  rw [fits, offsets_eq, Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.succ_eq_add_one, Nat.mul_eq,
    Nat.pow_eq, hbound, hfull]
  unfold Format.minQuantum Format.maxQuantum
  omega

/--
The magnitude `c × 10 ^ q` of sign `s` rounded at the quantum exponent `r` into the format `f`
(`quantizeAt_eq`): invalid when `r` is outside the format or the rounded coefficient exceeds the
precision (`fits`), and otherwise the rounded datum, with `inexact`, when `signalInexact` asks
for it, exactly when digits were dropped.
-/
def quantizeAt (f : Format) (mode : RoundingMode) (signalInexact s : Bool) (c : Nat)
    (q r : Int) : Outcome :=
  roundAtQuantum mode s c q r fun coefficient dropped =>
    Bool.casesOn (motive := fun _ => Outcome) (fits f coefficient r) Arithmetic.invalidResult
      { value := .finite s coefficient r
        status := { inexact := signalInexact && !Nat.beq dropped 0 } }

/--
`quantizeAt` with the `inexact` signal is `Arithmetic.quantizeMagnitude`, the specified rounding
of a magnitude at a quantum exponent: the same datum and the same flags, for every format,
rounding direction, coefficient and pair of exponents.
-/
theorem quantizeAt_eq (f : Format) (mode : RoundingMode) (s : Bool) (c : Nat) (q r : Int) :
    Arithmetic.quantizeMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ q) r =
      quantizeAt f mode true s c q r := by
  rw [quantizeAt, roundAtQuantum_eq, fits_eq, casesOn_decide]
  unfold Arithmetic.quantizeMagnitude
  have hexact := roundAt_exact_iff mode s c q r
  by_cases hdropped : droppedAt c q r = 0
  · have heq := hexact.2 hdropped
    simp [heq, hdropped]
  · have hne : ¬ ((mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) r : Nat) : ℚ) * (10 : ℚ) ^ r =
        (c : ℚ) * (10 : ℚ) ^ q := fun h => hdropped (hexact.1 h)
    have hbeq : Nat.beq (droppedAt c q r) 0 = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq]
      exact hdropped
    simp [hne, hbeq]

/-- Without the `inexact` signal, `quantizeAt` is its outcome with that flag cleared. -/
theorem quantizeAt_quiet (f : Format) (mode : RoundingMode) (s : Bool) (c : Nat) (q r : Int) :
    quantizeAt f mode false s c q r =
      { quantizeAt f mode true s c q r with
        status := { (quantizeAt f mode true s c q r).status with inexact := false } } := by
  rw [quantizeAt, quantizeAt, roundAtQuantum_eq, roundAtQuantum_eq]
  cases fits f (mode.roundAt s ((c : ℚ) * (10 : ℚ) ^ q) r) r <;> rfl

/--
The outcome of a coefficient `rounded` of sign `negative` at the quantum `shift` above the least
quantum (`deliverRounded_eq`): a coefficient that reached ten to the precision is its leading
digit one quantum higher, a quantum beyond the format overflows, an inexact result is delivered
as it is with its flags, and an exact result as the member of its cohort nearest to the
preferred exponent.
-/
def deliverRounded (f : Format) (mode : RoundingMode) (negative : Bool) (rounded shift : Nat)
    (inexact tiny : Bool) (preferred : Int) : Outcome :=
  (fun full =>
    (fun carry =>
      (fun coefficient place =>
        Bool.casesOn (motive := fun _ => Outcome)
          (Nat.ble (Nat.mul 3 (Nat.pow 2 f.exponentBits)) place)
          { value := Bool.casesOn (motive := fun _ => Datum) inexact
              (preferredCohort f negative coefficient (quantumAt place f.bias) preferred)
              (.finite negative coefficient (quantumAt place f.bias))
            status := { inexact := inexact, underflow := Bool.and tiny inexact } }
          (overflow f mode negative))
        (Bool.casesOn (motive := fun _ => Nat) carry rounded (Nat.div full 10))
        (Bool.casesOn (motive := fun _ => Nat) carry shift (Nat.succ shift)))
      (Nat.beq rounded full))
    (Nat.pow 10 (Nat.succ (Nat.mul 3 f.declets)))

/--
`deliverRounded` is the delivery that the specifications of the projection and of the square
root share: from the pair that the carry of the rounded coefficient gives, the overflow test,
the datum and the flags, for every format, rounding direction and sign.
-/
theorem deliverRounded_eq (f : Format) (mode : RoundingMode) (negative : Bool)
    (rounded shift : Nat) (inexact tiny : Bool) (preferred : Int) (pair : Nat × Int)
    (hpair : pair =
      if rounded = f.coefficientBound then (f.payloadBound, (shift : Int) - f.bias + 1)
      else (rounded, (shift : Int) - f.bias)) :
    deliverRounded f mode negative rounded shift inexact tiny preferred =
      if f.maxQuantum < pair.2 then
        { value := if mode.overflowToInfinity negative then .infinity negative
            else f.maxFinite negative
          status := { overflow := true, inexact := true } }
      else
        { value := if inexact then .finite negative pair.1 pair.2
            else preferredCohort f negative pair.1 pair.2 preferred
          status := { inexact := inexact, underflow := tiny && inexact } } := by
  subst hpair
  have hfull : 10 ^ (3 * f.declets + 1) = f.coefficientBound := (Format.coefficientBound_eq f).symm
  have hbound : 3 * 2 ^ f.exponentBits = f.exponentBound := rfl
  have hdiv : ∀ m n : Nat, Nat.div m n = m / n := fun _ _ => rfl
  have hsucc : (shift : Int) - f.bias + 1 = ((shift + 1 : Nat) : Int) - f.bias := by
    push_cast
    ring
  have hover : ∀ place : Nat,
      f.exponentBound ≤ place ↔ f.maxQuantum < (place : Int) - f.bias := fun place => by
    unfold Format.maxQuantum
    omega
  unfold deliverRounded
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one, hdiv, hfull, hbound,
    coefficientBound_div_ten, natBeq_eq, natBle_eq f.exponentBound, quantumAt_eq, hsucc]
  by_cases hcarry : rounded = f.coefficientBound
  · rw [decide_eq_true hcarry, ite_eq_left hcarry]
    dsimp only
    by_cases hov : f.exponentBound ≤ shift + 1
    · rw [decide_eq_true hov, ite_eq_left ((hover _).1 hov)]
      rfl
    · rw [decide_eq_false hov, ite_eq_right (fun h => hov ((hover _).2 h))]
      cases inexact <;> rfl
  · rw [decide_eq_false hcarry, ite_eq_right hcarry]
    dsimp only
    by_cases hov : f.exponentBound ≤ shift
    · rw [decide_eq_true hov, ite_eq_left ((hover _).1 hov)]
      rfl
    · rw [decide_eq_false hov, ite_eq_right (fun h => hov ((hover _).2 h))]
      cases inexact <;> rfl

/-! ## `quantize` (§5.3.2) -/

/--
Kernel form of `Arithmetic.quantize` (`quantize_eq`): a finite first operand is rounded at the
quantum exponent of a finite second operand by `quantizeAt`. Every other case is the
specification.
-/
def quantize (f : Format) (mode : RoundingMode) (x y : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q => Datum.casesOn (motive := fun _ => Outcome) y
      (fun _ _ r => quantizeAt f mode true s c q r)
      (fun _ => Arithmetic.quantize f mode x y) (fun _ _ _ => Arithmetic.quantize f mode x y))
    (fun _ => Arithmetic.quantize f mode x y) (fun _ _ _ => Arithmetic.quantize f mode x y)

/--
Decimal `quantize` is its kernel form, for every format, rounding direction and pair of data:
the same datum and the same flags.
-/
@[kernel_optimize] theorem quantize_eq (f : Format) (mode : RoundingMode) (x y : Datum) :
    Arithmetic.quantize f mode x y = quantize f mode x y := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> rcases y with ⟨s', d, r⟩ | s' | ⟨s', t', p'⟩ <;>
    try rfl
  exact quantizeAt_eq f mode s c q r

/-! ## Integral rounding (§5.3.1) -/

/-- The larger of an integer and zero, by cases on its constructor (`nonnegative_eq`). -/
def nonnegative (q : Int) : Int :=
  Int.casesOn (motive := fun _ => Int) q (fun n => Int.ofNat n) (fun _ => Int.ofNat 0)

/-- `nonnegative q` is `max q 0`. -/
theorem nonnegative_eq (q : Int) : nonnegative q = max q 0 := by
  rcases q with n | n
  · exact (max_eq_left (Int.natCast_nonneg n)).symm
  · exact (max_eq_right (Int.negSucc_lt_zero n).le).symm

/--
Kernel form of the decimal integral roundings (`roundToIntegralExact_eq`,
`roundToIntegral_eq`): a finite datum with the quantum exponent `q` is rounded at `max q 0` by
`quantizeAt`, with the `inexact` signal when `signalInexact` is `true`. An infinity and a NaN
are left to the specification.
-/
def roundToIntegral (f : Format) (mode : RoundingMode) (signalInexact : Bool) (x : Datum) :
    Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q => quantizeAt f mode signalInexact s c q (nonnegative q))
    (fun _ => Bool.casesOn (motive := fun _ => Outcome) signalInexact
      (Arithmetic.roundToIntegral f mode x) (Arithmetic.roundToIntegralExact f mode x))
    (fun _ _ _ => Bool.casesOn (motive := fun _ => Outcome) signalInexact
      (Arithmetic.roundToIntegral f mode x) (Arithmetic.roundToIntegralExact f mode x))

/--
IEEE 754-2019 §5.3.1 `roundToIntegralExact` on decimal data is its kernel form, for every
format, rounding direction and datum: the same datum and the same flags.
-/
@[kernel_optimize] theorem roundToIntegralExact_eq (f : Format) (mode : RoundingMode)
    (x : Datum) :
    Arithmetic.roundToIntegralExact f mode x = roundToIntegral f mode true x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  change Arithmetic.quantizeMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ q) (max q 0) =
    quantizeAt f mode true s c q (nonnegative q)
  rw [nonnegative_eq, quantizeAt_eq]

/--
The integral rounding of IEEE 754-2019 §5.3.1 in a given direction on decimal data, which
does not signal `inexact`, is its kernel form, for every format, rounding direction and datum.
-/
@[kernel_optimize] theorem roundToIntegral_eq (f : Format) (mode : RoundingMode) (x : Datum) :
    Arithmetic.roundToIntegral f mode x = roundToIntegral f mode false x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  change ({ Arithmetic.roundToIntegralExact f mode (.finite s c q) with
      status := { (Arithmetic.roundToIntegralExact f mode (.finite s c q)).status with
        inexact := false } } : Outcome) = quantizeAt f mode false s c q (nonnegative q)
  rw [roundToIntegralExact_eq, quantizeAt_quiet]
  rfl

/-! ## Kernel shapes -/

kernel_shape roundAtQuantum
kernel_shape droppedAt
kernel_shape signedInteger
kernel_shape inRange
kernel_shape convertToInteger
kernel_shape fits
kernel_shape quantizeAt
kernel_shape deliverRounded
kernel_shape quantize
kernel_shape nonnegative
kernel_shape roundToIntegral

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
