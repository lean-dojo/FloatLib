/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedProof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds
import Mathlib.Order.Compare

/-!
# Correctness of rounding by exact comparisons

For a conventional IEEE descriptor and a comparator that orders a real number `r` against every
rational, `ComparisonRounding.round` to nearest-even delivers `roundAt fmt r` whenever its
result is finite (`toReal_round`). `inexact` is raised exactly when the delivered value is not
`r`, in every direction (`deliver_inexact_iff`), and a delivery that is not finite raises
`overflow` (`deliver_overflow_of_isFinite_eq_false`).

The equation with `roundAt` in this module is for rounding to nearest-even. For the directions
toward negative and toward positive infinity the theorems here are enclosures in the extended
reals: the result of `.down` is at most `r` (`toEReal_round_down_le`) and the result of `.up`
is at least `r` (`le_toEReal_round_up`), infinite results included.
`Rounding.Comparison.Directions` proves correct rounding in every direction: the result is
`roundAt fmt r mode` in range and the overflow result of the direction beyond it.

`Rule.Locates rule r` says that a rule delivers one rounding of `r`: an exact zero for `r = 0`,
or a comparator of `r`. `toReal_unary` and `toReal_binary` carry `toReal_round` through the
operand tables: at finite operands whose rule locates `r`, a finite result denotes
`roundAt fmt r`. `unary_encloses` and `binary_encloses` do the same for the two enclosures. No
statement is made here about `underflow`.

`deliver` may be given a hint: a nearest-even result that was found without the comparator.
`Hint.Sound hint r` says that the hint is right about `r`, and the theorems for nearest-even and
for `inexact` hold for every such hint (`toReal_deliver`, `deliver_inexact_iff`). The directed
directions do not read the hint.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.ComparisonRounding

open FloatLib.Floats

variable {fmt : FloatFormat}

/-- Negating the left side of a comparison exchanges and negates both sides. -/
private theorem cmp_neg_left (a b : ℝ) : cmp (-a) b = cmp (-b) a := by
  rcases lt_trichotomy (-a) b with h | h | h
  · rw [(cmp_eq_lt_iff _ _).mpr h, (cmp_eq_lt_iff _ _).mpr (neg_lt.mp h)]
  · rw [(cmp_eq_eq_iff _ _).mpr h, (cmp_eq_eq_iff _ _).mpr (by linarith)]
  · rw [(cmp_eq_gt_iff _ _).mpr h, (cmp_eq_gt_iff _ _).mpr (by linarith)]

/-- The comparator that `round` uses for a negative number orders its magnitude. -/
theorem magnitude_compare {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (candidate : ℚ) : (compare (-candidate)).swap = cmp (-target) (candidate : ℝ) := by
  rw [hcompare, cmp_swap, Rat.cast_neg, cmp_neg_left]

/--
**Rounding by exact comparisons is nearest-even rounding.** For a conventional IEEE descriptor
and a comparator of the real number `target`, a finite result of `round` denotes
`roundAt fmt target`.
-/
theorem toReal_round (hfmt : fmt.isIEEE = true) (compare : ℚ → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hfinite : isFinite (round fmt compare) = true) :
    toReal (round fmt compare) = roundAt fmt target := by
  have hzero := hcompare 0
  rw [Rat.cast_zero] at hzero
  unfold round at hfinite ⊢
  cases h : compare 0 with
  | eq =>
      have htarget : target = 0 := by
        rw [h] at hzero
        exact (cmp_eq_eq_iff _ _).mp hzero.symm
      simp [htarget]
  | gt =>
      have hpos : 0 < target := by
        rw [h] at hzero
        exact (cmp_eq_gt_iff _ _).mp hzero.symm
      simp only [h, roundMagnitude] at hfinite ⊢
      simpa using
        AlgebraicRounding.toReal_round_eq_roundAt fmt hfmt false compare target hpos.le hcompare
          hfinite
  | lt =>
      have hneg : target < 0 := by
        rw [h] at hzero
        exact (cmp_eq_lt_iff _ _).mp hzero.symm
      simp only [h, roundMagnitude] at hfinite ⊢
      simpa using
        AlgebraicRounding.toReal_round_eq_roundAt fmt hfmt true _ (-target)
          (neg_nonneg.mpr hneg.le) (magnitude_compare hcompare) hfinite

/-! ## The directions toward negative and toward positive infinity -/

/-- The representative carries the requested sign. -/
theorem representative_negative (sign : Bool) (compare : ℚ → Ordering) (away : Option Bool) :
    (representative fmt sign compare away).negative = sign := by
  unfold representative
  dsimp only
  split
  · split <;> rfl
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- The real value of a dyadic number is its magnitude with its sign. -/
private theorem toReal_of_negative (d : Numerics.Dyadic) :
    d.toReal = (if d.negative then -1 else 1) *
      ((d.significand : ℝ) * Flocq.bpow Numerics.binaryRadix d.exponent) := by
  cases h : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, h, Flocq.bpow,
      Numerics.binaryRadix, Numerics.Radix.toReal]

/--
For a conventional IEEE descriptor and a comparator of the positive real number `target`, the
representative for a direction toward zero has a magnitude of at most `target`.
-/
theorem representative_toward_le (hfmt : fmt.isIEEE = true) (sign : Bool)
    {compare : ℚ → Ordering} {target : ℝ} (hpos : 0 < target)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)) :
    ((representative fmt sign compare (some false)).significand : ℝ) *
        Flocq.bpow Numerics.binaryRadix (representative fmt sign compare (some false)).exponent ≤
      target := by
  unfold representative
  simp only [AlgebraicRounding.powerBounds_compare fmt hcompare]
  cases hlow : compare (AlgebraicRounding.powerOfTwo (AlgebraicRounding.lowerExponent fmt)) with
  | lt => simpa using hpos.le
  | eq =>
      have htarget : target =
          Flocq.bpow Numerics.binaryRadix (AlgebraicRounding.lowerExponent fmt) := by
        simpa only [hcompare, AlgebraicRounding.cast_powerOfTwo, cmp_eq_eq_iff] using hlow
      simp [htarget]
  | gt =>
      dsimp only
      split_ifs with hhigh
      · have hle : Flocq.bpow Numerics.binaryRadix (AlgebraicRounding.upperExponent fmt) ≤
            target := by
          simpa only [hcompare, AlgebraicRounding.cast_powerOfTwo, ne_eq, cmp_eq_lt_iff, not_lt]
            using hhigh
        simpa using hle
      · have hlo := (AlgebraicRounding.bpow_lowerExponent_lt_of_compare_eq_gt fmt hcompare hlow).le
        have hhi := AlgebraicRounding.lt_bpow_upperExponent_of_compare_eq_lt fmt hcompare
          (by simpa only [not_not] using hhigh)
        obtain ⟨-, ha, -⟩ :=
          AlgebraicRounding.certificate_spec fmt hfmt compare target hcompare hlo hhi
        exact (le_div_iff₀ (Flocq.bpow.pos _ _)).mp (accuracyRepresents_bounds ha).1

/--
For a comparator of a real number `target` of at least `2 ^ (emax + 1)`, the representative is
that power of two, whatever the direction.
-/
theorem representative_of_le (sign : Bool) (away : Option Bool) {compare : ℚ → Ordering}
    {target : ℝ} (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hlarge : Flocq.bpow Numerics.binaryRadix (AlgebraicRounding.upperExponent fmt) ≤ target) :
    representative fmt sign compare away = ⟨sign, 1, AlgebraicRounding.upperExponent fmt⟩ := by
  have hlow : compare (AlgebraicRounding.powerOfTwo (AlgebraicRounding.lowerExponent fmt)) =
      .gt := by
    rw [hcompare, AlgebraicRounding.cast_powerOfTwo, cmp_eq_gt_iff]
    exact ((Flocq.bpow_lt_bpow_iff _ _ _).mpr
      (AlgebraicRounding.lowerExponent_lt_upperExponent fmt)).trans_le hlarge
  have hhigh : compare (AlgebraicRounding.powerOfTwo (AlgebraicRounding.upperExponent fmt)) ≠
      .lt := by
    rw [hcompare, AlgebraicRounding.cast_powerOfTwo, ne_eq, cmp_eq_lt_iff]
    exact not_lt.mpr hlarge
  unfold representative
  simp only [AlgebraicRounding.powerBounds_compare fmt hcompare, hlow, hhigh, ne_eq,
    not_false_eq_true, ↓reduceIte]

/--
For a conventional IEEE descriptor and a comparator of a real number `target` below
`2 ^ (emax + 1)`, the representative for a direction away from zero has a magnitude of at least
`target`.
-/
theorem le_representative_away (hfmt : fmt.isIEEE = true) (sign : Bool)
    {compare : ℚ → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (hrange : target < Flocq.bpow Numerics.binaryRadix (AlgebraicRounding.upperExponent fmt)) :
    target ≤ ((representative fmt sign compare (some true)).significand : ℝ) *
      Flocq.bpow Numerics.binaryRadix (representative fmt sign compare (some true)).exponent := by
  have hhigh : compare (AlgebraicRounding.powerOfTwo (AlgebraicRounding.upperExponent fmt)) =
      .lt := by
    rw [hcompare, AlgebraicRounding.cast_powerOfTwo, cmp_eq_lt_iff]
    exact hrange
  unfold representative
  simp only [AlgebraicRounding.powerBounds_compare fmt hcompare, hhigh, ne_eq, not_true_eq_false,
    ↓reduceIte]
  cases hlow : compare (AlgebraicRounding.powerOfTwo (AlgebraicRounding.lowerExponent fmt)) with
  | lt =>
      have hlt : target <
          Flocq.bpow Numerics.binaryRadix (AlgebraicRounding.lowerExponent fmt) := by
        simpa only [hcompare, AlgebraicRounding.cast_powerOfTwo, cmp_eq_lt_iff] using hlow
      simpa using hlt.le
  | eq =>
      have htarget : target =
          Flocq.bpow Numerics.binaryRadix (AlgebraicRounding.lowerExponent fmt) := by
        simpa only [hcompare, AlgebraicRounding.cast_powerOfTwo, cmp_eq_eq_iff] using hlow
      simp [htarget]
  | gt =>
      dsimp only
      have hlo := (AlgebraicRounding.bpow_lowerExponent_lt_of_compare_eq_gt fmt hcompare hlow).le
      obtain ⟨-, ha, -⟩ :=
        AlgebraicRounding.certificate_spec fmt hfmt compare target hcompare hlo hrange
      have hb := accuracyRepresents_bounds ha
      rw [← div_le_iff₀ (Flocq.bpow.pos _ _)]
      cases haccuracy : (AlgebraicRounding.certificate fmt compare).accuracy with
      | exact =>
          rw [haccuracy] at ha
          exact le_of_eq ha
      | inexact ordering =>
          push_cast
          exact hb.2.le

/--
**Rounding toward negative infinity does not exceed the located number.** For a conventional
IEEE descriptor and a comparator of the real number `target`, the result of `round` in the
direction `.down` is at most `target` in the extended reals, a result of negative infinity
included.
-/
theorem toEReal_round_down_le (hfmt : fmt.isIEEE = true) (compare : ℚ → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)) :
    toEReal (round fmt compare .down) ≤ (target : EReal) := by
  have heq : round fmt compare .down =
      AlgebraicRounding.roundSigned fmt .down compare := by
    unfold round AlgebraicRounding.roundSigned
    cases compare 0 <;> rfl
  rw [heq, AlgebraicRounding.roundSigned_eq_roundReal fmt .down hcompare]
  by_cases hzero : target = 0
  · simp [hzero]
  · exact (roundReal_roundsTo (fmt := fmt) .down hzero).toEReal_down_le hfmt

/--
**Rounding toward positive infinity is not below the located number.** For a conventional IEEE
descriptor and a comparator of the real number `target`, the result of `round` in the direction
`.up` is at least `target` in the extended reals, a result of positive infinity included.
-/
theorem le_toEReal_round_up (hfmt : fmt.isIEEE = true) (compare : ℚ → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)) :
    (target : EReal) ≤ toEReal (round fmt compare .up) := by
  have heq : round fmt compare .up =
      AlgebraicRounding.roundSigned fmt .up compare := by
    unfold round AlgebraicRounding.roundSigned
    cases compare 0 <;> rfl
  rw [heq, AlgebraicRounding.roundSigned_eq_roundReal fmt .up hcompare]
  by_cases hzero : target = 0
  · simp [hzero]
  · exact (roundReal_roundsTo (fmt := fmt) .up hzero).le_toEReal_up hfmt

/-- `outcome` delivers the value it is given. -/
@[simp] theorem outcome_value (compare : ℚ → Ordering) (value : Model fmt)
    (mode : IEEERoundingMode) (known : Option Ordering) :
    (outcome fmt compare value mode known).value = value := by
  unfold outcome
  split <;> rfl

/--
For a comparator of the real number `target` and a `known` ordering that, when present, is the
ordering of the value and `target`, the outcome of a finite value raises `inexact` exactly when
the value is not `target`, in every direction.
-/
theorem outcome_inexact_iff (compare : ℚ → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    {value : Model fmt} (mode : IEEERoundingMode) {known : Option Ordering}
    (hknown : ∀ ordering, known = some ordering → ordering = cmp (toReal value) target)
    (hfinite : isFinite value = true) :
    (outcome fmt compare value mode known).status.inexact = true ↔ toReal value ≠ target := by
  obtain ⟨delivered, hdelivered, hreal⟩ := Algebraic.exists_toRat?_of_isFinite hfinite
  unfold outcome
  cases known with
  | none =>
      simp only [hdelivered, hcompare, hreal, bne_iff_ne, ne_eq]
      rw [cmp_swap, cmp_eq_eq_iff]
  | some ordering =>
      simp only [hdelivered, hknown ordering rfl, hreal, bne_iff_ne, ne_eq]
      rw [cmp_eq_eq_iff]

/--
That a hint is right about `target`: a result it has is finite, denotes `roundAt fmt target`,
and an ordering it states is the ordering of that value and `target`.
-/
def Hint.Sound (hint : Unit → Option (Hint fmt)) (target : ℝ) : Prop :=
  ∀ found, hint () = some found → isFinite found.value = true ∧
    toReal found.value = roundAt fmt target ∧
    ∀ ordering, found.ternary = some ordering → ordering = cmp (toReal found.value) target

/-- The hint without a result is right about every number. -/
theorem Hint.sound_none (target : ℝ) : Hint.Sound (fmt := fmt) (fun _ => none) target :=
  fun _ h => absurd h (by simp)

/-- Without a hint `resolve` selects the rounding by comparisons, in every direction. -/
theorem resolve_none (compare : ℚ → Ordering) (mode : IEEERoundingMode) :
    resolve fmt compare mode (fun _ => none) = ⟨round fmt compare mode, none⟩ := by
  cases mode <;> rfl

/-- An ordering that `resolve` states is the ordering of its value and `target`. -/
theorem resolve_ternary (compare : ℚ → Ordering) (mode : IEEERoundingMode)
    {hint : Unit → Option (Hint fmt)} {target : ℝ} (hhint : Hint.Sound hint target)
    (ordering : Ordering) (h : (resolve fmt compare mode hint).ternary = some ordering) :
    ordering = cmp (toReal (resolve fmt compare mode hint).value) target := by
  cases mode
  case nearest =>
    unfold resolve at h ⊢
    dsimp only at h ⊢
    cases hfound : hint () with
    | none => simp [hfound] at h
    | some found =>
        rw [hfound] at h
        exact (hhint found hfound).2.2 ordering h
  all_goals exact absurd h (by simp [resolve])

/-- `deliver` adds flags to the value that `resolve` selects. -/
@[simp] theorem deliver_value (compare : ℚ → Ordering) (mode : IEEERoundingMode)
    (hint : Unit → Option (Hint fmt)) :
    (deliver fmt compare mode hint).value = (resolve fmt compare mode hint).value := by
  simp [deliver]

/-- A delivery that is not finite raises `overflow`, in every direction. -/
theorem deliver_overflow_of_isFinite_eq_false (compare : ℚ → Ordering) (mode : IEEERoundingMode)
    (h : isFinite (round fmt compare mode) = false) :
    (deliver fmt compare mode).status.overflow = true := by
  change (outcome fmt compare (resolve fmt compare mode fun _ => none).value mode
    (resolve fmt compare mode fun _ => none).ternary).status.overflow = true
  rw [resolve_none]
  unfold outcome
  split
  · next delivered hdelivered =>
      rw [Algebraic.isFinite_of_toRat?_eq_some hdelivered] at h
      exact absurd h (by decide)
  · rfl

/--
For a comparator of the real number `target` and a hint that is right about `target`, a finite
delivery raises `inexact` exactly when it is not `target`, in every direction.
-/
theorem deliver_inexact_iff (compare : ℚ → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (mode : IEEERoundingMode) {hint : Unit → Option (Hint fmt)} (hhint : Hint.Sound hint target)
    (hfinite : isFinite (deliver fmt compare mode hint).value = true) :
    (deliver fmt compare mode hint).status.inexact = true ↔
      toReal (deliver fmt compare mode hint).value ≠ target := by
  rw [deliver_value] at hfinite ⊢
  exact outcome_inexact_iff compare target hcompare mode (resolve_ternary compare mode hhint)
    hfinite

/--
**To nearest-even a delivery is the correctly rounded value, with or without a hint.** For a
conventional IEEE descriptor, a comparator of the real number `target` and a hint that is right
about `target`, a finite delivery to nearest-even denotes `roundAt fmt target`.
-/
theorem toReal_deliver (hfmt : fmt.isIEEE = true) (compare : ℚ → Ordering) (target : ℝ)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    {hint : Unit → Option (Hint fmt)} (hhint : Hint.Sound hint target)
    (hfinite : isFinite (deliver fmt compare .nearest hint).value = true) :
    toReal (deliver fmt compare .nearest hint).value = roundAt fmt target := by
  rw [deliver_value] at hfinite ⊢
  unfold resolve at hfinite ⊢
  dsimp only at hfinite ⊢
  cases hfound : hint () with
  | none =>
      rw [hfound] at hfinite
      exact toReal_round hfmt compare target hcompare hfinite
  | some found => exact (hhint found hfound).2.1

/-- That a rule delivers one rounding of the real number `target`. -/
def Rule.Locates : Rule → ℝ → Prop
  | .zero _, target => target = 0
  | .real compare, target => ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)
  | _, _ => False

/-- The rule of a rational value locates it. -/
theorem Rule.locates_rational (value : ℚ) : (Rule.rational value).Locates (value : ℝ) := by
  intro candidate
  simp only [cmp, cmpUsing, Rat.cast_lt]

/--
The rule of a function with `f (±0) = ±0` locates `target` when `target` is zero at a zero
argument and the comparator orders `target` elsewhere.
-/
theorem Rule.locates_oddAt {negative : Bool} {argument : ℚ} {compare : ℚ → Ordering}
    {target : ℝ} (hzero : argument = 0 → target = 0)
    (hcompare : argument ≠ 0 → ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)) :
    (Rule.oddAt negative argument compare).Locates target := by
  unfold Rule.oddAt
  split
  · next h => exact hzero h
  · next h => exact hcompare h

/--
For a conventional IEEE descriptor, a rule that locates `target` delivers `roundAt fmt target`
to nearest-even whenever its value is finite, with any hint that is right about `target`.
-/
theorem Rule.toReal_deliver (hfmt : fmt.isIEEE = true) {rule : Rule} {target : ℝ}
    (hrule : rule.Locates target) {hint : Unit → Option (Hint fmt)}
    (hhint : Hint.Sound hint target)
    (hfinite : isFinite (rule.deliver fmt .nearest hint).value = true) :
    toReal (rule.deliver fmt .nearest hint).value = roundAt fmt target := by
  cases rule with
  | zero negative =>
      have htarget : target = 0 := hrule
      simp [Rule.deliver, htarget]
  | real compare => exact ComparisonRounding.toReal_deliver hfmt compare target hrule hhint hfinite
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

/--
**A rule's directed results enclose the located number.** For a conventional IEEE descriptor, a
rule that locates `target` delivers at most `target` toward negative infinity and at least
`target` toward positive infinity, in the extended reals, whatever the hint.
-/
theorem Rule.deliver_encloses (hfmt : fmt.isIEEE = true) {rule : Rule} {target : ℝ}
    (hrule : rule.Locates target) (hint : Unit → Option (Hint fmt)) :
    toEReal (rule.deliver fmt .down hint).value ≤ (target : EReal) ∧
      (target : EReal) ≤ toEReal (rule.deliver fmt .up hint).value := by
  cases rule with
  | zero negative =>
      have htarget : target = 0 := hrule
      simp [Rule.deliver, htarget]
  | real compare =>
      simp only [Rule.deliver, deliver_value]
      exact ⟨toEReal_round_down_le hfmt compare target hrule,
        le_toEReal_round_up hfmt compare target hrule⟩
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

/--
A rule that locates `target` raises `inexact` exactly when its finite value is not `target`, in
every direction and with any hint that is right about `target`.
-/
theorem Rule.deliver_inexact_iff {rule : Rule} {target : ℝ} (hrule : rule.Locates target)
    (mode : IEEERoundingMode) {hint : Unit → Option (Hint fmt)} (hhint : Hint.Sound hint target)
    (hfinite : isFinite (rule.deliver fmt mode hint).value = true) :
    (rule.deliver fmt mode hint).status.inexact = true ↔
      toReal (rule.deliver fmt mode hint).value ≠ target := by
  cases rule with
  | zero negative =>
      have htarget : target = 0 := hrule
      simp [Rule.deliver, htarget, Numerics.IEEEStatus.clear]
  | real compare =>
      exact ComparisonRounding.deliver_inexact_iff compare target hrule mode hhint hfinite
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

/-- A finite value is the finite operand of its sign bit and its exact value. -/
theorem Operand.of?_of_toRat? {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) :
    Operand.of? x = some (.finite (signBit x) q) := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hq
  simp [Operand.of?, isNaN_eq_false_of_isFinite_eq_true x hfinite,
    isInfinite_eq_false_of_isFinite_eq_true x hfinite, hq]

/-- At a finite operand a function of one operand is the outcome of its rule, with the hint of
that operand. -/
theorem unary_of_toRat? (rule : Operand → Rule) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) (mode : IEEERoundingMode)
    (hint : Operand → Unit → Option (Hint fmt)) :
    unary rule x mode hint =
      (rule (.finite (signBit x) q)).deliver fmt mode (hint (.finite (signBit x) q)) := by
  simp [unary, Operand.of?_of_toRat? hq]

/-- A rounding raises neither `invalid` nor `divideByZero`: the outcome of a value has the
flags `overflow`, `underflow` and `inexact` only. -/
theorem outcome_invalid_divideByZero (compare : ℚ → Ordering) (value : Model fmt)
    (mode : IEEERoundingMode) (known : Option Ordering) :
    (outcome fmt compare value mode known).status.invalid = false ∧
      (outcome fmt compare value mode known).status.divideByZero = false := by
  unfold outcome
  split <;> exact ⟨rfl, rfl⟩

/-- A rule that locates a real number raises neither `invalid` nor `divideByZero`, in every
rounding direction and with any hint. -/
theorem Rule.deliver_invalid_divideByZero {rule : Rule} {target : ℝ}
    (hrule : rule.Locates target) (mode : IEEERoundingMode)
    (hint : Unit → Option (Hint fmt)) :
    (rule.deliver fmt mode hint).status.invalid = false ∧
      (rule.deliver fmt mode hint).status.divideByZero = false := by
  cases rule with
  | zero negative => exact ⟨rfl, rfl⟩
  | real compare => exact outcome_invalid_divideByZero compare _ mode _
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

/-- At finite operands a function of two operands is the outcome of its rule, with the hint
of that pair. -/
theorem binary_of_toRat? (rule : Operand → Operand → Rule) {x y : Model fmt} {p q : ℚ}
    (hp : toRat? x = some p) (hq : toRat? y = some q) (mode : IEEERoundingMode)
    (hint : Operand → Operand → Unit → Option (Hint fmt)) :
    binary rule x y mode hint =
      (rule (.finite (signBit x) p) (.finite (signBit y) q)).deliver fmt mode
        (hint (.finite (signBit x) p) (.finite (signBit y) q)) := by
  simp [binary, Operand.of?_of_toRat? hp, Operand.of?_of_toRat? hq]

/-- At a finite operand whose rule locates a real number, a function of one operand raises
neither `invalid` nor `divideByZero`, in every rounding direction. -/
theorem unary_invalid_divideByZero (rule : Operand → Rule) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) q)).Locates target) (mode : IEEERoundingMode)
    (hint : Operand → Unit → Option (Hint fmt)) :
    (unary rule x mode hint).status.invalid = false ∧
      (unary rule x mode hint).status.divideByZero = false := by
  rw [unary_of_toRat? rule hq]
  exact Rule.deliver_invalid_divideByZero hrule mode _

/-- At finite operands whose rule locates a real number, a function of two operands raises
neither `invalid` nor `divideByZero`, in every rounding direction. -/
theorem binary_invalid_divideByZero (rule : Operand → Operand → Rule) {x y : Model fmt}
    {p q : ℚ} (hp : toRat? x = some p) (hq : toRat? y = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) p) (.finite (signBit y) q)).Locates target)
    (mode : IEEERoundingMode) (hint : Operand → Operand → Unit → Option (Hint fmt)) :
    (binary rule x y mode hint).status.invalid = false ∧
      (binary rule x y mode hint).status.divideByZero = false := by
  rw [binary_of_toRat? rule hp hq]
  exact Rule.deliver_invalid_divideByZero hrule mode _

/--
**A function of one operand rounds once.** For a conventional IEEE descriptor, a finite operand
whose rule locates `target` and a hint that is right about `target` at that operand, a finite
result to nearest-even denotes `roundAt fmt target`.
-/
theorem toReal_unary (hfmt : fmt.isIEEE = true) (rule : Operand → Rule) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) q)).Locates target)
    {hint : Operand → Unit → Option (Hint fmt)}
    (hhint : Hint.Sound (hint (.finite (signBit x) q)) target)
    (hfinite : isFinite (unary rule x .nearest hint).value = true) :
    toReal (unary rule x .nearest hint).value = roundAt fmt target := by
  rw [unary_of_toRat? rule hq] at hfinite ⊢
  exact Rule.toReal_deliver hfmt hrule hhint hfinite

/--
**A function of two operands rounds once.** For a conventional IEEE descriptor, finite operands
whose rule locates `target` and a hint that is right about `target` at those operands, a finite
result to nearest-even denotes `roundAt fmt target`.
-/
theorem toReal_binary (hfmt : fmt.isIEEE = true) (rule : Operand → Operand → Rule)
    {x y : Model fmt} {p q : ℚ} (hp : toRat? x = some p) (hq : toRat? y = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) p) (.finite (signBit y) q)).Locates target)
    {hint : Operand → Operand → Unit → Option (Hint fmt)}
    (hhint : Hint.Sound (hint (.finite (signBit x) p) (.finite (signBit y) q)) target)
    (hfinite : isFinite (binary rule x y .nearest hint).value = true) :
    toReal (binary rule x y .nearest hint).value = roundAt fmt target := by
  rw [binary_of_toRat? rule hp hq] at hfinite ⊢
  exact Rule.toReal_deliver hfmt hrule hhint hfinite

/--
**The directed results of a function of one operand enclose its value.** For a conventional
IEEE descriptor and a finite operand whose rule locates `target`, the result toward negative
infinity is at most `target` and the result toward positive infinity at least `target`,
whatever the hint.
-/
theorem unary_encloses (hfmt : fmt.isIEEE = true) (rule : Operand → Rule) {x : Model fmt} {q : ℚ}
    (hq : toRat? x = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) q)).Locates target)
    (hint : Operand → Unit → Option (Hint fmt)) :
    toEReal (unary rule x .down hint).value ≤ (target : EReal) ∧
      (target : EReal) ≤ toEReal (unary rule x .up hint).value := by
  rw [unary_of_toRat? rule hq, unary_of_toRat? rule hq]
  exact Rule.deliver_encloses hfmt hrule _

/--
**The directed results of a function of two operands enclose its value.** For a conventional
IEEE descriptor and finite operands whose rule locates `target`, the result toward negative
infinity is at most `target` and the result toward positive infinity at least `target`,
whatever the hint.
-/
theorem binary_encloses (hfmt : fmt.isIEEE = true) (rule : Operand → Operand → Rule)
    {x y : Model fmt} {p q : ℚ} (hp : toRat? x = some p) (hq : toRat? y = some q) {target : ℝ}
    (hrule : (rule (.finite (signBit x) p) (.finite (signBit y) q)).Locates target)
    (hint : Operand → Operand → Unit → Option (Hint fmt)) :
    toEReal (binary rule x y .down hint).value ≤ (target : EReal) ∧
      (target : EReal) ≤ toEReal (binary rule x y .up hint).value := by
  rw [binary_of_toRat? rule hp hq, binary_of_toRat? rule hp hq]
  exact Rule.deliver_encloses hfmt hrule _

end FloatLib.Floats.Formats.BinaryInterchange.Model.ComparisonRounding
