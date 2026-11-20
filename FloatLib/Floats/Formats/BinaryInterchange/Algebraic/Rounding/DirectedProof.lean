/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedRuntime
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.HalfUlp
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Grid
public import FloatLib.Floats.Formats.Flocq.Calculation.GuardSticky
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.RoundedReal
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
public import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correct rounding from exact comparisons, in every rounding direction

`Model.roundReal fmt mode x` is the rounding of the real `x` to the format `fmt` in the direction
`mode`. It is `AlgebraicRounding.roundSigned` run on the comparisons of `x` itself, so any
executable oracle that orders `x` against every rational gives the same encoding
(`roundSigned_eq_roundReal`), with no premise on a search budget or on the distance of `x` from a
rounding boundary.

`roundReal_roundsTo` states what that encoding is for every format descriptor, in the words of
IEEE 754-2019: with `roundAt fmt x mode` the rounding of `x` on the grid of the format with an
unbounded exponent range (clause 4.3), the result is that value when it is at most the largest
finite magnitude, and otherwise the overflow result of the direction (clause 7.4). The
descriptors are the IEEE ones, the formats without an infinity such as OCP E4M3, whose overflow
result is their NaN when the direction rounds away and their largest finite value otherwise,
the formats with one zero such as ONNX E4M3FNUZ, and the formats in which every encoding is
finite. In a format with signed zeros the sign bit is the sign of `x`, also when the result is a
zero or an infinity. `roundMagnitude_roundsTo`, `roundLocated_roundsTo` and `packGrid_roundsTo`
are its steps.

Negation mirrors the direction: `roundReal_neg` and, on oracles, `roundSigned_neg` say that
rounding `-x` is the negation of rounding `x` in the direction `mode.negate`.

The proof reads the rounding off a bracket of the scaled significand. The oracle's truncated
significand has two bits below the last place and a flag for exactness, which locate the
significand between two integers and against their midpoint, and `Flocq.round_of_guardSticky`
computes each direction from that location. A located magnitude is delivered through
`roundRatScaled` at a value of the grid, which every descriptor delivers exactly
(`roundRatScaled_of_grid`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/--
`result` is the rounding of the real `x` in the direction `mode`, with the sign `sign`.

`roundAt fmt x mode` rounds on the grid of `fmt` with an unbounded exponent range. When that value
is at most the largest finite magnitude, `result` is finite and denotes it. Otherwise `result`
is the overflow result of IEEE 754-2019, clause 7.4. In a format with signed zeros `result`
carries the sign bit `sign`, also when it is a zero. A format with one zero delivers that zero
for a negative value that rounds to zero and its NaN, whose encoding is fixed, as the overflow
result of either sign, so its sign bit is not part of the contract.
-/
structure RoundsTo (fmt : FloatFormat) (mode : IEEERoundingMode) (x : ℝ) (sign : Bool)
    (result : Model fmt) : Prop where
  /-- In range, the result is finite and denotes the grid rounding. -/
  finite : |roundAt fmt x mode| ≤ toReal (posMaxFinite fmt) →
    isFinite result = true ∧ toReal result = roundAt fmt x mode
  /-- Out of range, the result is the overflow value of the direction. -/
  overflow : toReal (posMaxFinite fmt) < |roundAt fmt x mode| →
    result = directedOverflow fmt sign (mode.overflowRoundsMagnitudeUp sign)
  /-- In a format with signed zeros the result carries the given sign bit. -/
  signBit : fmt.supportsSignedZero = true → signBit result = sign

/-- In an IEEE format, which has signed zeros, the result carries the given sign bit. -/
theorem RoundsTo.signBit_of_isIEEE {fmt : FloatFormat} {mode : IEEERoundingMode} {x : ℝ}
    {sign : Bool} {result : Model fmt} (h : RoundsTo fmt mode x sign result)
    (hfmt : fmt.isIEEE = true) : Model.signBit result = sign :=
  h.signBit (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt)

/-- A downward rounding contract gives an extended-real lower bound, including overflow. -/
theorem RoundsTo.toEReal_down_le {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x : ℝ} {result : Model fmt}
    (h : RoundsTo fmt .down x (decide (x < 0)) result) :
    toEReal result ≤ (x : EReal) := by
  have hround : roundAt fmt x .down ≤ x := Flocq.round_floor_le x
  by_cases hrange : |roundAt fmt x .down| ≤ toReal (posMaxFinite fmt)
  · obtain ⟨hfinite, hvalue⟩ := h.finite hrange
    rw [toEReal_eq_coe_toReal_of_isFinite _ hfinite, hvalue]
    exact EReal.coe_le_coe_iff.mpr hround
  · rw [h.overflow (not_le.mp hrange)]
    by_cases hx : x < 0
    · simp [hx, IEEERoundingMode.overflowRoundsMagnitudeUp,
        IEEERoundingMode.roundsAwayFromZero, directedOverflow,
        nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt, toEReal_negInf fmt hfmt]
    · have hnonneg : 0 ≤ roundAt fmt x .down := by
        simpa only [roundAt_zero] using roundAt_mono fmt (not_lt.mp hx) .down
      have hbeyond := not_le.mp hrange
      rw [abs_of_nonneg hnonneg] at hbeyond
      simp only [hx, decide_false, IEEERoundingMode.overflowRoundsMagnitudeUp,
        IEEERoundingMode.roundsAwayFromZero, directedOverflow, Bool.false_eq_true, ↓reduceIte]
      rw [toEReal_eq_coe_toReal_of_isFinite _ (isFinite_maxFinite fmt false),
        toReal_maxFinite]
      exact EReal.coe_le_coe_iff.mpr (by simpa using hbeyond.le.trans hround)

/-- An upward rounding contract gives an extended-real upper bound, including overflow. -/
theorem RoundsTo.le_toEReal_up {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x : ℝ} {result : Model fmt}
    (h : RoundsTo fmt .up x (decide (x < 0)) result) :
    (x : EReal) ≤ toEReal result := by
  have hround : x ≤ roundAt fmt x .up := Flocq.le_round_ceil x
  by_cases hrange : |roundAt fmt x .up| ≤ toReal (posMaxFinite fmt)
  · obtain ⟨hfinite, hvalue⟩ := h.finite hrange
    rw [toEReal_eq_coe_toReal_of_isFinite _ hfinite, hvalue]
    exact EReal.coe_le_coe_iff.mpr hround
  · rw [h.overflow (not_le.mp hrange)]
    by_cases hx : x < 0
    · have hnonpos : roundAt fmt x .up ≤ 0 := by
        simpa only [roundAt_zero] using roundAt_mono fmt hx.le .up
      have hbeyond := not_le.mp hrange
      rw [abs_of_nonpos hnonpos] at hbeyond
      simp only [hx, decide_true, IEEERoundingMode.overflowRoundsMagnitudeUp,
        IEEERoundingMode.roundsAwayFromZero, Bool.not_true, directedOverflow,
        Bool.false_eq_true, ↓reduceIte]
      rw [toEReal_eq_coe_toReal_of_isFinite _ (isFinite_maxFinite fmt true),
        toReal_maxFinite]
      exact EReal.coe_le_coe_iff.mpr (by simp only [↓reduceIte]; linarith)
    · simp [hx, IEEERoundingMode.overflowRoundsMagnitudeUp,
        IEEERoundingMode.roundsAwayFromZero, directedOverflow,
        nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt, toEReal_posInf fmt hfmt]

namespace AlgebraicRounding

/-! ## Delivering a magnitude on the grid -/

/-- Nearest-even rational rounding in an IEEE format keeps the sign bit it is given. -/
theorem signBit_roundRatScaled {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (hdenominator : denominator ≠ 0) :
    signBit (roundRatScaled fmt sign numerator denominator exponent) = sign := by
  rw [roundRatScaled, dite_eq_left hfmt]
  exact signBit_ieeeRoundRatScaled hfmt sign numerator denominator exponent hdenominator

/-- In a format with signed zeros, the overflow result of every direction carries the sign of
the value that overflowed: an infinity, the NaN of a format without one, or the largest finite
value. -/
theorem signBit_directedOverflow {fmt : FloatFormat}
    (hzero : fmt.supportsSignedZero = true) (sign roundMagnitudeUp : Bool) :
    signBit (directedOverflow fmt sign roundMagnitudeUp) = sign := by
  cases roundMagnitudeUp
  · simp [directedOverflow]
  · simp only [directedOverflow, ↓reduceIte, nativeOverflow]
    cases hencoding : fmt.encoding with
    | ieee => cases sign <;> simp
    | finiteMaxNaN => simp [propagatedNaN, hencoding]
    | finiteUnsignedZero => simp [FloatFormat.supportsSignedZero, hencoding] at hzero
    | finite => simp

/--
`packGrid` delivers a magnitude that is already on the grid of the format, for every format
descriptor: in range it is the finite encoding of the signed magnitude, and beyond the largest
finite value it is the overflow result of the direction.
-/
theorem packGrid_roundsTo {fmt : FloatFormat}
    (mode : IEEERoundingMode) (sign : Bool) (mantissa : Nat) (exponent : Int) (x : ℝ)
    (hround : roundAt fmt x mode =
      (if sign then (-1 : ℝ) else 1) * ((mantissa : ℝ) * Flocq.bpow binaryRadix exponent)) :
    RoundsTo fmt mode x sign (packGrid fmt mode sign mantissa exponent) := by
  have hpow := Flocq.bpow.pos binaryRadix exponent
  have habs : |roundAt fmt x mode| = (mantissa : ℝ) * Flocq.bpow binaryRadix exponent := by
    rw [hround]
    cases sign <;> simp [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg mantissa) hpow.le)]
  have hmax := toReal_posMaxFinite_pos fmt
  unfold packGrid
  simp only [Dyadic.Internal.compareScalable_eq_compare,
    Dyadic.compare_eq_lt_iff]
  split
  · rename_i hmantissa
    have hvalue : roundAt fmt x mode = 0 := by simp [hround, hmantissa]
    refine ⟨fun _ => ⟨isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign), ?_⟩,
      fun hover => ?_, ?_⟩
    · rw [toReal_zero, hvalue]
    · rw [hvalue, abs_zero] at hover
      exact absurd hover (not_lt.mpr hmax.le)
    · intro hzero
      simp [signBit_zero, hzero]
  · rename_i hmantissa
    have hcompare : (maxFiniteDyadic fmt).toRat < (Dyadic.mk false mantissa exponent).toRat ↔
        toReal (posMaxFinite fmt) < |roundAt fmt x mode| := by
      rw [habs, ← Dyadic.toReal_maxFiniteDyadic, ← Dyadic.cast_toRat, Flocq.bpow_binaryRadix,
        ← Dyadic.toReal_mk_false, ← Dyadic.cast_toRat]
      exact Rat.cast_lt.symm
    split
    · rename_i hover
      exact ⟨fun hin => absurd (hcompare.mp hover) (not_lt.mpr hin), fun _ => rfl,
        fun hzero => signBit_directedOverflow hzero sign _⟩
    · rename_i hin
      have hin : |roundAt fmt x mode| ≤ toReal (posMaxFinite fmt) :=
        not_lt.mp (mt hcompare.mpr hin)
      have hexact : signedScaledRatToReal sign mantissa 1 exponent = roundAt fmt x mode := by
        rw [hround]
        cases sign <;> simp [signedScaledRatToReal, scaledRatToReal]
      have hgrid : roundAt fmt (signedScaledRatToReal sign mantissa 1 exponent) =
          signedScaledRatToReal sign mantissa 1 exponent := by
        rw [hexact]
        exact roundAt_of_genericFormat fmt (genericFormat_roundAt fmt x mode)
      obtain ⟨hfinite, hvalue⟩ :=
        roundRatScaled_of_grid fmt sign hmantissa exponent hgrid (hexact ▸ hin)
      exact ⟨fun _ => ⟨hfinite, hvalue.trans hexact⟩,
        fun hover => absurd hover (not_lt.mpr hin),
        fun _ => signBit_roundRatScaled_of_grid fmt sign hmantissa exponent hgrid (hexact ▸ hin)⟩

/--
For an exact comparator, the bounded power search gives the same outer tests as direct
comparison with the lower and upper powers of two.
-/
theorem roundMagnitude_eq (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    {compare : Rat → Ordering} {target : ℝ}
    (hcompare : ∀ candidate : Rat, compare candidate = cmp target (candidate : ℝ)) :
    roundMagnitude fmt mode sign compare =
  if compare (powerOfTwo (upperExponent fmt)) ≠ .lt then
    directedOverflow fmt sign (mode.overflowRoundsMagnitudeUp sign)
  else if compare (powerOfTwo (lowerExponent fmt)) = .lt then
    roundLocated fmt mode sign 0 fmt.minSubnormalExponent false true
  else
    let exponent := certificateExponent fmt (binade fmt compare)
    let mantissa := truncatedMantissa fmt compare exponent
    let exact := compare ((mantissa : Rat) * powerOfTwo exponent) == .eq
    roundLocated fmt mode sign (mantissa / 4) (exponent + 2) (decide (2 ≤ mantissa % 4))
      (mantissa % 2 == 1 || !exact) := by
  simp only [roundMagnitude, powerBounds_compare fmt hcompare]

/-! ## Rounding a located magnitude -/

/-- The bracket location that a guard bit and a sticky bit name: `Flocq.guardStickyLocation`,
which the decimal formats use too. -/
abbrev location (guard sticky : Bool) : Location :=
  guardStickyLocation guard sticky

/--
A nonnegative magnitude located on the grid of `fmt`: `exponent` is its canonical exponent, and
its scaled significand lies in the unit bracket above `mantissa`, at the place that the guard and
sticky bits name.
-/
structure Located (fmt : FloatFormat) (t : ℝ) (mantissa : Nat) (exponent : Int)
    (guard sticky : Bool) : Prop where
  /-- The exponent is the canonical exponent of the magnitude. -/
  exponent_eq : cexp binaryRadix (fexpOf fmt) t = exponent
  /-- The scaled significand sits in the bracket above `mantissa` at the named location. -/
  bracket : InbetweenInt (mantissa : ℤ) (scaledMantissa binaryRadix (fexpOf fmt) t)
    (location guard sticky)

/--
Every direction rounds a located magnitude to its integer part or the next integer, as
`MagnitudeRounding.increment` decides from the parity, the guard bit and the sticky bit.
-/
theorem Located.roundAt_eq {fmt : FloatFormat} {t : ℝ} {mantissa : Nat} {exponent : Int}
    {guard sticky : Bool} (h : Located fmt t mantissa exponent guard sticky)
    (mode : IEEERoundingMode) :
    roundAt fmt t mode =
      ((if (mode.magnitudeRounding false).increment (mantissa % 2 == 1) guard sticky
        then mantissa + 1 else mantissa : ℕ) : ℝ) * Flocq.bpow binaryRadix exponent := by
  rw [roundAt_eq_round, round_of_guardSticky h.bracket mode, h.exponent_eq]

/--
`roundLocated` rounds a located magnitude with either sign, for every format descriptor: the
negative value rounds its magnitude in the mirrored direction.
-/
theorem roundLocated_roundsTo {fmt : FloatFormat} {t : ℝ}
    {mantissa : Nat} {exponent : Int} {guard sticky : Bool}
    (h : Located fmt t mantissa exponent guard sticky) (mode : IEEERoundingMode) (sign : Bool) :
    RoundsTo fmt mode (if sign then -t else t) sign
      (roundLocated fmt mode sign mantissa exponent guard sticky) := by
  apply packGrid_roundsTo
  cases sign with
  | false => simpa using h.roundAt_eq mode
  | true =>
      have hmirror := h.roundAt_eq mode.negate
      rw [IEEERoundingMode.magnitudeRounding_negate, Bool.not_false] at hmirror
      simp only [↓reduceIte]
      rw [roundAt_neg fmt t mode, hmirror]
      ring

/-! ## Locating the magnitude of an oracle -/

/-- A magnitude strictly below half the least subnormal lies in the lower half of the first cell. -/
theorem located_of_lt_lowerExponent (fmt : FloatFormat) {t : ℝ} (ht : 0 < t)
    (hsmall : t < Flocq.bpow binaryRadix (lowerExponent fmt)) :
    Located fmt t 0 fmt.minSubnormalExponent false true := by
  have hcexp : cexp binaryRadix (fexpOf fmt) t = fmt.minSubnormalExponent := by
    have hmag := magnitude_le_of_abs_lt_bpow binaryRadix t (lowerExponent fmt) ht.ne'
      (by rwa [abs_of_pos ht])
    simp only [cexp, fexpOf, fltExp, lowerExponent] at hmag ⊢
    omega
  refine ⟨hcexp, ?_⟩
  have hpow := Flocq.bpow.pos binaryRadix fmt.minSubnormalExponent
  have hhalf : Flocq.bpow binaryRadix (lowerExponent fmt) =
      Flocq.bpow binaryRadix fmt.minSubnormalExponent / 2 := by
    rw [lowerExponent, Flocq.bpow_binaryRadix, Flocq.bpow_binaryRadix,
      zpow_sub_one₀ (two_ne_zero)]
    ring
  rw [scaledMantissa_eq_div, hcexp]
  have hlt : t / Flocq.bpow binaryRadix fmt.minSubnormalExponent < 1 / 2 := by
    rw [div_lt_iff₀ hpow]
    linarith
  refine .inexact .lt ⟨by simpa using div_pos ht hpow, by push_cast; linarith⟩
    ((cmp_eq_lt_iff _ _).mpr (by push_cast; linarith))

/-- A value in the lower half of the unit bracket above `mantissa`. -/
private theorem inbetweenInt_lt {mantissa : Nat} {w : ℝ} (hlower : (mantissa : ℝ) < w)
    (hupper : w < mantissa + 1 / 2) : InbetweenInt (mantissa : ℤ) w (.inexact .lt) :=
  .inexact .lt ⟨by simpa using hlower, by push_cast; linarith⟩
    ((cmp_eq_lt_iff _ _).mpr (by push_cast; linarith))

/-- The midpoint of the unit bracket above `mantissa`. -/
private theorem inbetweenInt_eq {mantissa : Nat} {w : ℝ} (hw : w = mantissa + 1 / 2) :
    InbetweenInt (mantissa : ℤ) w (.inexact .eq) :=
  .inexact .eq ⟨by push_cast; linarith, by push_cast; linarith⟩
    ((cmp_eq_eq_iff _ _).mpr (by push_cast; linarith))

/-- A value in the upper half of the unit bracket above `mantissa`. -/
private theorem inbetweenInt_gt {mantissa : Nat} {w : ℝ} (hlower : (mantissa : ℝ) + 1 / 2 < w)
    (hupper : w < mantissa + 1) : InbetweenInt (mantissa : ℤ) w (.inexact .gt) :=
  .inexact .gt ⟨by push_cast; linarith, by push_cast; linarith⟩
    ((cmp_eq_gt_iff _ _).mpr (by push_cast; linarith))

/--
Two bits below the last place and an exactness flag locate a scaled significand: the quotient by
four is the integer part, the upper bit the guard bit, and the lower bit or an inexact
truncation the sticky bit.
-/
theorem inbetweenInt_of_guarded (mantissa remainder : Nat) (v : ℝ) (exact : Bool)
    (hremainder : remainder < 4)
    (hlower : 4 * (mantissa : ℝ) + remainder ≤ v) (hupper : v < 4 * (mantissa : ℝ) + remainder + 1)
    (hexact : exact = true ↔ v = 4 * (mantissa : ℝ) + remainder) :
    InbetweenInt (mantissa : ℤ) (v / 4)
      (location (decide (2 ≤ remainder)) (remainder % 2 == 1 || !exact)) := by
  have hstrict : exact = false → 4 * (mantissa : ℝ) + remainder < v := fun hfalse =>
    lt_of_le_of_ne hlower fun heq => by simp [hexact.mpr heq.symm] at hfalse
  obtain rfl | rfl | rfl | rfl : remainder = 0 ∨ remainder = 1 ∨ remainder = 2 ∨ remainder = 3 := by
    omega
  · cases exact
    · have := hstrict rfl
      exact inbetweenInt_lt (by push_cast at this; linarith) (by push_cast at hupper; linarith)
    · have := hexact.mp rfl
      exact .exact (by push_cast at this ⊢; linarith)
  · have hloc : location (decide (2 ≤ 1)) (1 % 2 == 1 || !exact) = .inexact .lt := by
      cases exact <;> rfl
    rw [hloc]
    exact inbetweenInt_lt (by push_cast at hlower; linarith) (by push_cast at hupper; linarith)
  · cases exact
    · have := hstrict rfl
      exact inbetweenInt_gt (by push_cast at this; linarith) (by push_cast at hupper; linarith)
    · have := hexact.mp rfl
      exact inbetweenInt_eq (by push_cast at this; linarith)
  · have hloc : location (decide (2 ≤ 3)) (3 % 2 == 1 || !exact) = .inexact .gt := by
      cases exact <;> rfl
    rw [hloc]
    exact inbetweenInt_gt (by push_cast at hlower; linarith) (by push_cast at hupper; linarith)

/--
A magnitude in a binade whose scaled significand at the certificate exponent has the integer
part `mantissa` is located: the two low bits of `mantissa` are below the last place of the
format at that magnitude, and `exact` says that nothing was discarded.
-/
theorem located_of_truncated (fmt : FloatFormat) {t : ℝ} (ht : 0 < t) {binade : Int}
    (hblo : Flocq.bpow binaryRadix binade ≤ t)
    (hbhi : t < Flocq.bpow binaryRadix (binade + 1)) {mantissa : Nat} {exact : Bool}
    (hfloorLo : (mantissa : ℝ) ≤ t / Flocq.bpow binaryRadix (certificateExponent fmt binade))
    (hfloorHi : t / Flocq.bpow binaryRadix (certificateExponent fmt binade) < (mantissa : ℝ) + 1)
    (hexact : exact = true ↔
      t / Flocq.bpow binaryRadix (certificateExponent fmt binade) = (mantissa : ℝ)) :
    Located fmt t (mantissa / 4) (certificateExponent fmt binade + 2)
      (decide (2 ≤ mantissa % 4)) (mantissa % 2 == 1 || !exact) := by
  generalize hexponent : certificateExponent fmt binade = exponent at hfloorLo hfloorHi hexact ⊢
  have hmag : magnitude binaryRadix t = binade + 1 :=
    magnitude_eq_of_bpow_bounds _ _ _ (by simpa [abs_of_pos ht] using hblo)
      (by simpa [abs_of_pos ht] using hbhi)
  have hcexp : cexp binaryRadix (fexpOf fmt) t = exponent + 2 := by
    simp only [cexp, hmag, fexpOf, fltExp, ← hexponent, certificateExponent]
    omega
  refine ⟨hcexp, ?_⟩
  have hscale : t / Flocq.bpow binaryRadix (exponent + 2) =
      t / Flocq.bpow binaryRadix exponent / 4 := by
    rw [Flocq.bpow.add_exp, show Flocq.bpow binaryRadix 2 = 4 by
      norm_num [Flocq.bpow_binaryRadix], div_mul_eq_div_div]
  have hsplit : (mantissa : ℝ) = 4 * ((mantissa / 4 : ℕ) : ℝ) + ((mantissa % 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod mantissa 4).symm
  rw [scaledMantissa_eq_div, hcexp, hscale,
    ← Nat.mod_mod_of_dvd mantissa (by norm_num : 2 ∣ 4)]
  apply inbetweenInt_of_guarded _ _ _ _ (Nat.mod_lt _ (by norm_num))
  · rw [← hsplit]; exact hfloorLo
  · rw [← hsplit]; exact hfloorHi
  · rw [← hsplit]; exact hexact

/--
For a magnitude in the searched range, the truncated significand of the oracle locates it: its
two low bits are below the last place of the format at that magnitude.
-/
theorem located_of_certificate (fmt : FloatFormat) (compare : Rat → Ordering) (t : ℝ)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp t (candidate : ℝ))
    (hlower : Flocq.bpow binaryRadix (lowerExponent fmt) ≤ t)
    (hupper : t < Flocq.bpow binaryRadix (upperExponent fmt)) :
    Located fmt t (truncatedMantissa fmt compare (certificateExponent fmt (binade fmt compare)) / 4)
      (certificateExponent fmt (binade fmt compare) + 2)
      (decide (2 ≤ truncatedMantissa fmt compare
        (certificateExponent fmt (binade fmt compare)) % 4))
      (truncatedMantissa fmt compare (certificateExponent fmt (binade fmt compare)) % 2 == 1 ||
        !(compare ((truncatedMantissa fmt compare
          (certificateExponent fmt (binade fmt compare)) : Rat) *
            powerOfTwo (certificateExponent fmt (binade fmt compare))) == .eq)) := by
  have ht : 0 < t := (Flocq.bpow.pos _ _).trans_le hlower
  obtain ⟨hblo, hbhi⟩ := binade_bounds fmt compare t hcompare hlower hupper
  obtain ⟨hvlo, hvhi⟩ := certificate_scaled_bounds fmt compare t hcompare hlower hupper
  change 1 ≤ t / Flocq.bpow binaryRadix (certificateExponent fmt (binade fmt compare)) at hvlo
  change t / Flocq.bpow binaryRadix (certificateExponent fmt (binade fmt compare)) < _ at hvhi
  obtain ⟨hfloorLo, hfloorHi⟩ := truncatedMantissa_bounds fmt compare t _ hcompare
    (by linarith) hvhi
  refine located_of_truncated fmt ht hblo hbhi hfloorLo
    hfloorHi ?_
  rw [beq_iff_eq, hcompare, cmp_eq_eq_iff, div_eq_iff (Flocq.bpow.pos _ _).ne']
  push_cast [cast_powerOfTwo]
  rfl

/-- The accuracy class of a scaled significand is exact when the significand is its integer
part. -/
theorem accuracyQuarter_eq_zero_iff {mantissa : Nat}
    {accuracy : Float.Model.UnpackedFloat.Accuracy} {value : ℝ}
    (h : AccuracyRepresents mantissa accuracy value) :
    (accuracyQuarter accuracy == 0) = true ↔ value = (mantissa : ℝ) := by
  rcases accuracy with _ | (_ | _ | _) <;> simp only [AccuracyRepresents] at h
  · simpa [accuracyQuarter] using h
  · simpa [accuracyQuarter] using h.1.ne'
  · simp [accuracyQuarter, h]
  · simp only [accuracyQuarter, Nat.reduceBEq, Bool.false_eq_true, false_iff]
    intro heq
    linarith [h.1]

/--
The quarter-integer stand-in of a located magnitude is located at the same place. For a
magnitude `t` in a binade whose scaled significand at the certificate exponent has the integer
part `mantissa` and the accuracy class `accuracy`, the dyadic number
`(4 * mantissa + accuracyQuarter accuracy) * 2 ^ (exponent - 2)` lies in the same binade and has
the same integer part and class, so every direction rounds it as it rounds `t`.
-/
theorem located_of_quarter (fmt : FloatFormat) {t : ℝ} {binade : Int}
    (hbinade : lowerExponent fmt ≤ binade)
    (hblo : Flocq.bpow binaryRadix binade ≤ t)
    (hbhi : t < Flocq.bpow binaryRadix (binade + 1)) {mantissa : Nat}
    {accuracy : Float.Model.UnpackedFloat.Accuracy}
    (hrep : AccuracyRepresents mantissa accuracy
      (t / Flocq.bpow binaryRadix (certificateExponent fmt binade))) :
    Located fmt (((4 * mantissa + accuracyQuarter accuracy : ℕ) : ℝ) *
        Flocq.bpow binaryRadix (certificateExponent fmt binade - 2))
      (mantissa / 4) (certificateExponent fmt binade + 2) (decide (2 ≤ mantissa % 4))
      (mantissa % 2 == 1 || !(accuracyQuarter accuracy == 0)) := by
  obtain ⟨hlo, hhi⟩ := accuracyRepresents_bounds hrep
  have hquarter : accuracyQuarter accuracy ≤ 3 := by
    rcases accuracy with _ | (_ | _ | _) <;> simp [accuracyQuarter]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, binade = certificateExponent fmt binade + n := by
    refine ⟨(binade - certificateExponent fmt binade).toNat, ?_⟩
    simp only [certificateExponent, lowerExponent] at hbinade ⊢
    omega
  set exponent := certificateExponent fmt binade with hexponentDef
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hunit : (0 : ℝ) < (2 : ℝ) ^ (exponent - 2) := zpow_pos (by norm_num) _
  have hexponent : Flocq.bpow binaryRadix exponent = 4 * (2 : ℝ) ^ (exponent - 2) := by
    rw [Flocq.bpow_binaryRadix, zpow_sub₀ htwo]
    norm_num
    field_simp
  have hlowerPower : Flocq.bpow binaryRadix binade =
      4 * (2 : ℝ) ^ n * (2 : ℝ) ^ (exponent - 2) := by
    rw [Flocq.bpow_binaryRadix, hn, zpow_add₀ htwo, zpow_natCast, zpow_sub₀ htwo]
    norm_num
    field_simp
  have hupperPower : Flocq.bpow binaryRadix (binade + 1) =
      8 * (2 : ℝ) ^ n * (2 : ℝ) ^ (exponent - 2) := by
    rw [Flocq.bpow_binaryRadix, hn, zpow_add₀ htwo, zpow_add₀ htwo, zpow_natCast, zpow_one,
      zpow_sub₀ htwo]
    norm_num
    field_simp
    ring
  rw [hexponent] at hlo hhi
  rw [le_div_iff₀ (by positivity)] at hlo
  rw [div_lt_iff₀ (by positivity)] at hhi
  rw [hlowerPower] at hblo
  rw [hupperPower] at hbhi
  have hbelow : 2 ^ n ≤ mantissa := by
    have h : (4 * (2 : ℝ) ^ n) * (2 : ℝ) ^ (exponent - 2) <
        (4 * ((mantissa : ℝ) + 1)) * (2 : ℝ) ^ (exponent - 2) := by
      linarith
    have h := lt_of_mul_lt_mul_right h hunit.le
    have hcast : ((2 ^ n : ℕ) : ℝ) < ((mantissa + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp hcast)
  have habove : mantissa + 1 ≤ 2 * 2 ^ n := by
    have h : (4 * (mantissa : ℝ)) * (2 : ℝ) ^ (exponent - 2) <
        (8 * (2 : ℝ) ^ n) * (2 : ℝ) ^ (exponent - 2) := by
      linarith
    have h := lt_of_mul_lt_mul_right h hunit.le
    have hcast : ((mantissa : ℕ) : ℝ) < ((2 * 2 ^ n : ℕ) : ℝ) := by
      push_cast
      linarith
    exact Nat.cast_lt.mp hcast
  have hratio : ((4 * mantissa + accuracyQuarter accuracy : ℕ) : ℝ) *
        Flocq.bpow binaryRadix (exponent - 2) / Flocq.bpow binaryRadix exponent =
        ((4 * mantissa + accuracyQuarter accuracy : ℕ) : ℝ) / 4 := by
    rw [hexponent, Flocq.bpow_binaryRadix]
    field_simp
  have hpositive : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
  refine located_of_truncated fmt ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Flocq.bpow_binaryRadix]
    have : (0 : ℝ) < ((4 * mantissa + accuracyQuarter accuracy : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 4 * mantissa + accuracyQuarter accuracy)
    positivity
  · rw [hlowerPower, Flocq.bpow_binaryRadix]
    refine mul_le_mul_of_nonneg_right ?_ hunit.le
    have : 4 * 2 ^ n ≤ 4 * mantissa + accuracyQuarter accuracy := by omega
    exact_mod_cast this
  · rw [hupperPower, Flocq.bpow_binaryRadix]
    refine mul_lt_mul_of_pos_right ?_ hunit
    have : 4 * mantissa + accuracyQuarter accuracy < 8 * 2 ^ n := by omega
    exact_mod_cast this
  · rw [hratio, le_div_iff₀ (by norm_num)]
    push_cast
    linarith [(Nat.cast_nonneg (accuracyQuarter accuracy) : (0 : ℝ) ≤ _)]
  · rw [hratio, div_lt_iff₀ (by norm_num)]
    have : ((accuracyQuarter accuracy : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hquarter
    push_cast
    linarith
  · rw [hratio, div_eq_iff (by norm_num), beq_iff_eq]
    constructor
    · intro hzero
      rw [hzero]
      push_cast
      ring
    · intro hvalue
      have : ((4 * mantissa + accuracyQuarter accuracy : ℕ) : ℝ) = ((4 * mantissa : ℕ) : ℝ) := by
        push_cast at hvalue ⊢
        linarith
      have := Nat.cast_injective this
      omega

/-! ## Rounding the magnitude and the signed value of an oracle -/

/-- A real of magnitude at least a power of two on the grid rounds to at least that power. -/
theorem bpow_le_abs_roundAt (fmt : FloatFormat) (mode : IEEERoundingMode) {x : ℝ} {e : ℤ}
    (he : fmt.minSubnormalExponent ≤ e) (hx : Flocq.bpow binaryRadix e ≤ |x|) :
    Flocq.bpow binaryRadix e ≤ |roundAt fmt x mode| := by
  have hpositive (mode : IEEERoundingMode) {y : ℝ} (hy : Flocq.bpow binaryRadix e ≤ y) :
      Flocq.bpow binaryRadix e ≤ roundAt fmt y mode := by
    have h := roundAt_mono fmt hy mode
    rwa [roundAt_of_genericFormat fmt (genericFormat_bpow fmt he) mode] at h
  rcases le_total 0 x with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg] at hx
    exact (hpositive mode hx).trans (le_abs_self _)
  · rw [abs_of_nonpos hnonpos] at hx
    have h := hpositive mode.negate hx
    rw [← _root_.neg_neg x, roundAt_neg fmt (-x) mode, abs_neg]
    exact h.trans (le_abs_self _)

/--
`roundMagnitude` rounds a positive magnitude given by an exact oracle, with either sign, in
every direction and for every format descriptor. No premise restricts the magnitude: it may
underflow, overflow or lie on a rounding boundary.
-/
theorem roundMagnitude_roundsTo {fmt : FloatFormat}
    (mode : IEEERoundingMode) (sign : Bool) (compare : Rat → Ordering) {t : ℝ} (ht : 0 < t)
    (hcompare : ∀ candidate : Rat, compare candidate = cmp t (candidate : ℝ)) :
    RoundsTo fmt mode (if sign then -t else t) sign (roundMagnitude fmt mode sign compare) := by
  by_cases hlarge : compare (powerOfTwo (upperExponent fmt)) ≠ .lt
  · rw [roundMagnitude_eq fmt mode sign hcompare, ite_eq_left hlarge]
    have hge : Flocq.bpow binaryRadix (upperExponent fmt) ≤ t := by
      simpa only [hcompare, cast_powerOfTwo, ne_eq, cmp_eq_lt_iff, not_lt] using hlarge
    have hbeyond : toReal (posMaxFinite fmt) <
        |roundAt fmt (if sign then -t else t) mode| := by
      apply (toReal_posMaxFinite_lt_bpow fmt).trans_le
      apply bpow_le_abs_roundAt fmt mode
      · have := lowerExponent_lt_upperExponent fmt
        simp only [lowerExponent, upperExponent] at this ⊢
        omega
      · cases sign <;> simpa [abs_of_pos ht, upperExponent] using hge
    exact ⟨fun hin => absurd hbeyond (not_lt.mpr hin), fun _ => rfl,
      fun hzero => signBit_directedOverflow hzero sign _⟩
  · have hlt : t < Flocq.bpow binaryRadix (upperExponent fmt) :=
      lt_bpow_upperExponent_of_compare_eq_lt fmt hcompare (by simpa only [not_not] using hlarge)
    by_cases hsmall : compare (powerOfTwo (lowerExponent fmt)) = .lt
    · rw [roundMagnitude_eq fmt mode sign hcompare, ite_eq_right hlarge,
        ite_eq_left hsmall]
      exact roundLocated_roundsTo (located_of_lt_lowerExponent fmt ht
        (by simpa only [hcompare, cast_powerOfTwo, cmp_eq_lt_iff] using hsmall)) mode sign
    · rw [roundMagnitude_eq fmt mode sign hcompare, ite_eq_right hlarge,
        ite_eq_right hsmall]
      exact roundLocated_roundsTo (located_of_certificate fmt compare t
        hcompare (by simpa only [hcompare, cast_powerOfTwo, cmp_eq_lt_iff, not_lt] using hsmall)
        hlt) mode sign

/-! ## Negation -/

/-- The overflow result of a negative sign is the negation of the positive one. -/
theorem directedOverflow_true_eq_neg (fmt : FloatFormat) (roundMagnitudeUp : Bool) :
    directedOverflow fmt true roundMagnitudeUp =
      neg (directedOverflow fmt false roundMagnitudeUp) := by
  cases roundMagnitudeUp <;> simp [directedOverflow, nativeOverflow_true_eq_neg_false]

/--
Delivering a grid magnitude with a negative sign negates its delivery with a positive sign in the
mirrored direction.
-/
theorem packGrid_true_eq_neg {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (mode : IEEERoundingMode) (mantissa : Nat) (exponent : Int) :
    packGrid fmt mode true mantissa exponent =
      neg (packGrid fmt mode.negate false mantissa exponent) := by
  unfold packGrid
  rw [IEEERoundingMode.overflowRoundsMagnitudeUp_negate]
  split
  · simp [zero]
  · split
    · exact directedOverflow_true_eq_neg fmt _
    · exact roundRatScaled_true_eq_neg_false fmt mantissa 1 exponent hfmt one_ne_zero

/--
Rounding a magnitude with a negative sign negates its rounding with a positive sign in the
mirrored direction.
-/
theorem roundMagnitude_true_eq_neg {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (mode : IEEERoundingMode) (compare : Rat → Ordering) :
    roundMagnitude fmt mode true compare =
      neg (roundMagnitude fmt mode.negate false compare) := by
  have hlocated (mantissa : Nat) (exponent : Int) (guard sticky : Bool) :
      roundLocated fmt mode true mantissa exponent guard sticky =
        neg (roundLocated fmt mode.negate false mantissa exponent guard sticky) := by
    unfold roundLocated
    rw [IEEERoundingMode.magnitudeRounding_negate]
    exact packGrid_true_eq_neg hfmt mode _ _
  simp only [roundMagnitude, IEEERoundingMode.overflowRoundsMagnitudeUp_negate]
  split
  · exact directedOverflow_true_eq_neg fmt _
  · split
    · exact hlocated _ _ _ _
    · exact hlocated _ _ _ _

/--
Rounding from the mirrored oracle, which orders `-x`, negates the rounding of `x` in the mirrored
direction `mode.negate`, and the sign of an exact zero flips.
-/
theorem roundSigned_neg {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (compare : Rat → Ordering) (zeroSign : Bool) :
    roundSigned fmt mode (fun boundary => (compare (-boundary)).swap) (!zeroSign) =
      neg (roundSigned fmt mode.negate compare zeroSign) := by
  have hsigned := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  unfold roundSigned
  simp only [neg_zero]
  cases hzero : compare 0 with
  | eq =>
      cases zeroSign
      · simp [zero, hsigned]
      · simp [zero, hsigned, neg_negZero_of_supportsSignedZero fmt hsigned]
  | gt =>
      change roundMagnitude fmt mode true (fun boundary => ((compare (- -boundary)).swap).swap) =
        neg (roundMagnitude fmt mode.negate false compare)
      rw [show (fun boundary => ((compare (- -boundary)).swap).swap) = compare by
        funext boundary
        simp]
      exact roundMagnitude_true_eq_neg hfmt mode compare
  | lt =>
      change roundMagnitude fmt mode false (fun boundary => (compare (-boundary)).swap) =
        neg (roundMagnitude fmt mode.negate true (fun boundary => (compare (-boundary)).swap))
      rw [roundMagnitude_true_eq_neg hfmt mode.negate, neg_neg, IEEERoundingMode.negate_negate]

end AlgebraicRounding

/--
The rounding of the real `x` to the format `fmt` in the direction `mode`: the specification of a
correctly rounded operation, with the overflow results of IEEE 754-2019, clause 7.4
(`roundReal_roundsTo`). A zero `x` gives the zero with the sign `zeroSign`.

It is `AlgebraicRounding.roundSigned` on the comparisons of `x` itself, which no program can
evaluate. An executable oracle that agrees with those comparisons computes the same encoding
(`AlgebraicRounding.roundSigned_eq_roundReal`).
-/
noncomputable def roundReal (fmt : FloatFormat) (mode : IEEERoundingMode) (x : ℝ)
    (zeroSign : Bool := false) : Model fmt :=
  AlgebraicRounding.roundSigned fmt mode (fun boundary : Rat => cmp x (boundary : ℝ)) zeroSign

/-- An executable oracle that orders `x` against every rational rounds to `roundReal`. -/
theorem AlgebraicRounding.roundSigned_eq_roundReal (fmt : FloatFormat) (mode : IEEERoundingMode)
    {compare : Rat → Ordering} {x : ℝ}
    (hcompare : ∀ candidate : Rat, compare candidate = cmp x (candidate : ℝ))
    (zeroSign : Bool := false) :
    AlgebraicRounding.roundSigned fmt mode compare zeroSign = roundReal fmt mode x zeroSign := by
  rw [roundReal, show compare = fun boundary : Rat => cmp x (boundary : ℝ) from funext hcompare]

/-- A real zero rounds to the zero of the requested sign in every direction. -/
@[simp] theorem roundReal_zero (fmt : FloatFormat) (mode : IEEERoundingMode) (zeroSign : Bool) :
    roundReal fmt mode 0 zeroSign = zero fmt zeroSign := by
  simp [roundReal, AlgebraicRounding.roundSigned]

/--
For every format descriptor, `roundReal` of a nonzero real is its rounding in the sense of
IEEE 754-2019, clauses 4.3 and 7.4: the grid rounding `roundAt fmt x mode` when that is at most
the largest finite magnitude, the overflow result of the direction otherwise (the NaN of a
format without an infinity when the direction rounds away), and in a format with signed zeros
the sign bit of `x` in both cases.
-/
theorem roundReal_roundsTo {fmt : FloatFormat}
    (mode : IEEERoundingMode) {x : ℝ} (hx : x ≠ 0) (zeroSign : Bool := false) :
    RoundsTo fmt mode x (decide (x < 0)) (roundReal fmt mode x zeroSign) := by
  unfold roundReal AlgebraicRounding.roundSigned
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hcmp : cmp x ((0 : Rat) : ℝ) = .lt := (cmp_eq_lt_iff _ _).mpr (by simpa using hneg)
    simp only [hcmp, decide_eq_true hneg]
    have h := AlgebraicRounding.roundMagnitude_roundsTo (fmt := fmt) mode true
      (fun boundary : Rat => (cmp x ((-boundary : Rat) : ℝ)).swap) (neg_pos.mpr hneg)
      (fun candidate => by
        rw [cmp_swap]
        push_cast
        simp only [cmp, cmpUsing, neg_lt, lt_neg])
    simpa using h
  · have hcmp : cmp x ((0 : Rat) : ℝ) = .gt := (cmp_eq_gt_iff _ _).mpr (by simpa using hpos)
    simp only [hcmp, decide_eq_false (not_lt.mpr hpos.le)]
    simpa using AlgebraicRounding.roundMagnitude_roundsTo (fmt := fmt) mode false
      (fun boundary : Rat => cmp x (boundary : ℝ)) hpos (fun _ => rfl)

/--
For an IEEE descriptor, rounding `-x` negates the rounding of `x` in the mirrored direction
`mode.negate`, which exchanges `up` and `down` and fixes the other four, with the opposite sign
of an exact zero. It is `roundAt_neg` with the overflow results and the signs of zero.
-/
theorem roundReal_neg {fmt : FloatFormat} (hfmt : fmt.isIEEE = true) (mode : IEEERoundingMode)
    (x : ℝ) (zeroSign : Bool) :
    roundReal fmt mode (-x) (!zeroSign) = neg (roundReal fmt mode.negate x zeroSign) := by
  rw [roundReal, roundReal, ← AlgebraicRounding.roundSigned_neg hfmt mode]
  congr 1
  funext boundary
  rw [cmp_swap]
  push_cast
  simp only [cmp, cmpUsing, neg_lt, lt_neg]

end FloatLib.Floats.Formats.BinaryInterchange.Model
