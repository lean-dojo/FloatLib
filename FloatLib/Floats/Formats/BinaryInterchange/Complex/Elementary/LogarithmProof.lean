/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Logarithm
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.SmallProof
public import FloatLib.Numerics.Exact.Elementary.Proof
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Proof

/-!
# Correct rounding of the complex logarithm and inverse tangents

For an IEEE descriptor, each part of `ExecComplex.log`, `log1p`, `atanh` and `atan` at a finite
argument away from the poles is the exact part rounded once in the requested direction:

* `log_eq`: the principal logarithm `Complex.log`, at every finite nonzero argument;
* `log1p_eq`: `Complex.log (1 + w)`, at every finite nonzero argument other than `-1`;
* `atanh_eq`: the inverse hyperbolic tangent, at every finite argument other than `±1`;
* `atan_eq`: `-i atanh (i w)`, at every finite argument other than `±i`.

No premise restricts the argument further: the comparisons behind the rounding are the total
exact comparators `prepareLog` and `prepareAtan2`, so results that underflow, results near a
rounding boundary and arguments of any magnitude are covered.

The finite arguments that those theorems exclude have their own: `log_zero` (the pole
`-∞ + i arg`, C23 G.6.4.2), `log1p_zero` (a zero is returned unchanged), `log1p_neg_one`,
`atanh_one` and `atanh_neg_one` (the poles `±∞ ± 0 i`, G.6.3.3), `atan_I` and `atan_neg_I`. So
every finite argument of the four functions is covered by a theorem. These hold for every
descriptor.

The exact results are stated where the sign bits are clear and extended by the symmetries of
C23 G.6 (`Exact.ofUpperHalf`, `Exact.ofQuadrant`). For `atanh` the first-quadrant value is the
closed form `log (|1 + w|² / |1 - w|²) / 4 + i arg (1 - |w|² + 2 i im w) / 2`, which is
`(log (1 + w) - log (1 - w)) / 2` and takes the value above the cut for a real `w > 1`
(C23 7.3.3).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-- Comparing with a positive multiple of a boundary compares the quotient with the boundary. -/
theorem cmp_mul_eq_cmp_div (v : ℝ) {scale : Rat} (hscale : 0 < scale) (boundary : Rat) :
    cmp v ((scale * boundary : Rat) : ℝ) = cmp (v / scale) (boundary : ℝ) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  push_cast
  simp only [cmp, cmpUsing, div_lt_iff₀ hs, lt_div_iff₀ hs, mul_comm]

/-- The table-reduced enclosure of the logarithm of a positive rational contains it. -/
theorem contains_ratLogEnclosure {q : Rat} (hq : 0 < q) (precision : Nat) :
    (ratLogEnclosure q precision).Contains (Real.log (q : ℝ)) := by
  obtain ⟨hsplit, hvalue⟩ := Model.Transcendentals.Certified.splitTwoPow_spec hq
  have h := Model.Transcendentals.CorrectlyRounded.contains_logEnclosure hsplit
    (Model.Transcendentals.Certified.splitTwoPow q).2 precision
  rwa [hvalue] at h

/-- `coarseLog` contains the logarithm of a positive rational. -/
theorem contains_coarseLog {q : Rat} (hq : 0 < q) (precision : Nat) :
    (coarseLog q precision).Contains (Real.log (q : ℝ)) := by
  unfold coarseLog
  obtain ⟨hlo, hhi⟩ := dyadicAround_bounds q (precision + 8)
  split
  · rename_i hlong
    have hpositive := hlong.2
    have hloR : ((dyadicAround q (precision + 8)).lo : ℝ) ≤ (q : ℝ) := by exact_mod_cast hlo
    have hhiR : (q : ℝ) ≤ ((dyadicAround q (precision + 8)).hi : ℝ) := by exact_mod_cast hhi
    exact ⟨(contains_ratLogEnclosure hpositive precision).1.trans
        (Real.log_le_log (by exact_mod_cast hpositive) hloR),
      (Real.log_le_log (by exact_mod_cast hq) hhiR).trans
        (contains_ratLogEnclosure (hq.trans_le hhi) precision).2⟩
  · exact contains_ratLogEnclosure hq precision

/-- `coarseAtan` contains the arctangent of the slope. -/
theorem contains_coarseAtan (slope : Rat) (precision : Nat) :
    (coarseAtan slope precision).Contains (Real.arctan (slope : ℝ)) := by
  unfold coarseAtan
  split
  · obtain ⟨hlo, hhi⟩ := dyadicAround_bounds slope (precision + 8)
    exact ⟨(Enclosure.contains_atan _ _).1.trans
        (Real.arctan_strictMono.monotone (by exact_mod_cast hlo)),
      (Real.arctan_strictMono.monotone (by exact_mod_cast hhi)).trans
        (Enclosure.contains_atan _ _).2⟩
  · exact Enclosure.contains_atan slope _

/-- `coarseArg` contains the principal argument. -/
theorem contains_coarseArg (x y : Rat) (precision : Nat) :
    (coarseArg x y precision).Contains (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩) := by
  unfold coarseArg
  rw [← TrigonometricComparison.atan2Reduction_eq_arg]
  exact RationalInterval.contains_add (contains_coarseAtan _ precision)
    (RationalInterval.contains_scale (Enclosure.contains_piQuarter (precision / 2))
      (TrigonometricComparison.atan2Reduction x y).2)

/-- `logPart` is an oracle for `log q / scale`. -/
theorem logPart_denotes {q scale : Rat} (hq : 0 < q) (hscale : 0 < scale) :
    (logPart fmt q scale).Denotes (Real.log (q : ℝ) / scale) false := by
  rw [logPart, dite_eq_left hq]
  have hexact : (Part.real (fmt := fmt) (fun boundary =>
      (ElementaryComparison.prepareLog q (cacheLevels fmt) hq).compare (scale * boundary))
      false).Denotes (Real.log (q : ℝ) / scale) false :=
    ⟨_, rfl, fun boundary => by
      rw [ElementaryComparison.prepareLog_eq_real, cmp_mul_eq_cmp_div _ hscale]⟩
  refine hexact.within (contains_orElse (fun interval hinterval => ?_)
    (contains_of_refineTwice fun precision interval hinterval => ?_))
  · obtain ⟨small, hsmall, rfl⟩ := Option.map_eq_some_iff.mp hinterval
    have h := Numerics.RationalInterval.contains_scale (contains_smallLog? hsmall) (1 / scale)
    convert h using 1
    push_cast
    ring
  · have h := Numerics.RationalInterval.contains_scale (contains_coarseLog hq precision)
      (1 / scale)
    rw [← Option.some.inj hinterval]
    convert h using 1
    push_cast
    ring

/-- `argPart` is an oracle for `arg (x + i y) / scale`. -/
theorem argPart_denotes (x y : Rat) {scale : Rat} (hscale : 0 < scale) :
    (argPart fmt x y scale).Denotes (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ / scale) false := by
  have hexact : (Part.real (fmt := fmt) (fun boundary =>
      (TrigonometricComparison.prepareAtan2 x y (cacheLevels fmt)).compare (scale * boundary))
      false).Denotes (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ / scale) false :=
    ⟨_, rfl, fun boundary => by
      rw [TrigonometricComparison.prepareAtan2_eq_real, cmp_mul_eq_cmp_div _ hscale]⟩
  refine hexact.within (contains_orElse (fun interval hinterval => ?_)
    (contains_of_refineTwice fun precision interval hinterval => ?_))
  · obtain ⟨small, hsmall, rfl⟩ := Option.map_eq_some_iff.mp hinterval
    have h := Numerics.RationalInterval.contains_scale (contains_smallArg? hsmall) (1 / scale)
    convert h using 1
    push_cast
    ring
  · have h := Numerics.RationalInterval.contains_scale
      (contains_coarseArg x y precision) (1 / scale)
    rw [← Option.some.inj hinterval]
    convert h using 1
    push_cast
    ring

/-- The parts of `logRat` are the principal logarithm of a nonzero complex rational. -/
theorem logRat_denotes {x y : Rat} (hne : ¬(x = 0 ∧ y = 0)) :
    (logRat fmt x y).Denotes ⟨Complex.log ⟨(x : ℝ), (y : ℝ)⟩, false, false⟩ := by
  have hq : 0 < x * x + y * y := by
    rcases lt_or_eq_of_le (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y)) with h | h
    · exact h
    · exact absurd ⟨by nlinarith [mul_self_nonneg x, mul_self_nonneg y],
        by nlinarith [mul_self_nonneg x, mul_self_nonneg y]⟩ hne
  refine ⟨?_, ?_⟩
  · have h := logPart_denotes (fmt := fmt) hq (by norm_num : (0 : Rat) < 2)
    have hnorm : ‖(⟨(x : ℝ), (y : ℝ)⟩ : ℂ)‖ = √((x * x + y * y : Rat) : ℝ) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      push_cast
      ring_nf
    rw [show (Complex.log ⟨(x : ℝ), (y : ℝ)⟩).re =
        Real.log ((x * x + y * y : Rat) : ℝ) / (2 : Rat) by
      rw [Complex.log_re, hnorm, Real.log_sqrt (by exact_mod_cast hq.le)]
      norm_num]
    exact h
  · simpa [Complex.log_im, logRat] using
      argPart_denotes (fmt := fmt) x y (by norm_num : (0 : Rat) < 1)

/--
The exact result of `clog` at a finite nonzero argument: the principal logarithm where the
imaginary sign bit is clear, its conjugate elsewhere, and positive zeros there.
-/
noncomputable def logExact : ExecComplex fmt → Exact :=
  Exact.ofUpperHalf fun z => ⟨Complex.log (toComplex z), false, false⟩

/-- At a finite nonzero argument the parts of `logCore` are the principal logarithm. -/
theorem logCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true) (hne : toComplex z ≠ 0) :
    (logCore z).Denotes ⟨Complex.log (toComplex z), false, false⟩ := by
  obtain ⟨x, y, hx, hy, hw, -⟩ := exists_toRat?_of_isFinite hz
  have hxy : ¬(x = 0 ∧ y = 0) := fun h => hne (by rw [hw, h.1, h.2]; simp [Complex.ext_iff])
  simp only [logCore, hx, hy, hxy, ↓reduceIte, hw]
  exact logRat_denotes hxy

/--
For an IEEE descriptor, `log` of a finite nonzero argument is the principal logarithm with each
part rounded once in the direction `mode`.
-/
theorem log_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (mode : Model.IEEERoundingMode := .nearest) :
    log z mode = (logExact z).round fmt mode :=
  (Parts.ofUpperHalf_denotes hfmt (fun ζ => toComplex ζ ≠ 0)
    (fun ζ hζ hd => by rwa [toComplex_conj ζ hζ, ne_eq, map_eq_zero])
    (fun _ hζ hd _ => logCore_denotes hζ hd) hz hne).round mode

/--
`log` at a zero is the pole of C23 G.6.4.2 with the angle of the zero: `log (+0 ± 0 i) = -∞ ± 0 i`
and `log (-0 ± 0 i) = -∞ ± π i`, with `π` rounded once in the direction `mode`.
-/
theorem log_zero {z : ExecComplex fmt} (hz : isFinite z = true) (hzero : toComplex z = 0)
    (mode : Model.IEEERoundingMode := .nearest) :
    log z mode = ⟨Model.negInf fmt, Model.roundReal fmt mode
      (if Model.signBit z.re then (if Model.signBit z.im then -Real.pi else Real.pi) else 0)
      (Model.signBit z.im)⟩ := by
  have hcore (ζ : ExecComplex fmt) (hζ : isFinite ζ = true) (h0 : toComplex ζ = 0) :
      logCore ζ = ⟨.exact (Model.negInf fmt),
        argPart fmt (if Model.signBit ζ.re then -1 else 1) 0 1⟩ := by
    obtain ⟨hx, hy⟩ := toRat?_of_toComplex_eq (a := 0) (b := 0) hζ
      (by rw [h0]; apply Complex.ext <;> simp)
    simp [logCore, hx, hy]
  have harg (s : Bool) : (argPart fmt (if s then -1 else 1) 0 1).Denotes
      (if s then Real.pi else 0) false := by
    have h := argPart_denotes (fmt := fmt) (if s then -1 else 1) 0 one_pos
    cases s
    · simpa [show (⟨1, 0⟩ : ℂ) = 1 from rfl] using h
    · simpa [show (⟨-1, 0⟩ : ℂ) = -1 from by apply Complex.ext <;> simp] using h
  unfold log logParts Parts.ofUpperHalf
  cases him : Model.signBit z.im with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hcore z hz hzero, Parts.round, (harg _).round mode]
      cases hre : Model.signBit z.re <;> simp [Part.round]
  | true =>
      simp only [↓reduceIte]
      rw [hcore _ (isFinite_conj hz) (by rw [toComplex_conj z hz, hzero, map_zero]), Parts.conj,
        Parts.round, (harg _).neg.round mode]
      cases hre : Model.signBit z.re <;> simp [Part.round, ExecComplex.conj, hre]

/--
The exact result of `log1p` at a finite argument other than `0` and `-1`: the principal logarithm
of `1 + w` where the imaginary sign bit is clear, and its conjugate elsewhere.
-/
noncomputable def log1pExact : ExecComplex fmt → Exact :=
  Exact.ofUpperHalf fun z => ⟨Complex.log (1 + toComplex z), false, false⟩

/-- At a finite argument other than `0` and `-1` the parts of `log1pCore` are `log (1 + w)`. -/
theorem log1pCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (hpole : 1 + toComplex z ≠ 0) :
    (log1pCore z).Denotes ⟨Complex.log (1 + toComplex z), false, false⟩ := by
  obtain ⟨x, y, hx, hy, hw, -⟩ := exists_toRat?_of_isFinite hz
  have hxy : ¬(x = 0 ∧ y = 0) := fun h => hne (by rw [hw, h.1, h.2]; simp [Complex.ext_iff])
  have hsum : (1 : ℂ) + ⟨(x : ℝ), (y : ℝ)⟩ = ⟨((1 + x : Rat) : ℝ), (y : ℝ)⟩ := by
    apply Complex.ext <;> simp
  have hxy1 : ¬(1 + x = 0 ∧ y = 0) := fun h => hpole (by
    rw [hw, hsum, h.1, h.2]
    simp [Complex.ext_iff])
  simp only [log1pCore, hx, hy, hxy, hxy1, ↓reduceIte, hw, hsum]
  exact logRat_denotes hxy1

/--
For an IEEE descriptor, `log1p` of a finite argument other than `0` and `-1` is the principal
logarithm of the exact sum `1 + w` with each part rounded once in the direction `mode`.
-/
theorem log1p_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (hne : toComplex z ≠ 0) (hpole : 1 + toComplex z ≠ 0)
    (mode : Model.IEEERoundingMode := .nearest) :
    log1p z mode = (log1pExact z).round fmt mode :=
  (Parts.ofUpperHalf_denotes hfmt (fun ζ => toComplex ζ ≠ 0 ∧ 1 + toComplex ζ ≠ 0)
    (fun ζ hζ hd => by
      rw [toComplex_conj ζ hζ]
      refine ⟨by simpa using hd.1, fun h => hd.2 ?_⟩
      simpa using congrArg (starRingEnd ℂ) h)
    (fun _ hζ hd _ => log1pCore_denotes hζ hd.1 hd.2) hz ⟨hne, hpole⟩).round mode

/-- `log1p` returns a zero argument unchanged, with both signs. -/
theorem log1p_zero {z : ExecComplex fmt} (hz : isFinite z = true) (hzero : toComplex z = 0)
    (mode : Model.IEEERoundingMode := .nearest) : log1p z mode = z := by
  have hcore (ζ : ExecComplex fmt) (hζ : isFinite ζ = true) (h0 : toComplex ζ = 0) :
      log1pCore ζ = ⟨.exact ζ.re, .exact ζ.im⟩ := by
    obtain ⟨hx, hy⟩ := toRat?_of_toComplex_eq (a := 0) (b := 0) hζ
      (by rw [h0]; apply Complex.ext <;> simp)
    simp [log1pCore, hx, hy]
  unfold log1p log1pParts Parts.ofUpperHalf
  split
  · rw [hcore _ (isFinite_conj hz) (by rw [toComplex_conj z hz, hzero, map_zero])]
    simp [Parts.conj, Parts.round, Part.round, Part.neg, ExecComplex.conj]
  · rw [hcore z hz hzero]
    rfl

/-- `log1p` at `-1` is the pole of `clog` at a positive zero: `log1p (-1 ± 0 i) = -∞ ± 0 i`. -/
theorem log1p_neg_one {z : ExecComplex fmt} (hz : isFinite z = true)
    (hpole : toComplex z = -1) (mode : Model.IEEERoundingMode := .nearest) :
    log1p z mode = ⟨Model.negInf fmt, Model.zero fmt (Model.signBit z.im)⟩ := by
  have hcore (ζ : ExecComplex fmt) (hζ : isFinite ζ = true) (h1 : toComplex ζ = -1) :
      log1pCore ζ = ⟨.exact (Model.negInf fmt), .exact (Model.zero fmt false)⟩ := by
    obtain ⟨hx, hy⟩ := toRat?_of_toComplex_eq (a := -1) (b := 0) hζ
      (by rw [h1]; apply Complex.ext <;> simp)
    simp [log1pCore, hx, hy]
  unfold log1p log1pParts Parts.ofUpperHalf
  cases him : Model.signBit z.im with
  | false => simp [hcore z hz hpole, Parts.round, Part.round]
  | true =>
      simp [hcore _ (isFinite_conj hz) (by rw [toComplex_conj z hz, hpole]; simp), Parts.conj,
        Parts.round, Part.round, Part.neg, Model.zero]

/--
The inverse hyperbolic tangent of a complex number in closed form:
`log (|1 + w|² / |1 - w|²) / 4 + i arg (1 - |w|² + 2 i im w) / 2`.

It is `(log (1 + w) - log (1 - w)) / 2` off the real axis and between `-1` and `1`. At a real
`w` beyond `±1` it is the value on the upper side of the cut for `w > 1`, imaginary part `π / 2`.
-/
noncomputable def atanhValue (w : ℂ) : ℂ :=
  ⟨Real.log (((1 + w.re) * (1 + w.re) + w.im * w.im) /
      ((1 - w.re) * (1 - w.re) + w.im * w.im)) / 4,
    Complex.arg ⟨(1 - w.re) * (1 + w.re) - w.im * w.im, 2 * w.im⟩ / 2⟩

/--
The exact result of `catanh` at a finite argument other than `±1`: `atanhValue` where both sign
bits are clear, extended as an odd function that commutes with conjugation.
-/
noncomputable def atanhExact : ExecComplex fmt → Exact :=
  Exact.ofQuadrant true fun z => ⟨atanhValue (toComplex z), false, false⟩

/-- At a finite argument other than `±1` the parts of `atanhCore` are `atanhValue`. -/
theorem atanhCore_denotes {z : ExecComplex fmt} (hz : isFinite z = true)
    (hpos : toComplex z ≠ 1) (hneg : toComplex z ≠ -1) :
    (atanhCore z).Denotes ⟨atanhValue (toComplex z), false, false⟩ := by
  obtain ⟨x, y, hx, hy, hw, -⟩ := exists_toRat?_of_isFinite hz
  have hxy : ¬(x = 1 ∧ y = 0) := fun h => hpos (by rw [hw, h.1, h.2]; simp [Complex.ext_iff])
  have hxy' : ¬(x = -1 ∧ y = 0) := fun h => hneg (by rw [hw, h.1, h.2]; simp [Complex.ext_iff])
  have hsq (a : Rat) (ha : ¬(a = 0 ∧ y = 0)) : 0 < a * a + y * y := by
    rcases lt_or_eq_of_le (add_nonneg (mul_self_nonneg a) (mul_self_nonneg y)) with h | h
    · exact h
    · exact absurd ⟨by nlinarith [mul_self_nonneg a, mul_self_nonneg y],
        by nlinarith [mul_self_nonneg a, mul_self_nonneg y]⟩ ha
  have hnum := hsq (1 + x) fun h => hxy' ⟨by linarith [h.1], h.2⟩
  have hden := hsq (1 - x) fun h => hxy ⟨by linarith [h.1], h.2⟩
  simp only [atanhCore, hx, hy, hxy, ↓reduceIte, hw, atanhValue]
  refine ⟨?_, ?_⟩
  · have h := logPart_denotes (fmt := fmt) (div_pos hnum hden) (by norm_num : (0 : Rat) < 4)
    push_cast at h
    exact h
  · have h := argPart_denotes (fmt := fmt) ((1 - x) * (1 + x) - y * y) (2 * y)
      (by norm_num : (0 : Rat) < 2)
    push_cast at h
    exact h

/-- Negating the real part of a finite complex value negates the real part it denotes. -/
theorem toComplex_neg_re {z : ExecComplex fmt} (hz : isFinite z = true) :
    toComplex (⟨Model.neg z.re, z.im⟩ : ExecComplex fmt) =
      ⟨-(toComplex z).re, (toComplex z).im⟩ := by
  rw [toComplex, Model.toReal_neg _ ((isFinite_eq_true_iff z).1 hz).1]
  rfl

/--
At every finite argument other than `±1` the parts of `catanh` before rounding are the exact
result: the first-quadrant value extended by parity and conjugation.
-/
theorem atanhParts_denotes (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt}
    (hz : isFinite z = true) (hpos : toComplex z ≠ 1) (hneg : toComplex z ≠ -1) :
    (atanhParts z).Denotes (atanhExact z) :=
  Parts.ofQuadrant_denotes hfmt true (fun ζ => toComplex ζ ≠ 1 ∧ toComplex ζ ≠ -1)
    (fun ζ hζ hd => by
      rw [toComplex_conj ζ hζ]
      exact ⟨fun h => hd.1 (by simpa using congrArg (starRingEnd ℂ) h),
        fun h => hd.2 (by simpa using congrArg (starRingEnd ℂ) h)⟩)
    (fun ζ hζ hd => by
      rw [toComplex_neg_re hζ]
      constructor
      · intro h
        exact hd.2 (Complex.ext (by simpa using neg_eq_iff_eq_neg.mp (congrArg Complex.re h))
          (by simpa using congrArg Complex.im h))
      · intro h
        exact hd.1 (Complex.ext (by simpa using neg_eq_iff_eq_neg.mp (congrArg Complex.re h))
          (by simpa using congrArg Complex.im h)))
    (fun _ hζ hd _ _ => atanhCore_denotes hζ hd.1 hd.2) hz ⟨hpos, hneg⟩

/--
For an IEEE descriptor, `atanh` of a finite argument other than `±1` is the inverse hyperbolic
tangent with each part rounded once in the direction `mode`.
-/
theorem atanh_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (hpos : toComplex z ≠ 1) (hneg : toComplex z ≠ -1)
    (mode : Model.IEEERoundingMode := .nearest) :
    atanh z mode = (atanhExact z).round fmt mode :=
  (atanhParts_denotes hfmt hz hpos hneg).round mode

/-- At the argument one, with a zero imaginary part of either sign, `atanhCore` is the pole. -/
theorem atanhCore_one {z : ExecComplex fmt} (hz : isFinite z = true) (hpole : toComplex z = 1) :
    atanhCore z = ⟨.exact (Model.posInf fmt), .exact (Model.zero fmt false)⟩ := by
  obtain ⟨hx, hy⟩ := toRat?_of_toComplex_eq (a := 1) (b := 0) hz
    (by rw [hpole]; apply Complex.ext <;> simp)
  simp [atanhCore, hx, hy]

/-- The parts of `catanh` before rounding at `1 ± 0 i`: the pole `+∞ ± 0 i`. -/
theorem atanhParts_one {z : ExecComplex fmt} (hz : isFinite z = true)
    (hpole : toComplex z = 1) :
    atanhParts z =
      ⟨.exact (Model.posInf fmt), .exact (Model.zero fmt (Model.signBit z.im))⟩ := by
  have hsign : Model.signBit z.re = false := by
    have hreal : Model.toReal z.re = 1 := congrArg Complex.re hpole
    rw [signBit_eq_decide_toReal_neg ((isFinite_eq_true_iff z).1 hz).1
      (by rw [hreal]; exact one_ne_zero), hreal]
    simp
  unfold atanhParts Parts.ofQuadrant Parts.ofUpperHalf
  cases him : Model.signBit z.im with
  | false => simp [hsign, atanhCore_one hz hpole]
  | true =>
      have hsc : Model.signBit (ExecComplex.conj z).re = false := hsign
      simp [hsc, atanhCore_one (isFinite_conj hz) (by rw [toComplex_conj z hz, hpole]; simp),
        Parts.conj, Part.neg, Model.zero]

/-- The parts of `catanh` before rounding at `-1 ± 0 i`: the pole `-∞ ± 0 i`. -/
theorem atanhParts_neg_one {z : ExecComplex fmt} (hz : isFinite z = true)
    (hpole : toComplex z = -1) :
    atanhParts z =
      ⟨.exact (Model.negInf fmt), .exact (Model.zero fmt (Model.signBit z.im))⟩ := by
  have hsign : Model.signBit z.re = true := by
    have hreal : Model.toReal z.re = -1 := congrArg Complex.re hpole
    rw [signBit_eq_decide_toReal_neg ((isFinite_eq_true_iff z).1 hz).1
      (by rw [hreal]; norm_num), hreal]
    simp
  have hreflect (ζ : ExecComplex fmt) (hζ : isFinite ζ = true) (h : toComplex ζ = -1) :
      atanhCore ⟨Model.neg ζ.re, ζ.im⟩ =
        ⟨.exact (Model.posInf fmt), .exact (Model.zero fmt false)⟩ :=
    atanhCore_one (by simpa [isFinite] using hζ) (by
      rw [toComplex_neg_re hζ, h]
      apply Complex.ext <;> simp)
  unfold atanhParts Parts.ofQuadrant Parts.ofUpperHalf
  cases him : Model.signBit z.im with
  | false => simp [hsign, hreflect z hz hpole, Part.neg]
  | true =>
      have hsc : Model.signBit (ExecComplex.conj z).re = true := hsign
      simp [hsc, hreflect _ (isFinite_conj hz) (by rw [toComplex_conj z hz, hpole]; simp),
        Parts.conj, Part.neg, Model.zero]

/-- `atanh (1 ± 0 i) = +∞ ± 0 i`, the pole of C23 G.6.3.3, in every rounding direction. -/
theorem atanh_one {z : ExecComplex fmt} (hz : isFinite z = true) (hpole : toComplex z = 1)
    (mode : Model.IEEERoundingMode := .nearest) :
    atanh z mode = ⟨Model.posInf fmt, Model.zero fmt (Model.signBit z.im)⟩ := by
  rw [atanh, atanhParts_one hz hpole]
  rfl

/-- `atanh (-1 ± 0 i) = -∞ ± 0 i`, the pole of C23 G.6.3.3 by parity, in every direction. -/
theorem atanh_neg_one {z : ExecComplex fmt} (hz : isFinite z = true) (hpole : toComplex z = -1)
    (mode : Model.IEEERoundingMode := .nearest) :
    atanh z mode = ⟨Model.negInf fmt, Model.zero fmt (Model.signBit z.im)⟩ := by
  rw [atanh, atanhParts_neg_one hz hpole]
  rfl

/-- The exact result of `catan` at a finite argument other than `±i`: `-i catanh (i z)`. -/
noncomputable def atanExact (z : ExecComplex fmt) : Exact := (atanhExact (mulI z)).mulNegI

/-- Multiplying a finite complex value by `i` exactly multiplies the number it denotes by `i`. -/
theorem toComplex_mulI {z : ExecComplex fmt} (hz : isFinite z = true) :
    toComplex (mulI z) = Complex.I * toComplex z := by
  rw [mulI, toComplex, Model.toReal_neg _ ((isFinite_eq_true_iff z).1 hz).2]
  apply Complex.ext <;> simp [toComplex]

/-- Multiplication by `i` keeps a complex value finite. -/
theorem isFinite_mulI {z : ExecComplex fmt} (hz : isFinite z = true) :
    isFinite (mulI z) = true := by
  obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 hz
  simp [isFinite, mulI, hre, him]

/--
For an IEEE descriptor, `atan` of a finite argument other than `±i` is `-i atanh (i w)` with each
part rounded once in the direction `mode`.
-/
theorem atan_eq (hfmt : fmt.isIEEE = true) {z : ExecComplex fmt} (hz : isFinite z = true)
    (hpos : toComplex z ≠ Complex.I) (hneg : toComplex z ≠ -Complex.I)
    (mode : Model.IEEERoundingMode := .nearest) :
    atan z mode = (atanExact z).round fmt mode := by
  have h1 : toComplex (mulI z) ≠ 1 := by
    rw [toComplex_mulI hz]
    intro h
    apply hneg
    have := congrArg (fun v => -Complex.I * v) h
    simpa [← mul_assoc] using this
  have h2 : toComplex (mulI z) ≠ -1 := by
    rw [toComplex_mulI hz]
    intro h
    apply hpos
    have := congrArg (fun v => -Complex.I * v) h
    simpa [← mul_assoc] using this
  exact (atanhParts_denotes hfmt (isFinite_mulI hz) h1 h2).mulNegI.round mode

/-- `atan (±0 + i) = ±0 + ∞ i`: the pole of `catanh` at `-1` through `catan z = -i catanh (i z)`. -/
theorem atan_I {z : ExecComplex fmt} (hz : isFinite z = true) (hpole : toComplex z = Complex.I)
    (mode : Model.IEEERoundingMode := .nearest) :
    atan z mode = ⟨Model.zero fmt (Model.signBit z.re), Model.posInf fmt⟩ := by
  have h : toComplex (mulI z) = -1 := by rw [toComplex_mulI hz, hpole, Complex.I_mul_I]
  rw [atan, atanParts, atanhParts_neg_one (isFinite_mulI hz) h]
  simp [Parts.mulNegI, Parts.round, Part.round, Part.neg, mulI]

/-- `atan (±0 - i) = ±0 - ∞ i`: the pole of `catanh` at `1` through `catan z = -i catanh (i z)`. -/
theorem atan_neg_I {z : ExecComplex fmt} (hz : isFinite z = true)
    (hpole : toComplex z = -Complex.I) (mode : Model.IEEERoundingMode := .nearest) :
    atan z mode = ⟨Model.zero fmt (Model.signBit z.re), Model.negInf fmt⟩ := by
  have h : toComplex (mulI z) = 1 := by rw [toComplex_mulI hz, hpole]; simp
  rw [atan, atanParts, atanhParts_one (isFinite_mulI hz) h]
  simp [Parts.mulNegI, Parts.round, Part.round, Part.neg, mulI]

/-! ## Conjugation and parity at every argument -/

/--
`clog (conj z) = conj (clog z)` (C23 G.6.4.2), at every argument, a NaN or an infinity included, in
a rounding direction that negation fixes.
-/
theorem log_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    log (ExecComplex.conj z) mode = ExecComplex.conj (log z mode) :=
  Parts.round_ofUpperHalf_conj hfmt logCore z hmode

/--
`log1p (conj z) = conj (log1p z)`, at every argument, a NaN or an infinity included, in a
rounding direction that negation fixes.
-/
theorem log1p_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    log1p (ExecComplex.conj z) mode = ExecComplex.conj (log1p z mode) :=
  Parts.round_ofUpperHalf_conj hfmt log1pCore z hmode

/--
`catanh (conj z) = conj (catanh z)` (C23 G.6.3.3), at every argument, a NaN or an infinity included,
in a rounding direction that negation fixes.
-/
theorem atanh_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    atanh (ExecComplex.conj z) mode = ExecComplex.conj (atanh z mode) :=
  Parts.round_ofUpperHalf_conj hfmt _ z hmode

/--
`catanh` is odd (C23 G.6.3.3): `catanh (-z) = -catanh z` at every argument, a NaN or an infinity
included, in a rounding direction that negation fixes.
-/
theorem atanh_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    atanh (ExecComplex.neg z) mode = ExecComplex.neg (atanh z mode) :=
  Parts.round_ofQuadrant_neg hfmt atanhCore z hmode

/--
`catan (conj z) = conj (catan z)` (C23 G.6.1, paragraph 8, from `catanh`), at every argument, a NaN
or an infinity included, in a rounding direction that negation fixes.
-/
theorem atan_conj (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    atan (ExecComplex.conj z) mode = ExecComplex.conj (atan z mode) :=
  Parts.round_mulNegI_conj hfmt atanhCore z hmode

/--
`catan` is odd (C23 G.6.1, paragraph 8, from `catanh`): `catan (-z) = -catan z` at every argument, a
NaN or an infinity included, in a rounding direction that negation fixes.
-/
theorem atan_neg (hfmt : fmt.isIEEE = true) (z : ExecComplex fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    atan (ExecComplex.neg z) mode = ExecComplex.neg (atan z mode) :=
  Parts.round_mulNegI_neg hfmt atanhCore z hmode

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
