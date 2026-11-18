/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Parts
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Semantics
public import FloatLib.Numerics.Enclosure.Rational.Proof

/-!
# Exact results of complex functions and their rounding

`Exact` is the exact result of a complex function at one input: a complex number, and the sign
of the zero delivered for a part that is exactly zero. `Exact.round` rounds each part once with
`Model.roundReal`, which is the specification of a correctly rounded complex function at a finite
input.

`Exact.ofUpperHalf` and `Exact.ofQuadrant` state a function on every finite input from its values
where the sign bits are clear, by the symmetries of C23 G.6. They are the same definitions as
`Parts.ofUpperHalf` and `Parts.ofQuadrant` on the executable side, so a zero part selects the
side of a branch cut in the specification as it does in the code (C23 7.3.3).

`Parts.Denotes` relates the executable parts to an exact result: each part is an oracle that
compares the corresponding real with every rational. Then the rounded parts are the rounding of
the exact result (`Parts.Denotes.round`), in every rounding direction, and the symmetries
preserve the relation.

The extensions also commute with conjugation and negation at every input, a NaN or an infinity
included (`Parts.ofUpperHalf_conj`, `Parts.ofQuadrant_neg`), and rounding commutes with them in
the directions that negation fixes (`Part.round_neg`, `Parts.round_conj_of_negate`). The symmetry
theorems of the functions (`exp_conj`, `sinh_neg`, ...) are one-line corollaries of
`Parts.round_ofUpperHalf_conj`, `Parts.round_ofQuadrant_neg` and `Parts.round_mulNegI_conj`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

noncomputable section

variable {fmt : FloatFormat}

/--
The exact result of a complex function at one input: its value, and the signs of the zeros
delivered for a real or imaginary part that is exactly zero.
-/
structure Exact where
  /-- The exact complex value. -/
  value : ℂ
  /-- Sign of the zero delivered when the real part is exactly zero. -/
  reZero : Bool := false
  /-- Sign of the zero delivered when the imaginary part is exactly zero. -/
  imZero : Bool := false

namespace Exact

/-- The conjugate result: the imaginary part and the sign of its zero flip. -/
def conj (e : Exact) : Exact := ⟨starRingEnd ℂ e.value, e.reZero, !e.imZero⟩

/-- The result times `-i`: `-i (u + i v) = v - i u`. -/
def mulNegI (e : Exact) : Exact := ⟨-Complex.I * e.value, e.imZero, !e.reZero⟩

/--
Each part of the exact result rounded once to `fmt` in the direction `mode`: the result of a
correctly rounded complex function.
-/
def round (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (e : Exact) : ExecComplex fmt :=
  ⟨Model.roundReal fmt mode e.value.re e.reZero, Model.roundReal fmt mode e.value.im e.imZero⟩

/--
Extend exact results given where the imaginary sign bit is clear to every input by
`f (conj z) = conj (f z)`.
-/
def ofUpperHalf (core : ExecComplex fmt → Exact) (z : ExecComplex fmt) : Exact :=
  if Model.signBit z.im then (core (ExecComplex.conj z)).conj else core z

/--
Extend exact results given where both sign bits are clear to every input by
`f (conj z) = conj (f z)` and the parity `f (-z) = -f z` (`odd`) or `f (-z) = f z`.
-/
def ofQuadrant (odd : Bool) (core : ExecComplex fmt → Exact) : ExecComplex fmt → Exact :=
  ofUpperHalf fun z =>
    if Model.signBit z.re then
      let w := core ⟨Model.neg z.re, z.im⟩
      if odd then ⟨⟨-w.value.re, w.value.im⟩, !w.reZero, w.imZero⟩ else w.conj
    else core z

end Exact

/--
The part is an oracle for the real `x`: it compares `x` with every rational, and delivers the
zero with the sign `zeroSign` when `x` is zero.
-/
def Part.Denotes (part : Part fmt) (x : ℝ) (zeroSign : Bool) : Prop :=
  ∃ compare, part = .real compare zeroSign ∧
    ∀ boundary : Rat, compare boundary = cmp x (boundary : ℝ)

/-- Negating a part negates the real it denotes and flips the sign of its zero. -/
theorem Part.Denotes.neg {part : Part fmt} {x : ℝ} {zeroSign : Bool}
    (h : part.Denotes x zeroSign) : part.neg.Denotes (-x) (!zeroSign) := by
  obtain ⟨compare, rfl, hcompare⟩ := h
  refine ⟨_, rfl, fun boundary => ?_⟩
  rw [hcompare, cmp_swap]
  push_cast
  simp only [cmp, cmpUsing, neg_lt, lt_neg]

/-- A part that denotes a real rounds to the rounding of that real, in every direction. -/
theorem Part.Denotes.round {part : Part fmt} {x : ℝ} {zeroSign : Bool}
    (h : part.Denotes x zeroSign) (mode : Model.IEEERoundingMode) :
    part.round mode = Model.roundReal fmt mode x zeroSign := by
  obtain ⟨compare, rfl, hcompare⟩ := h
  exact Model.AlgebraicRounding.roundSigned_eq_roundReal fmt mode hcompare zeroSign

/-- With a sound enclosure, `compareWithin` is the exact comparison at every boundary. -/
theorem compareWithin_eq {enclosure : Option Numerics.RationalInterval} {exact : Rat → Ordering}
    {x : ℝ} (henclosure : ∀ interval, enclosure = some interval → interval.Contains x)
    (hexact : ∀ boundary : Rat, exact boundary = cmp x (boundary : ℝ)) (boundary : Rat) :
    compareWithin enclosure exact boundary = cmp x (boundary : ℝ) := by
  unfold compareWithin
  split
  · rename_i interval
    obtain ⟨hlo, hhi⟩ := henclosure interval rfl
    split
    · rename_i hbelow
      exact ((cmp_eq_gt_iff _ _).mpr
        ((by exact_mod_cast hbelow : (boundary : ℝ) < interval.lo).trans_le hlo)).symm
    · split
      · rename_i habove
        exact ((cmp_eq_lt_iff _ _).mpr
          (hhi.trans_lt (by exact_mod_cast habove : (interval.hi : ℝ) < boundary))).symm
      · exact hexact boundary
  · exact hexact boundary

/-- A sound enclosure does not change the real that a part denotes. -/
theorem Part.Denotes.within {part : Part fmt} {x : ℝ} {zeroSign : Bool}
    (h : part.Denotes x zeroSign) {enclosure : Option Numerics.RationalInterval}
    (henclosure : ∀ interval, enclosure = some interval → interval.Contains x) :
    (part.within enclosure).Denotes x zeroSign := by
  obtain ⟨compare, rfl, hcompare⟩ := h
  exact ⟨_, rfl, compareWithin_eq henclosure hcompare⟩

/-- Every enclosure that `refineTwice` returns is one that `enclose` returned. -/
theorem contains_of_refineTwice {enclose : Nat → Option Numerics.RationalInterval} {x : ℝ}
    (h : ∀ precision interval, enclose precision = some interval → interval.Contains x)
    (interval : Numerics.RationalInterval) (hresult : refineTwice fmt enclose = some interval) :
    interval.Contains x := by
  unfold refineTwice at hresult
  dsimp only at hresult
  split at hresult
  · rename_i first hfirst
    split at hresult
    · exact Option.some.inj hresult ▸ h _ _ hfirst
    · split at hresult
      · rename_i refined hrefined
        exact Option.some.inj hresult ▸ h _ _ hrefined
      · exact Option.some.inj hresult ▸ h _ _ hfirst
  · exact h _ _ hresult

/-- Both parts are oracles for the parts of the exact result `e`. -/
def Parts.Denotes (w : Parts fmt) (e : Exact) : Prop :=
  w.re.Denotes e.value.re e.reZero ∧ w.im.Denotes e.value.im e.imZero

namespace Parts.Denotes

variable {w : Parts fmt} {e : Exact}

/-- Conjugation before rounding conjugates the exact result. -/
theorem conj (h : w.Denotes e) : w.conj.Denotes e.conj :=
  ⟨h.1, by simpa [Parts.conj, Exact.conj] using h.2.neg⟩

/-- Multiplication by `-i` before rounding multiplies the exact result by `-i`. -/
theorem mulNegI (h : w.Denotes e) : w.mulNegI.Denotes e.mulNegI :=
  ⟨by simpa [Parts.mulNegI, Exact.mulNegI] using h.2,
    by simpa [Parts.mulNegI, Exact.mulNegI] using h.1.neg⟩

/--
Parts that denote an exact result round to the rounding of that result: each part is rounded
once, in every rounding direction.
-/
theorem round (h : w.Denotes e) (mode : Model.IEEERoundingMode) :
    w.round mode = e.round fmt mode := by
  rw [Parts.round, Exact.round, h.1.round mode, h.2.round mode]

end Parts.Denotes

/-- In an IEEE format, negation flips the sign bit of every encoding. -/
theorem signBit_neg (hfmt : fmt.isIEEE = true) (x : Model fmt) :
    Model.signBit (Model.neg x) = !Model.signBit x := by
  rw [Model.neg_eq_toggleSign_of_supportsSignedZero x
    (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt), Model.signBit_toggleSign]

/-! ## The symmetries at every input

The extensions `Parts.ofUpperHalf` and `Parts.ofQuadrant` commute with conjugation and negation
by construction, whatever the argument is: a NaN, an infinity or a finite value. Rounding then
commutes with them in the directions that negation fixes (`mode.negate = mode`: the two
roundings to nearest, toward zero and away from zero), and mirrors `up` and `down`.
-/

/-- Negating a part twice gives the part back. -/
@[simp] theorem Part.neg_neg (part : Part fmt) : part.neg.neg = part := by
  cases part with
  | exact value => simp [Part.neg]
  | real compare zeroSign =>
      simp only [Part.neg, Bool.not_not, Part.real.injEq, and_true]
      funext boundary
      simp

/-- Conjugating parts twice gives the parts back. -/
@[simp] theorem Parts.conj_conj (w : Parts fmt) : w.conj.conj = w := by
  simp [Parts.conj]

/-- Rounding a negated part negates the rounding of the part in the mirrored direction. -/
theorem Part.round_neg (hfmt : fmt.isIEEE = true) (part : Part fmt)
    (mode : Model.IEEERoundingMode) :
    part.neg.round mode = Model.neg (part.round mode.negate) := by
  cases part with
  | exact value => rfl
  | real compare zeroSign =>
      exact Model.AlgebraicRounding.roundSigned_neg hfmt mode compare zeroSign

/--
Rounding conjugated parts: the real part is unchanged, and the imaginary part is the negation of
its rounding in the mirrored direction.
-/
theorem Parts.round_conj (hfmt : fmt.isIEEE = true) (w : Parts fmt)
    (mode : Model.IEEERoundingMode) :
    w.conj.round mode = ⟨(w.round mode).re, Model.neg (w.round mode.negate).im⟩ := by
  simp [Parts.round, Parts.conj, Part.round_neg hfmt]

/-- In a direction that negation fixes, rounding commutes with conjugation. -/
theorem Parts.round_conj_of_negate (hfmt : fmt.isIEEE = true) (w : Parts fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    w.conj.round mode = ExecComplex.conj (w.round mode) := by
  rw [Parts.round_conj hfmt, hmode]
  rfl

/-- In a direction that negation fixes, rounding commutes with the negation of both parts. -/
theorem Parts.round_neg_of_negate (hfmt : fmt.isIEEE = true) (w : Parts fmt)
    {mode : Model.IEEERoundingMode} (hmode : mode.negate = mode) :
    (⟨w.re.neg, w.im.neg⟩ : Parts fmt).round mode = ExecComplex.neg (w.round mode) := by
  simp [Parts.round, ExecComplex.neg, Part.round_neg hfmt, hmode]

/-- An extension by conjugation commutes with conjugation, at every input. -/
theorem Parts.ofUpperHalf_conj (hfmt : fmt.isIEEE = true) (core : ExecComplex fmt → Parts fmt)
    (z : ExecComplex fmt) :
    Parts.ofUpperHalf core (ExecComplex.conj z) = (Parts.ofUpperHalf core z).conj := by
  have hsign : Model.signBit (ExecComplex.conj z).im = !Model.signBit z.im := by
    simp [ExecComplex.conj, signBit_neg hfmt]
  have hconj : ExecComplex.conj (ExecComplex.conj z) = z := by
    simp [ExecComplex.conj]
  unfold Parts.ofUpperHalf
  rw [hsign, hconj]
  cases Model.signBit z.im <;> simp

/--
Negating the real part of the argument of a quadrant extension negates the real part of an odd
function and conjugates an even one, at every input.
-/
theorem Parts.ofQuadrant_neg_re (hfmt : fmt.isIEEE = true) (odd : Bool)
    (core : ExecComplex fmt → Parts fmt) (z : ExecComplex fmt) :
    Parts.ofQuadrant odd core ⟨Model.neg z.re, z.im⟩ =
      if odd then ⟨(Parts.ofQuadrant odd core z).re.neg, (Parts.ofQuadrant odd core z).im⟩
      else (Parts.ofQuadrant odd core z).conj := by
  have hsign : Model.signBit (Model.neg z.re) = !Model.signBit z.re := signBit_neg hfmt z.re
  unfold Parts.ofQuadrant Parts.ofUpperHalf
  cases hre : Model.signBit z.re <;> cases him : Model.signBit z.im <;> cases odd <;>
    simp [hsign, hre, ExecComplex.conj, Parts.conj]

/--
Negating the argument of a quadrant extension negates both parts of an odd function and leaves an
even one unchanged, at every input.
-/
theorem Parts.ofQuadrant_neg (hfmt : fmt.isIEEE = true) (odd : Bool)
    (core : ExecComplex fmt → Parts fmt) (z : ExecComplex fmt) :
    Parts.ofQuadrant odd core (ExecComplex.neg z) =
      if odd then ⟨(Parts.ofQuadrant odd core z).re.neg, (Parts.ofQuadrant odd core z).im.neg⟩
      else Parts.ofQuadrant odd core z := by
  rw [show ExecComplex.neg z = ExecComplex.conj ⟨Model.neg z.re, z.im⟩ from rfl,
    Parts.ofQuadrant, Parts.ofUpperHalf_conj hfmt, ← Parts.ofQuadrant,
    Parts.ofQuadrant_neg_re hfmt]
  cases odd <;> simp [Parts.conj]

variable {mode : Model.IEEERoundingMode}

/--
A function extended by conjugation and rounded commutes with conjugation at every input, in a
direction that negation fixes. A quadrant extension is one too.
-/
theorem Parts.round_ofUpperHalf_conj (hfmt : fmt.isIEEE = true)
    (core : ExecComplex fmt → Parts fmt) (z : ExecComplex fmt) (hmode : mode.negate = mode) :
    (Parts.ofUpperHalf core (ExecComplex.conj z)).round mode =
      ExecComplex.conj ((Parts.ofUpperHalf core z).round mode) := by
  rw [Parts.ofUpperHalf_conj hfmt, Parts.round_conj_of_negate hfmt _ hmode]

/-- An odd quadrant extension, rounded in a direction that negation fixes, is odd. -/
theorem Parts.round_ofQuadrant_neg (hfmt : fmt.isIEEE = true)
    (core : ExecComplex fmt → Parts fmt) (z : ExecComplex fmt) (hmode : mode.negate = mode) :
    (Parts.ofQuadrant true core (ExecComplex.neg z)).round mode =
      ExecComplex.neg ((Parts.ofQuadrant true core z).round mode) := by
  rw [Parts.ofQuadrant_neg hfmt]
  exact Parts.round_neg_of_negate hfmt _ hmode

/-- An even quadrant extension is even, at every input and in every direction. -/
theorem Parts.round_ofQuadrant_neg_even (hfmt : fmt.isIEEE = true)
    (core : ExecComplex fmt → Parts fmt) (z : ExecComplex fmt) (mode : Model.IEEERoundingMode) :
    (Parts.ofQuadrant false core (ExecComplex.neg z)).round mode =
      (Parts.ofQuadrant false core z).round mode := by
  rw [Parts.ofQuadrant_neg hfmt]
  rfl

/--
The circular function `-i g (i z)` of an odd quadrant extension `g` (C23 G.6.1, paragraph 8)
commutes with conjugation at every input, in a direction that negation fixes.
-/
theorem Parts.round_mulNegI_conj (hfmt : fmt.isIEEE = true)
    (core : ExecComplex fmt → Parts fmt) (z : ExecComplex fmt) (hmode : mode.negate = mode) :
    (Parts.ofQuadrant true core (mulI (ExecComplex.conj z))).mulNegI.round mode =
      ExecComplex.conj ((Parts.ofQuadrant true core (mulI z)).mulNegI.round mode) := by
  have h := Parts.ofQuadrant_neg_re hfmt true core (mulI z)
  rw [show mulI (ExecComplex.conj z) = ⟨Model.neg (mulI z).re, (mulI z).im⟩ from rfl, h,
    ← Parts.round_conj_of_negate hfmt _ hmode]
  rfl

/--
The circular function `-i g (i z)` of an odd quadrant extension `g` is odd at every input, in a
direction that negation fixes.
-/
theorem Parts.round_mulNegI_neg (hfmt : fmt.isIEEE = true)
    (core : ExecComplex fmt → Parts fmt) (z : ExecComplex fmt) (hmode : mode.negate = mode) :
    (Parts.ofQuadrant true core (mulI (ExecComplex.neg z))).mulNegI.round mode =
      ExecComplex.neg ((Parts.ofQuadrant true core (mulI z)).mulNegI.round mode) := by
  have h := Parts.ofQuadrant_neg hfmt true core (mulI z)
  rw [show mulI (ExecComplex.neg z) = ExecComplex.neg (mulI z) from rfl, h,
    ← Parts.round_neg_of_negate hfmt _ hmode]
  rfl

/-- A finite value has a finite conjugate. -/
theorem isFinite_conj {z : ExecComplex fmt} (hz : isFinite z = true) :
    isFinite (ExecComplex.conj z) = true := by
  simpa [isFinite, ExecComplex.conj] using hz

/--
A function correct where the imaginary sign bit is clear is correct at every finite input of a
domain closed under conjugation, after the extension by conjugation.
-/
theorem Parts.ofUpperHalf_denotes (hfmt : fmt.isIEEE = true)
    {core : ExecComplex fmt → Parts fmt} {spec : ExecComplex fmt → Exact}
    (domain : ExecComplex fmt → Prop)
    (hconj : ∀ ζ : ExecComplex fmt, isFinite ζ = true → domain ζ → domain (ExecComplex.conj ζ))
    (hcore : ∀ ζ : ExecComplex fmt, isFinite ζ = true → domain ζ →
      Model.signBit ζ.im = false → (core ζ).Denotes (spec ζ))
    {z : ExecComplex fmt} (hz : isFinite z = true) (hdomain : domain z) :
    (Parts.ofUpperHalf core z).Denotes (Exact.ofUpperHalf spec z) := by
  unfold Parts.ofUpperHalf Exact.ofUpperHalf
  cases hsign : Model.signBit z.im with
  | false => simpa using hcore z hz hdomain hsign
  | true =>
      simpa using (hcore _ (isFinite_conj hz) (hconj z hz hdomain)
        (by simp [ExecComplex.conj, signBit_neg hfmt, hsign])).conj

/--
A function correct where both sign bits are clear is correct at every finite input of a domain
closed under conjugation and under negation of the real part, after the extension by conjugation
and parity.
-/
theorem Parts.ofQuadrant_denotes (hfmt : fmt.isIEEE = true) (odd : Bool)
    {core : ExecComplex fmt → Parts fmt} {spec : ExecComplex fmt → Exact}
    (domain : ExecComplex fmt → Prop)
    (hconj : ∀ ζ : ExecComplex fmt, isFinite ζ = true → domain ζ → domain (ExecComplex.conj ζ))
    (hreflect : ∀ ζ : ExecComplex fmt, isFinite ζ = true → domain ζ →
      domain ⟨Model.neg ζ.re, ζ.im⟩)
    (hcore : ∀ ζ : ExecComplex fmt, isFinite ζ = true → domain ζ →
      Model.signBit ζ.re = false → Model.signBit ζ.im = false → (core ζ).Denotes (spec ζ))
    {z : ExecComplex fmt} (hz : isFinite z = true) (hdomain : domain z) :
    (Parts.ofQuadrant odd core z).Denotes (Exact.ofQuadrant odd spec z) := by
  refine Parts.ofUpperHalf_denotes hfmt domain hconj (fun ζ hζ hd him => ?_) hz hdomain
  cases hsign : Model.signBit ζ.re with
  | false => simpa [hsign] using hcore ζ hζ hd hsign him
  | true =>
      have hfinite : isFinite (⟨Model.neg ζ.re, ζ.im⟩ : ExecComplex fmt) = true := by
        simpa [isFinite] using hζ
      have h := hcore _ hfinite (hreflect ζ hζ hd) (by simp [signBit_neg hfmt, hsign]) him
      cases odd with
      | false => simpa [hsign] using h.conj
      | true =>
          simp only [↓reduceIte]
          exact ⟨h.1.neg, h.2⟩

/--
A finite complex input decodes to two rationals, which are its real and imaginary parts as a
complex number, and neither part is a NaN or an infinity.
-/
theorem exists_toRat?_of_isFinite {z : ExecComplex fmt} (hz : isFinite z = true) :
    ∃ x y : Rat, Model.toRat? z.re = some x ∧ Model.toRat? z.im = some y ∧
      toComplex z = ⟨(x : ℝ), (y : ℝ)⟩ ∧
      Model.isNaN z.re = false ∧ Model.isInfinite z.re = false ∧
      Model.isNaN z.im = false ∧ Model.isInfinite z.im = false := by
  obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 hz
  have hsome (v : Model fmt) (hv : Model.isFinite v = true) : ∃ q, Model.toRat? v = some q :=
    Option.isSome_iff_exists.mp (by rw [Model.Algebraic.toRat?_isSome_eq_isFinite, hv])
  obtain ⟨x, hx⟩ := hsome z.re hre
  obtain ⟨y, hy⟩ := hsome z.im him
  refine ⟨x, y, hx, hy, ?_, Model.isNaN_eq_false_of_isFinite_eq_true _ hre,
    Model.isInfinite_eq_false_of_isFinite_eq_true _ hre,
    Model.isNaN_eq_false_of_isFinite_eq_true _ him,
    Model.isInfinite_eq_false_of_isFinite_eq_true _ him⟩
  rw [toComplex, Model.Algebraic.toReal_of_toRat?_eq_some hx,
    Model.Algebraic.toReal_of_toRat?_eq_some hy]

/-- A finite complex input whose value has the rational parts `a` and `b` decodes to them. -/
theorem toRat?_of_toComplex_eq {z : ExecComplex fmt} (hz : isFinite z = true) {a b : Rat}
    (hvalue : toComplex z = ⟨(a : ℝ), (b : ℝ)⟩) :
    Model.toRat? z.re = some a ∧ Model.toRat? z.im = some b := by
  obtain ⟨x, y, hx, hy, hw, -⟩ := exists_toRat?_of_isFinite hz
  rw [hw] at hvalue
  have hxa : x = a := by exact_mod_cast (show (x : ℝ) = a from congrArg Complex.re hvalue)
  have hyb : y = b := by exact_mod_cast (show (y : ℝ) = b from congrArg Complex.im hvalue)
  exact ⟨hxa ▸ hx, hyb ▸ hy⟩

/--
The sign bit of a finite value with a nonzero real value says whether that value is negative.
-/
theorem signBit_eq_decide_toReal_neg {x : Model fmt} (hx : Model.isFinite x = true)
    (hne : Model.toReal x ≠ 0) : Model.signBit x = decide (Model.toReal x < 0) := by
  cases hsign : Model.signBit x with
  | false =>
      exact (decide_eq_false (not_lt.mpr (Model.toReal_nonneg_of_signBit_eq_false hsign))).symm
  | true =>
      refine (decide_eq_true ?_).symm
      by_contra hnonneg
      rcases Model.isZero_or_signBit_eq_false_of_toReal_nonneg x hx (not_lt.mp hnonneg) with h | h
      · exact hne (Model.toReal_eq_zero_of_isZero x h)
      · rw [hsign] at h
        contradiction

end

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
