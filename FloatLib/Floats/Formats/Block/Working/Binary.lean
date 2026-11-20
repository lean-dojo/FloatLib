/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Binary
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.DivisionSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedProof
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.NonNaN
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Homogeneous
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Grid

/-!
# A block quantizer on the encodings of a binary working format

The reference quantizers of the block formats of ML accelerators do not compute with exact
quotients. torchao's `nvfp4_quantize` works in binary32: it divides the largest magnitude of a
block by the largest element value, divides by the outer scale, clamps, stores the result in
E4M3, forms one reciprocal per block and multiplies each element by it. This module has that
quantizer on encodings, for every working format, every scale format and every element format:

* `clamp low high x` is `torch.clamp`: a NaN stays, an infinity goes to the bound on its side.
* `blockMax block` is the largest magnitude of a block.
* `Quantizer work scale element` has the three constants of a quantizer: the `target` that the
  largest magnitude maps to and the `floor` and `ceiling` of a stored scale. `Quantizer.scale`,
  `Quantizer.reciprocal` and `Quantizer.element` are the stored block scale, the reciprocal of
  the total scale and the stored element, `Quantizer.block` quantizes a block and
  `Quantizer.words` gives its encodings as natural numbers.

Every operation is the IEEE operation of `Model work`, so a quotient or a product that exceeds
the range of the working format is an infinity, as on a machine.

## Main results

Each one holds for every IEEE working format and for all finite operands, whether or not an
operation overflows. `g` is the rounding onto the grid of the working format with an unbounded
exponent range (`roundAt work`).

* `toReal_clamp`, `clamp_posInf`, `clamp_negInf`: what the clamp returns.
* `toReal_blockMax`: the largest magnitude is exact.
* `Quantizer.toReal_scaled`: the clamped scale is `max floor (min ceiling (g (g (a / target) /
  outer)))`. When the second quotient overflows the machine has `+∞` and the formula has a number
  above the ceiling: both clamp to the ceiling.
* `Quantizer.toReal_scale`: the stored scale is that number rounded by the scale format.
* `Quantizer.toReal_element`: the stored element is the saturating element rounding of
  `max (-target) (min target (g (x * r)))`, for every finite reciprocal `r`. When the product
  overflows the machine has an infinity and the formula has a number beyond the target: both
  clamp to the target with the sign of the product.
* `Quantizer.reciprocal_eq`: the reciprocal is finite and equal to `g (g (1 / outer) / s)`, or
  a quotient overflowed and it is `+∞`. `Quantizer.toReal_element_posInf` then gives the
  element: the target with the sign of the input.

`Floats.Formats.Block.Working` instantiates these at binary32, E4M3 and E2M1 and derives the
error of an element from them.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block.Working

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.BinaryInterchange.Model

variable {W S E : FloatFormat}

/-- `torch.clamp` on encodings: `low` for a value below it, `high` for a value above it, and the
value otherwise. A NaN compares with nothing and is returned. -/
def clamp (low high x : Model W) : Model W :=
  if compare x low = some .lt then low else if compare high x = some .lt then high else x

/-- The largest magnitude of a block, and `+0` for an empty block. -/
def blockMax (block : List (Model W)) : Model W :=
  block.foldl (fun best x => if compare best (abs x) = some .lt then abs x else best)
    (zero W false)

/-! ## The clamp -/

/-- A finite value clamped between finite bounds is finite. -/
theorem isFinite_clamp {low high x : Model W} (hlow : isFinite low = true)
    (hhigh : isFinite high = true) (hx : isFinite x = true) :
    isFinite (clamp low high x) = true := by
  unfold clamp
  split_ifs <;> assumption

/-- On finite values with `low ≤ high`, the clamp is the clamp of the real values. -/
theorem toReal_clamp {low high x : Model W} (hlow : isFinite low = true)
    (hhigh : isFinite high = true) (hx : isFinite x = true) (hle : toReal low ≤ toReal high) :
    toReal (clamp low high x) = max (toReal low) (min (toReal high) (toReal x)) := by
  have hxl := compare_eq_some_lt_iff_toReal_lt_of_isFinite x low hx hlow
  have hhx := compare_eq_some_lt_iff_toReal_lt_of_isFinite high x hhigh hx
  unfold clamp
  split_ifs with h1 h2
  · rw [max_eq_left ((min_le_right _ _).trans (hxl.mp h1).le)]
  · rw [min_eq_left (hhx.mp h2).le, max_eq_right hle]
  · rw [min_eq_right (not_lt.mp (mt hhx.mpr h2)), max_eq_right (not_lt.mp (mt hxl.mpr h1))]

/-- `+∞` clamped between finite bounds is the upper bound. -/
theorem clamp_posInf (hW : W.isIEEE = true) {low high : Model W} (hlow : isFinite low = true)
    (hhigh : isFinite high = true) : clamp low high (posInf W) = high := by
  have hs := FloatFormat.supportsInfinity_eq_true_of_isIEEE W hW
  have h1 : compare (posInf W) low = some .gt := by
    simp [Model.compare, compareNonNaN, isNaN_eq_false_of_isFinite_eq_true low hlow,
      isInfinite_eq_false_of_isFinite_eq_true low hlow, hs]
  have h2 : compare high (posInf W) = some .lt := by
    simp [Model.compare, compareNonNaN, isNaN_eq_false_of_isFinite_eq_true high hhigh,
      isInfinite_eq_false_of_isFinite_eq_true high hhigh, hs]
  simp [clamp, h1, h2]

/-- `-∞` clamped between finite bounds is the lower bound. -/
theorem clamp_negInf (hW : W.isIEEE = true) {low high : Model W} (hlow : isFinite low = true) :
    clamp low high (negInf W) = low := by
  have hs := FloatFormat.supportsInfinity_eq_true_of_isIEEE W hW
  have h1 : compare (negInf W) low = some .lt := by
    simp [Model.compare, compareNonNaN, isNaN_eq_false_of_isFinite_eq_true low hlow,
      isInfinite_eq_false_of_isFinite_eq_true low hlow, hs]
  simp [clamp, h1]

/-! ## The largest magnitude -/

/-- The largest magnitude of a block of finite values is finite. -/
theorem isFinite_blockMax {block : List (Model W)} (h : ∀ x ∈ block, isFinite x = true) :
    isFinite (blockMax block) = true := by
  unfold blockMax
  suffices hgen : ∀ (block : List (Model W)) (init : Model W), isFinite init = true →
      (∀ x ∈ block, isFinite x = true) →
      isFinite (block.foldl
        (fun best x => if compare best (abs x) = some .lt then abs x else best) init) = true from
    hgen block _ (isFinite_eq_true_of_isZero_eq_true _ (isZero_zero W false)) h
  intro block
  induction block with
  | nil => intro init hinit _; exact hinit
  | cons x xs ih =>
    intro init hinit hall
    refine ih _ ?_ fun y hy => hall y (List.mem_cons_of_mem _ hy)
    change isFinite (if compare init (abs x) = some .lt then abs x else init) = true
    split_ifs
    · rw [isFinite_abs]
      exact hall x List.mem_cons_self
    · exact hinit

/-- The largest magnitude of a block of finite values is the largest of their magnitudes, and
zero for an empty block. -/
theorem toReal_blockMax (hW : W.isIEEE = true) {block : List (Model W)}
    (h : ∀ x ∈ block, isFinite x = true) :
    toReal (blockMax block) = (block.map fun x => |toReal x|).foldl max 0 := by
  have hz := FloatFormat.supportsSignedZero_eq_true_of_isIEEE W hW
  unfold blockMax
  suffices hgen : ∀ (block : List (Model W)) (init : Model W), isFinite init = true →
      (∀ x ∈ block, isFinite x = true) →
      toReal (block.foldl
        (fun best x => if compare best (abs x) = some .lt then abs x else best) init) =
        (block.map fun x => |toReal x|).foldl max (toReal init) by
    have h0 := hgen block _ (isFinite_eq_true_of_isZero_eq_true _ (isZero_zero W false)) h
    rwa [toReal_zero] at h0
  intro block
  induction block with
  | nil => intro init _ _; rfl
  | cons x xs ih =>
    intro init hinit hall
    have hx := hall x List.mem_cons_self
    have hax : isFinite (abs x) = true := by rw [isFinite_abs]; exact hx
    have hstep : isFinite (if compare init (abs x) = some .lt then abs x else init) = true := by
      split_ifs <;> assumption
    have hcmp := compare_eq_some_lt_iff_toReal_lt_of_isFinite init (abs x) hinit hax
    rw [toReal_abs_of_isFinite x hz hx] at hcmp
    rw [List.foldl_cons, List.map_cons, List.foldl_cons,
      ih _ hstep fun y hy => hall y (List.mem_cons_of_mem _ hy)]
    congr 1
    split_ifs with hlt
    · rw [toReal_abs_of_isFinite x hz hx]
      exact (max_eq_right (hcmp.mp hlt).le).symm
    · exact (max_eq_left (not_lt.mp (mt hcmp.mpr hlt))).symm

/-! ## One operation of the working format, with its overflow -/

/-- A nonzero dyadic number is negative exactly when its sign is set. -/
private theorem dyadic_toReal_neg_iff {d : Numerics.Dyadic} (h : d.significand ≠ 0) :
    d.toReal < 0 ↔ d.negative = true := by
  cases hs : d.negative with
  | false =>
    simp only [Bool.false_eq_true, iff_false, not_lt]
    exact (Dyadic.toReal_pos_of_negative_eq_false hs h).le
  | true => simpa using Dyadic.toReal_lt_zero_of_negative_eq_true hs h

/-- A finite value with a nonzero real value is not a zero. -/
private theorem isZero_eq_false_of_toReal_ne_zero {x : Model W} (h : toReal x ≠ 0) :
    isZero x = false := by
  by_contra hz
  exact h (toReal_eq_zero_of_isZero x (Bool.eq_true_of_not_eq_false hz))

/--
One division of the working format, for a finite dividend and a finite nonzero divisor: the
quotient is finite and is the exact quotient rounded once, or the exact quotient is beyond the
largest finite value and the result is the infinity with its sign.
-/
theorem div_eq_round_or_inf (hW : W.isIEEE = true) {x y : Model W} (hx : isFinite x = true)
    (hy : isFinite y = true) (hy0 : isZero y = false) :
    (isFinite (div x y) = true ∧ toReal (div x y) = roundAt W (toReal x / toReal y)) ∨
      (toReal (posMaxFinite W) < |toReal x / toReal y| ∧
        div x y = if toReal x / toReal y < 0 then negInf W else posInf W) := by
  by_cases hfin : isFinite (div x y) = true
  · exact Or.inl ⟨hfin, toReal_div_eq_roundAt x y hW hy hfin⟩
  right
  have hbig : toReal (posMaxFinite W) < |toReal x / toReal y| := by
    by_contra hle
    exact hfin (isFinite_div_of_abs_div_le_posMaxFinite x y hW hx hy hy0 (not_lt.mp hle))
  refine ⟨hbig, ?_⟩
  have hnan := isNaN_div_eq_false_of_isFinite x y .nearest hW hx hy hy0
  have hinf : isInfinite (div x y) = true := by
    by_contra h
    exact hfin (isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false _ hnan
      (Bool.eq_false_of_not_eq_true h))
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hdyMant := significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hdy hy0
  have hxr : toReal x = dx.toReal := by rw [toReal_eq, hdx]
  have hyr : toReal y = dy.toReal := by rw [toReal_eq, hdy]
  have hquot : toReal x / toReal y ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hbig
    exact absurd (toReal_posMaxFinite_pos W) (not_lt.mpr hbig.le)
  have hdxMant : dx.significand ≠ 0 := by
    intro h0
    exact hquot (by rw [hxr, (Dyadic.toReal_eq_zero_iff dx).2 h0, zero_div])
  have hdiv : div x y = roundRatScaled W (Bool.xor dx.negative dy.negative) dx.significand
      dy.significand (dx.exponent - dy.exponent) := by
    simp [Proof.div_eq_spec, Spec.div, hdx, hdy, hdyMant, hdxMant]
  have hsign : signBit (div x y) = Bool.xor dx.negative dy.negative := by
    rw [hdiv]
    exact AlgebraicRounding.signBit_roundRatScaled hW _ _ _ _ hdyMant
  have hneg : toReal x / toReal y < 0 ↔ Bool.xor dx.negative dy.negative = true := by
    rw [hxr, hyr]
    cases hsx : dx.negative <;> cases hsy : dy.negative
    · have h1 := Dyadic.toReal_pos_of_negative_eq_false hsx hdxMant
      have h2 := Dyadic.toReal_pos_of_negative_eq_false hsy hdyMant
      simpa using (div_pos h1 h2).le
    · have h1 := Dyadic.toReal_pos_of_negative_eq_false hsx hdxMant
      have h2 := Dyadic.toReal_lt_zero_of_negative_eq_true hsy hdyMant
      simpa using div_neg_of_pos_of_neg h1 h2
    · have h1 := Dyadic.toReal_lt_zero_of_negative_eq_true hsx hdxMant
      have h2 := Dyadic.toReal_pos_of_negative_eq_false hsy hdyMant
      simpa using div_neg_of_neg_of_pos h1 h2
    · have h1 := Dyadic.toReal_lt_zero_of_negative_eq_true hsx hdxMant
      have h2 := Dyadic.toReal_lt_zero_of_negative_eq_true hsy hdyMant
      simpa using (div_pos_of_neg_of_neg h1 h2).le
  obtain ⟨-, heq⟩ := eq_nativeOverflow_of_isInfinite hinf
  rw [heq, nativeOverflow_eq_signedInf_of_isIEEE W hW, hsign]
  by_cases hq : toReal x / toReal y < 0
  · rw [ite_eq_left hq, ite_eq_left (hneg.mp hq)]
  · rw [ite_eq_right hq, ite_eq_right (mt hneg.mpr hq)]

/--
One product of the working format, for finite factors: the product is finite and is the exact
product rounded once, or the rounded exact product is beyond the largest finite value and the
result is the infinity with its sign.
-/
theorem mul_eq_round_or_inf (hW : W.isIEEE = true) {x y : Model W} (hx : isFinite x = true)
    (hy : isFinite y = true) :
    (isFinite (mul x y) = true ∧ toReal (mul x y) = roundAt W (toReal x * toReal y)) ∨
      (toReal (posMaxFinite W) < |roundAt W (toReal x * toReal y)| ∧
        mul x y = if toReal x * toReal y < 0 then negInf W else posInf W) := by
  by_cases hfin : isFinite (mul x y) = true
  · exact Or.inl ⟨hfin, toReal_mul_eq_roundAt x y hW hfin⟩
  right
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  have hxr : toReal x = dx.toReal := by rw [toReal_eq, hdx]
  have hyr : toReal y = dy.toReal := by rw [toReal_eq, hdy]
  have hdxMant : dx.significand ≠ 0 := by
    intro h0
    refine hfin ?_
    have : mul x y = zero W (Bool.xor dx.negative dy.negative) := by
      simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, h0]
    rw [this]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero W _)
  have hdyMant : dy.significand ≠ 0 := by
    intro h0
    refine hfin ?_
    have : mul x y = zero W (Bool.xor dx.negative dy.negative) := by
      simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, h0]
    rw [this]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero W _)
  have hmul : mul x y = roundDyadic W ⟨Bool.xor dx.negative dy.negative,
      dx.significand * dy.significand, dx.exponent + dy.exponent⟩ := by
    simp [Proof.mul_eq_spec, Spec.mul, hdx, hdy, hdxMant, hdyMant]
  have hval : (Numerics.Dyadic.mk (Bool.xor dx.negative dy.negative)
      (dx.significand * dy.significand) (dx.exponent + dy.exponent)).toReal =
      toReal x * toReal y := by
    rw [hxr, hyr, ← Dyadic.toReal_mul]
  have hspec := roundDyadic_spec W ⟨Bool.xor dx.negative dy.negative,
    dx.significand * dy.significand, dx.exponent + dy.exponent⟩
  rw [hval, ← hmul] at hspec
  have hbig : toReal (posMaxFinite W) < |roundAt W (toReal x * toReal y)| := by
    by_contra hle
    exact hfin (hspec.1 (not_lt.mp hle)).1
  refine ⟨hbig, ?_⟩
  rw [hspec.2 hbig, nativeOverflow_eq_signedInf_of_isIEEE W hW]
  have hneg : toReal x * toReal y < 0 ↔ Bool.xor dx.negative dy.negative = true := by
    rw [← hval]
    exact dyadic_toReal_neg_iff (d := ⟨Bool.xor dx.negative dy.negative,
      dx.significand * dy.significand, dx.exponent + dy.exponent⟩)
      (Nat.mul_ne_zero hdxMant hdyMant)
  by_cases hq : toReal x * toReal y < 0
  · rw [ite_eq_left hq, ite_eq_left (hneg.mp hq)]
  · rw [ite_eq_right hq, ite_eq_right (mt hneg.mpr hq)]

/--
One cast between two descriptors of any kind: when the grid rounding of a finite value is inside
the finite range of the destination, the cast is finite and is that rounding.
-/
theorem cast_eq_roundAt_of_le {src dst : FloatFormat} (x : Model src) (hx : isFinite x = true)
    (hle : |roundAt dst (toReal x)| ≤ toReal (posMaxFinite dst)) :
    isFinite (Model.cast src dst x) = true ∧
      toReal (Model.cast src dst x) = roundAt dst (toReal x) := by
  by_cases hw : src.expWidth = dst.expWidth ∧ src.exponentBias = dst.exponentBias ∧
      src.encoding = dst.encoding ∧ src.fracWidth ≤ dst.fracWidth
  · rcases hw with ⟨he, hb, hc, hf⟩
    have hround : roundAt dst (toReal x) = toReal x :=
      Flocq.round_preserves_generic Flocq.nearestEven _ <|
        genericFormat_of_compatibleWidening hb hf (toReal_genericFormat_of_isFinite x hx)
    rw [cast_eq_widenExact_of_compatibleWidening x he hb hc hf hx, hround]
    exact ⟨isFinite_widenExact x he hb hc hf hx, toReal_widenExact x he hb hc hf hx⟩
  · have hnan := isNaN_eq_false_of_isFinite_eq_true x hx
    have hinf := isInfinite_eq_false_of_isFinite_eq_true x hx
    have hne : src ≠ dst := by
      intro h
      subst dst
      exact hw ⟨rfl, rfl, rfl, le_rfl⟩
    obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hx
    have hc : Model.cast src dst x = roundDyadic dst d := by
      simp only [Model.cast, Internal.Nearest.cast, hnan, hinf, Bool.false_eq_true, dite_false,
        hne]
      split
      · next he =>
        split
        · next hb =>
          split
          · next henc =>
            split
            · next hf => exact (hw ⟨he, hb, henc, hf⟩).elim
            · simp [finiteDyadic, hd]
          · simp [finiteDyadic, hd]
        · simp [finiteDyadic, hd]
      · simp [finiteDyadic, hd]
    have hv : d.toReal = toReal x := by rw [toReal_eq, hd]
    rw [hc]
    exact (roundDyadic_spec dst d).1 (by rw [hv]; exact hle) |>.imp id (by rw [hv]; exact id)

/-- A cast of a finite value inside the finite range of the destination is finite and is the
saturating rounding of the destination, for every pair of descriptors. -/
theorem cast_eq_saturating {src dst : FloatFormat} (x : Model src) (hx : isFinite x = true)
    (hle : |toReal x| ≤ toReal (posMaxFinite dst)) :
    isFinite (Model.cast src dst x) = true ∧
      toReal (Model.cast src dst x) = (Rounding.saturating dst).round (toReal x) := by
  have hfix : roundAt dst (toReal (posMaxFinite dst)) = toReal (posMaxFinite dst) :=
    roundAt_toReal_eq _ (isFinite_posMaxFinite dst)
  have hfixn : roundAt dst (-toReal (posMaxFinite dst)) = -toReal (posMaxFinite dst) := by
    rw [roundAt_neg, IEEERoundingMode.negate_nearest, hfix]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hle
  have hround : |roundAt dst (toReal x)| ≤ toReal (posMaxFinite dst) :=
    abs_le.mpr ⟨hfixn ▸ roundAt_mono dst hlo, hfix ▸ roundAt_mono dst hhi⟩
  obtain ⟨hfin, hval⟩ := cast_eq_roundAt_of_le x hx hround
  refine ⟨hfin, hval.trans ?_⟩
  change _ = clampAt dst (roundAt dst (toReal x))
  rw [clampAt_eq_self dst hround]

/-- A cast into a descriptor with a finer grid and at least the finite range of the source is
finite and exact, for every pair of descriptors. -/
theorem cast_exact_of_grid {src dst : FloatFormat} (x : Model src) (hx : isFinite x = true)
    (hfrac : src.fracWidth ≤ dst.fracWidth)
    (hmin : dst.minSubnormalExponent ≤ src.minSubnormalExponent)
    (hmax : toReal (posMaxFinite src) ≤ toReal (posMaxFinite dst)) :
    isFinite (Model.cast src dst x) = true ∧ toReal (Model.cast src dst x) = toReal x := by
  have hround : roundAt dst (toReal x) = toReal x :=
    Flocq.round_preserves_generic Flocq.nearestEven _
      (genericFormat_of_gridExtension hfrac hmin (toReal_genericFormat_of_isFinite x hx))
  have h := cast_eq_roundAt_of_le (dst := dst) x hx
    (by rw [hround]; exact (abs_toReal_le_posMaxFinite_of_isFinite x hx).trans hmax)
  rwa [hround] at h

/--
The clamped product of the working format, for finite factors and a finite bound `T ≥ 0`: it is
finite, and it is the exact product rounded onto the grid of the working format and clamped to
`[-T, T]`. This holds when the product overflows too: the machine clamps an infinity and the
formula clamps a number beyond the largest finite value, to the same bound.
-/
theorem toReal_clamp_mul (hW : W.isIEEE = true) {T x r : Model W} (hT : isFinite T = true)
    (hT0 : 0 ≤ toReal T) (hx : isFinite x = true) (hr : isFinite r = true) :
    isFinite (clamp (neg T) T (mul x r)) = true ∧
      toReal (clamp (neg T) T (mul x r)) =
        max (-toReal T) (min (toReal T) (roundAt W (toReal x * toReal r))) := by
  have hnT : isFinite (neg T) = true := by rw [isFinite_neg]; exact hT
  have hnTr : toReal (neg T) = -toReal T := toReal_neg T hT
  have hle : toReal (neg T) ≤ toReal T := by rw [hnTr]; linarith
  have hT' : toReal T ≤ toReal (posMaxFinite W) :=
    (le_abs_self _).trans (abs_toReal_le_posMaxFinite_of_isFinite T hT)
  rcases mul_eq_round_or_inf hW hx hr with ⟨hfin, hval⟩ | ⟨hbig, heq⟩
  · exact ⟨isFinite_clamp hnT hT hfin, by rw [toReal_clamp hnT hT hfin hle, hnTr, hval]⟩
  · by_cases hq : toReal x * toReal r < 0
    · rw [heq, ite_eq_left hq, clamp_negInf hW hnT]
      refine ⟨hnT, ?_⟩
      have hr0 : roundAt W (toReal x * toReal r) ≤ 0 := by
        have := roundAt_mono W hq.le
        rwa [roundAt_zero] at this
      rw [abs_of_nonpos hr0] at hbig
      rw [hnTr, min_eq_right (by linarith), max_eq_left (by linarith)]
    · rw [heq, ite_eq_right hq, clamp_posInf hW hnT hT]
      refine ⟨hT, ?_⟩
      have hr0 : 0 ≤ roundAt W (toReal x * toReal r) := by
        have := roundAt_mono W (not_lt.mp hq)
        rwa [roundAt_zero] at this
      rw [abs_of_nonneg hr0] at hbig
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]

/--
The clamped quotient of the working format, for a finite nonnegative dividend, a finite positive
divisor and finite bounds `low ≤ high`: it is finite, and it is the exact quotient rounded onto
the grid of the working format and clamped to `[low, high]`, also when the quotient overflows.
-/
theorem toReal_clamp_div (hW : W.isIEEE = true) {low high x y : Model W}
    (hlow : isFinite low = true) (hhigh : isFinite high = true)
    (hle : toReal low ≤ toReal high) (hx : isFinite x = true) (hx0 : 0 ≤ toReal x)
    (hy : isFinite y = true) (hy0 : 0 < toReal y) :
    isFinite (clamp low high (div x y)) = true ∧
      toReal (clamp low high (div x y)) =
        max (toReal low) (min (toReal high) (roundAt W (toReal x / toReal y))) := by
  have hq0 : 0 ≤ toReal x / toReal y := div_nonneg hx0 hy0.le
  rcases div_eq_round_or_inf hW hx hy (isZero_eq_false_of_toReal_ne_zero hy0.ne') with
    ⟨hfin, hval⟩ | ⟨hbig, heq⟩
  · exact ⟨isFinite_clamp hlow hhigh hfin, by rw [toReal_clamp hlow hhigh hfin hle, hval]⟩
  · rw [heq, ite_eq_right (not_lt.mpr hq0), clamp_posInf hW hlow hhigh]
    refine ⟨hhigh, ?_⟩
    rw [abs_of_nonneg hq0] at hbig
    have hfix : roundAt W (toReal (posMaxFinite W)) = toReal (posMaxFinite W) :=
      roundAt_toReal_eq _ (isFinite_posMaxFinite W)
    have hge : toReal (posMaxFinite W) ≤ roundAt W (toReal x / toReal y) :=
      hfix ▸ roundAt_mono W hbig.le
    have hhigh' : toReal high ≤ toReal (posMaxFinite W) :=
      (le_abs_self _).trans (abs_toReal_le_posMaxFinite_of_isFinite high hhigh)
    rw [min_eq_left (hhigh'.trans hge), max_eq_right hle]

/-- `+∞` over a finite positive value is `+∞`. -/
theorem div_posInf (hW : W.isIEEE = true) {y : Model W} (hy : isFinite y = true)
    (hy0 : 0 < toReal y) : div (posInf W) y = posInf W := by
  have hs := FloatFormat.supportsInfinity_eq_true_of_isIEEE W hW
  have hsign : signBit y = false := signBit_eq_false_of_toReal_pos hy hy0
  have hnone : chooseNaN2 (posInf W) y = none :=
    (chooseNaN2_eq_none_iff _ _).2 ⟨isNaN_posInf W, isNaN_eq_false_of_isFinite_eq_true y hy⟩
  rw [Proof.div_eq_spec, Spec.div,
    toDyadic?_eq_none_of_isInfinite_eq_true (isInfinite_posInf W hs)]
  simp [Spec.divSpecial, hnone, isInfinite_posInf W hs,
    isInfinite_eq_false_of_isFinite_eq_true y hy, hsign,
    nativeOverflow_eq_signedInf_of_isIEEE W hW]

/-- A finite nonzero value times `+∞` is the infinity with the sign of the value. -/
theorem mul_posInf (hW : W.isIEEE = true) {x : Model W} (hx : isFinite x = true)
    (hx0 : toReal x ≠ 0) :
    mul x (posInf W) = if toReal x < 0 then negInf W else posInf W := by
  have hs := FloatFormat.supportsInfinity_eq_true_of_isIEEE W hW
  have hnone : chooseNaN2 x (posInf W) = none :=
    (chooseNaN2_eq_none_iff _ _).2 ⟨isNaN_eq_false_of_isFinite_eq_true x hx, isNaN_posInf W⟩
  have hsign : signBit x = decide (toReal x < 0) := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · rw [signBit_eq_true_of_toReal_neg h, decide_eq_true h]
    · rw [signBit_eq_false_of_toReal_pos hx h, decide_eq_false (not_lt.mpr h.le)]
  rw [Proof.mul_eq_spec, Spec.mul,
    toDyadic?_eq_none_of_isInfinite_eq_true (isInfinite_posInf W hs)]
  simp [hnone, isInfinite_posInf W hs, isInfinite_eq_false_of_isFinite_eq_true x hx,
    isZero_eq_false_of_toReal_ne_zero hx0, hsign, nativeOverflow_eq_signedInf_of_isIEEE W hW]

/-- A fold of maxima is at least its start. -/
private theorem le_foldl_max (l : List ℝ) (init : ℝ) : init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact le_rfl
  | cons a l ih => exact (le_max_left init a).trans (ih _)

/-- The largest magnitude of a block of finite values is not negative. -/
theorem toReal_blockMax_nonneg (hW : W.isIEEE = true) {block : List (Model W)}
    (h : ∀ x ∈ block, isFinite x = true) : 0 ≤ toReal (blockMax block) := by
  rw [toReal_blockMax hW h]
  exact le_foldl_max _ _

/--
The constants of a block quantizer that computes in the binary format `work`, stores its block
scales in `scale` and its elements in `element`.
-/
structure Quantizer (work scale element : FloatFormat) where
  /-- The value that the largest magnitude of a block maps to: the largest element value. -/
  target : Model work
  /-- The least scale that is stored. -/
  floor : Model work
  /-- The greatest scale that is stored. -/
  ceiling : Model work

namespace Quantizer

variable (Q : Quantizer W S E)

/-- The block scale before it is stored: the largest magnitude over the target, over the outer
scale, clamped. Each quotient is rounded in the working format. -/
def scaled (outer : Model W) (block : List (Model W)) : Model W :=
  clamp Q.floor Q.ceiling (div (div (blockMax block) Q.target) outer)

/-- The stored block scale. -/
def scale (outer : Model W) (block : List (Model W)) : Model S :=
  Model.cast W S (Q.scaled outer block)

/-- The reciprocal of the total scale: the reciprocal of the outer scale over the stored block
scale, each quotient rounded in the working format. -/
def reciprocal (_Q : Quantizer W S E) (outer : Model W) (stored : Model S) : Model W :=
  div (div (posOne W) outer) (Model.cast S W stored)

/-- The stored element: the product with the reciprocal, rounded in the working format, clamped
to the target and rounded in the element format. -/
def element (reciprocal x : Model W) : Model E :=
  Model.cast W E (clamp (neg Q.target) Q.target (mul x reciprocal))

/-- The stored scale and the stored elements of one block under the outer scale `outer`. -/
def block (outer : Model W) (values : List (Model W)) : Model S × List (Model E) :=
  (Q.scale outer values,
    values.map (Q.element (Q.reciprocal outer (Q.scale outer values))))

/-- The words that a block stores: the encoding of its scale and the encodings of its elements,
as natural numbers. -/
def words (outer : Model W) (values : List (Model W)) : Nat × List Nat :=
  ((Q.block outer values).1.toNatBits, (Q.block outer values).2.map toNatBits)

/-! ## What the quantizer stores -/

section Theorems

variable (hW : W.isIEEE = true)
include hW

/--
The block scale before it is stored, for a finite block and a finite positive outer scale: with
`a` the largest magnitude of the block, it is `g (g (a / target) / outer)` clamped to
`[floor, ceiling]`, where `g` rounds onto the grid of the working format. The target is at least
one, so the first quotient is finite. When the second quotient overflows, the machine and the
formula both give the ceiling.
-/
theorem toReal_scaled (hT : isFinite Q.target = true) (hT1 : 1 ≤ toReal Q.target)
    (hfloor : isFinite Q.floor = true) (hceiling : isFinite Q.ceiling = true)
    (hle : toReal Q.floor ≤ toReal Q.ceiling) {outer : Model W} (ho : isFinite outer = true)
    (ho0 : 0 < toReal outer) {block : List (Model W)} (hb : ∀ x ∈ block, isFinite x = true) :
    isFinite (Q.scaled outer block) = true ∧
      toReal (Q.scaled outer block) =
        max (toReal Q.floor) (min (toReal Q.ceiling)
          (roundAt W (roundAt W (toReal (blockMax block) / toReal Q.target) / toReal outer))) := by
  have ha := isFinite_blockMax hb
  have ha0 := toReal_blockMax_nonneg hW hb
  have hT0 : 0 < toReal Q.target := lt_of_lt_of_le one_pos hT1
  have hTz := isZero_eq_false_of_toReal_ne_zero hT0.ne'
  have hbound : |toReal (blockMax block) / toReal Q.target| ≤ toReal (posMaxFinite W) := by
    rw [abs_of_nonneg (div_nonneg ha0 hT0.le)]
    exact (div_le_self ha0 hT1).trans
      ((le_abs_self _).trans (abs_toReal_le_posMaxFinite_of_isFinite _ ha))
  have hideal := isFinite_div_of_abs_div_le_posMaxFinite _ _ hW ha hT hTz hbound
  have hidealr := toReal_div_eq_roundAt_of_abs_div_le_posMaxFinite _ _ hW ha hT hTz hbound
  have hideal0 : 0 ≤ toReal (div (blockMax block) Q.target) := by
    rw [hidealr]
    have := roundAt_mono W (div_nonneg ha0 hT0.le)
    rwa [roundAt_zero] at this
  have h := toReal_clamp_div hW hfloor hceiling hle hideal hideal0 ho ho0
  rw [hidealr] at h
  exact h

/--
The stored block scale, for a finite block and a finite positive outer scale: it is finite, and
it is the saturating rounding in the scale format of the clamped scale of `toReal_scaled`. The
floor is not negative and the ceiling is inside the range of the scale format.
-/
theorem toReal_scale (hT : isFinite Q.target = true) (hT1 : 1 ≤ toReal Q.target)
    (hfloor : isFinite Q.floor = true) (hfloor0 : 0 ≤ toReal Q.floor)
    (hceiling : isFinite Q.ceiling = true) (hle : toReal Q.floor ≤ toReal Q.ceiling)
    (hS : toReal Q.ceiling ≤ toReal (posMaxFinite S)) {outer : Model W}
    (ho : isFinite outer = true) (ho0 : 0 < toReal outer) {block : List (Model W)}
    (hb : ∀ x ∈ block, isFinite x = true) :
    isFinite (Q.scale outer block) = true ∧
      toReal (Q.scale outer block) =
        (Rounding.saturating S).round (max (toReal Q.floor) (min (toReal Q.ceiling)
          (roundAt W (roundAt W (toReal (blockMax block) / toReal Q.target) / toReal outer)))) := by
  obtain ⟨hfin, hval⟩ := Q.toReal_scaled hW hT hT1 hfloor hceiling hle ho ho0 hb
  have hrange : |toReal (Q.scaled outer block)| ≤ toReal (posMaxFinite S) := by
    rw [hval, abs_of_nonneg (hfloor0.trans (le_max_left _ _))]
    exact (max_le hle (min_le_left _ _)).trans hS
  have h := cast_eq_saturating (dst := S) _ hfin hrange
  rw [hval] at h
  exact h

/--
The stored element, for a finite input and a finite reciprocal: it is finite, and it is the
saturating rounding in the element format of `g (x * r)` clamped to `[-target, target]`, where
`g` rounds onto the grid of the working format. When the product overflows, the machine and the
formula both give the target with the sign of the product.
-/
theorem toReal_element (hT : isFinite Q.target = true) (hT0 : 0 ≤ toReal Q.target)
    (hE : toReal Q.target ≤ toReal (posMaxFinite E)) {r x : Model W} (hr : isFinite r = true)
    (hx : isFinite x = true) :
    isFinite (Q.element r x) = true ∧
      toReal (Q.element r x) =
        (Rounding.saturating E).round (max (-toReal Q.target)
          (min (toReal Q.target) (roundAt W (toReal x * toReal r)))) := by
  obtain ⟨hfin, hval⟩ := toReal_clamp_mul hW hT hT0 hx hr
  have hrange : |toReal (clamp (neg Q.target) Q.target (mul x r))| ≤ toReal (posMaxFinite E) := by
    rw [hval]
    exact (abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩).trans hE
  have h := cast_eq_saturating (dst := E) _ hfin hrange
  rw [hval] at h
  exact h

/--
The reciprocal of the total scale, for a finite positive outer scale and a stored scale that the
working format holds as a finite positive value `s`: it is finite and equal to
`g (g (1 / outer) / s)`, or a quotient overflowed and it is `+∞`.
-/
theorem reciprocal_eq {outer : Model W} (ho : isFinite outer = true) (ho0 : 0 < toReal outer)
    {stored : Model S} (hs : isFinite (Model.cast S W stored) = true)
    (hs0 : 0 < toReal (Model.cast S W stored)) :
    (isFinite (Q.reciprocal outer stored) = true ∧
        toReal (Q.reciprocal outer stored) =
          roundAt W (roundAt W (1 / toReal outer) / toReal (Model.cast S W stored))) ∨
      Q.reciprocal outer stored = posInf W := by
  have hsz := isZero_eq_false_of_toReal_ne_zero hs0.ne'
  have hone0 : 0 ≤ 1 / toReal outer := div_nonneg zero_le_one ho0.le
  unfold reciprocal
  rcases div_eq_round_or_inf hW (isFinite_posOne W) ho
    (isZero_eq_false_of_toReal_ne_zero ho0.ne') with ⟨hfin, hval⟩ | ⟨-, heq⟩
  · rw [toReal_posOne] at hval
    have hc0 : 0 ≤ toReal (div (posOne W) outer) := by
      rw [hval]
      have := roundAt_mono W hone0
      rwa [roundAt_zero] at this
    rcases div_eq_round_or_inf hW hfin hs hsz with ⟨hfin2, hval2⟩ | ⟨-, heq2⟩
    · exact Or.inl ⟨hfin2, by rw [hval2, hval]⟩
    · exact Or.inr (by rw [heq2, ite_eq_right (not_lt.mpr (div_nonneg hc0 hs0.le))])
  · rw [toReal_posOne, ite_eq_right (not_lt.mpr hone0)] at heq
    exact Or.inr (by rw [heq, div_posInf hW hs hs0])

/--
The stored element under a reciprocal that overflowed to `+∞`, for a finite nonzero input: the
product is an infinity, so the element is the target with the sign of the input, rounded in the
element format. A zero input times `+∞` is a NaN, as on a machine, and has no theorem here.
-/
theorem toReal_element_posInf (hT : isFinite Q.target = true) (hT0 : 0 ≤ toReal Q.target)
    (hE : toReal Q.target ≤ toReal (posMaxFinite E)) {x : Model W} (hx : isFinite x = true)
    (hx0 : toReal x ≠ 0) :
    isFinite (Q.element (posInf W) x) = true ∧
      toReal (Q.element (posInf W) x) =
        (Rounding.saturating E).round
          (if toReal x < 0 then -toReal Q.target else toReal Q.target) := by
  have hnT : isFinite (neg Q.target) = true := by rw [isFinite_neg]; exact hT
  have hnTr : toReal (neg Q.target) = -toReal Q.target := toReal_neg Q.target hT
  unfold element
  rw [mul_posInf hW hx hx0]
  by_cases hneg : toReal x < 0
  · rw [ite_eq_left hneg, ite_eq_left hneg, clamp_negInf hW hnT, ← hnTr]
    exact cast_eq_saturating (dst := E) _ hnT
      (by rw [hnTr, abs_neg, abs_of_nonneg hT0]; exact hE)
  · rw [ite_eq_right hneg, ite_eq_right hneg, clamp_posInf hW hnT hT]
    exact cast_eq_saturating (dst := E) _ hT (by rw [abs_of_nonneg hT0]; exact hE)

end Theorems

end Quantizer

end FloatLib.Floats.Formats.Block.Working
