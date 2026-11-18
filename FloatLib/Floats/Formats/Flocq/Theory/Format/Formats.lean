/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Core

/-!
# Flocq-style formats (FIX / FLX / FLT)

Three real-valued format families come from three exponent-selection functions `fexp : ℤ → ℤ`:

- `FIX` is a fixed-exponent grid,
- `FLX` has fixed precision and unbounded exponents,
- `FLT` has fixed precision, a lower exponent bound, and gradual underflow.

With precision `prec`, `FLX` picks `e - prec` for magnitude `e` and `FLT` picks
`max (e - prec) emin`, while `FIX` ignores `e` and always picks `emin`. `FLT` has no upper exponent
bound, so it never overflows. Executable binary formats with infinities, NaNs, and signed zeros
are defined in `FloatLib/Floats/Formats/BinaryInterchange/`.

References:

- S. Boldo and G. Melquiond, “Flocq: A Unified Library for Proving Floating-Point Algorithms
  in Coq,” ARITH 2011, pp. 243–252, §§III-C–III-D (format predicates and their
  exponent-function descriptions), DOI: 10.1109/ARITH.2011.40.
- IEEE Standard for Floating-Point Arithmetic (IEEE 754-2019)
-/

@[expose] public section


namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/--
A positive number of radix digits for FLX, FLT, and FTZ formats.

Raw exponent functions remain available for algebraic proofs, but callers accepting an integer
configuration should first use `FormatPrecision.ofInt?`.  This prevents a zero or negative
precision from being silently reinterpreted through an absolute-value conversion.

This is Mathlib's proof-erased positive-natural carrier rather than another project-local
structure.
-/
abbrev FormatPrecision := PNat

namespace FormatPrecision

/-- Convert a proof-carrying format precision to the integer parameter used by exponent formulas. -/
def toInt (precision : FormatPrecision) : ℤ := (precision : ℕ)

/-- Check a natural-number precision at a configuration boundary. -/
def ofNat? (digits : ℕ) : Option FormatPrecision :=
  if h : 0 < digits then some ⟨digits, h⟩ else none

/-- Check an integer precision, rejecting zero and every negative value. -/
def ofInt? (digits : ℤ) : Option FormatPrecision :=
  if h : 0 < digits then
    some ⟨digits.toNat, by
      have hcast : (digits.toNat : ℤ) = digits := Int.toNat_of_nonneg h.le
      have : (0 : ℤ) < (digits.toNat : ℤ) := by simpa [hcast] using h
      exact_mod_cast this⟩
  else none

/-- A checked precision remains positive after conversion to the integer exponent parameter. -/
@[simp] theorem toInt_pos (precision : FormatPrecision) : 0 < precision.toInt := by
  change (0 : ℤ) < ((precision : ℕ) : ℤ)
  exact_mod_cast precision.2

/-- Natural precision validation fails at zero and nowhere else. -/
@[simp] theorem ofNat?_eq_none_iff (digits : ℕ) :
    ofNat? digits = none ↔ digits = 0 := by
  simp [ofNat?]

/-- Integer precision validation fails if and only if the input is nonpositive. -/
@[simp] theorem ofInt?_eq_none_iff (digits : ℤ) :
    ofInt? digits = none ↔ digits ≤ 0 := by
  simp [ofInt?]

end FormatPrecision

/--
`fixExp emin` is the simplest exponent-selection function: it always returns the same exponent.

This is Flocq's `FIX_exp`. It describes values living on a single fixed grid
$\beta^{\mathtt{emin}}\mathbb{Z}$, as in fixed-point arithmetic or quantization.
-/
def fixExp (emin : ℤ) : ℤ → ℤ := fun _ => emin

/--
`fixExp emin` satisfies the exponent-validity axioms `ValidExp`. Registering the result as an
instance lets the FIX theorems reuse the generic format lemmas shared with FLX and FLT.
-/
instance fixValidExp (emin : ℤ) : ValidExp (fixExp emin) where
  flocq_valid := by
    intro k
    constructor
    · intro h; simp only [fixExp] at h ⊢; exact Int.le_of_lt h
    · intro _; simp [fixExp]

/-- The constant FIX exponent function is monotone. -/
instance fixMonotoneExp (emin : ℤ) : MonotoneExp (fixExp emin) where
  monotone := by simp [fixExp]

/-- The constant FIX exponent function selects the same exponent in successive bins. -/
instance fixBoundedExpGrowth (emin : ℤ) : BoundedExpGrowth (fixExp emin) where
  bounded_growth := by simp [fixExp]

/-- The ULP at zero for a fixed-point grid is its fixed grid step. -/
theorem ulp_zero_fix (emin : ℤ) :
    ulp β (fixExp emin) 0 = bpow β emin :=
  ulp.zero_of_isNegligibleExp β (fixExp emin) (m := emin) le_rfl

/--
`FIXFormat emin x` says that `x` is exactly representable on the fixed grid with exponent `emin`.

The predicate is phrased through an existential `FloatRep β` so that it composes with the rest of
the rounding model (`toReal`, ULP bounds and so on).
-/
def FIXFormat (emin : ℤ) (x : ℝ) : Prop :=
  ∃ f : FloatRep β, x = toReal f ∧ f.exponent = emin

/--
`flxExp prec` is the unbounded-exponent family.

This is Flocq's `FLX_exp`: a floating-point format with no exponent bounds and mantissa precision
`prec`. It is a convenient intermediate model for proofs because it removes the underflow and
overflow corner cases while still tracking mantissa rounding.
-/
def flxExp (prec : ℤ) : ℤ → ℤ := fun e => e - prec

/--
`flxExp prec` satisfies `ValidExp` for positive precision.
-/
theorem validExp_flx (prec : ℤ) (h : 0 < prec) : ValidExp (flxExp prec) where
  flocq_valid := by
    intro k
    constructor
    · intro _
      change k + 1 - prec ≤ k
      omega
    · intro H
      change k ≤ k - prec at H
      omega

/-- `flxExp prec` satisfies the generic exponent axioms if and only if `prec` is positive. -/
theorem validExp_flx_iff (prec : ℤ) : ValidExp (flxExp prec) ↔ 0 < prec := by
  constructor
  · intro hvalid
    by_contra hprec
    have hsecond := (hvalid.flocq_valid 0).2 (show 0 ≤ 0 - prec by omega)
    have hbound := hsecond.1
    change 0 - prec + 1 - prec ≤ 0 - prec at hbound
    omega
  · exact validExp_flx prec

namespace FormatPrecision

/-- The unbounded exponent selector associated with a checked precision. -/
def flxExp (precision : FormatPrecision) : ℤ → ℤ := Flocq.flxExp precision.toInt

/-- A checked precision automatically discharges the FLX exponent-validity obligation. -/
instance flxExpValid (precision : FormatPrecision) : ValidExp precision.flxExp :=
  validExp_flx precision.toInt precision.toInt_pos

end FormatPrecision


/-- The FLX exponent selector is monotone for every precision parameter. -/
theorem monotoneExp_flx (prec : ℤ) : MonotoneExp (flxExp prec) where
  monotone _ _ hk := sub_le_sub_right hk prec

/-- The FLX exponent selector has bounded one-step growth. -/
theorem boundedExpGrowth_flx (prec : ℤ) : BoundedExpGrowth (flxExp prec) where
  bounded_growth := by simp [flxExp]

/--
Exact representability predicate for `FLX`.

The precision is positive, and $x=m\beta^e$ for an integer mantissa satisfying
$|m|<\beta^{\mathtt{prec}}$.
-/
def FLXFormat (prec : ℤ) (x : ℝ) : Prop :=
  0 < prec ∧
    ∃ f : FloatRep β, x = toReal f ∧ Int.natAbs f.mantissa < β.base ^ prec.toNat

/-- With nonpositive precision, the bounded-mantissa predicate `FLXFormat` holds for no value. -/
theorem not_flxFormat_of_nonpos (prec : ℤ) (hprec : prec ≤ 0) (x : ℝ) :
    ¬FLXFormat (β := β) prec x := by
  simp [FLXFormat, not_lt_of_ge hprec]

/-- The unbounded FLX exponent function has no negligible exponent. -/
theorem negligibleExp_flx (prec : ℤ) (hprec : 0 < prec) :
    negligibleExp (flxExp prec) = none := by
  rw [negligibleExp_eq_none_iff]
  rintro ⟨n, hn⟩
  change n ≤ n - prec at hn
  omega

/-- Consequently, the generic ULP of zero is zero for FLX. -/
theorem ulp_zero_flx (prec : ℤ) (hprec : 0 < prec) :
    @ulp β (flxExp prec) (validExp_flx prec hprec) 0 = 0 := by
  simp [ulp, negligibleExp_flx prec hprec]

/--
`fltExp emin prec` is the lower-exponent-bounded family with gradual underflow.

This is Flocq's `FLT_exp`. The exponent is bounded below by `emin` but has no upper bound, so the
format models gradual underflow but not overflow, infinities, or NaNs. Gradual underflow is
captured by taking `max (e - prec) emin`.
-/
def fltExp (emin prec : ℤ) : ℤ → ℤ := fun e => max (e - prec) emin

/--
`fltExp emin prec` satisfies `ValidExp` for positive precision.

This validity witness connects proofs to an executable binary descriptor through
`BinaryInterchange.Model.fexpOf` and `BinaryInterchange.Model.roundAt`.
-/
theorem validExp_flt (emin prec : ℤ) (h : 0 < prec) : ValidExp (fltExp emin prec) where
  flocq_valid := by
    intro k
    constructor
    · intro hk
      have hk' : max (k - prec) emin < k := by simpa [fltExp] using hk
      have hemin_le : emin ≤ k :=
        le_of_lt (lt_of_le_of_lt (le_max_right (k - prec) emin) hk')
      have hleft_le : k + 1 - prec ≤ k := by omega
      simpa [fltExp] using (max_le_iff).2 ⟨hleft_le, hemin_le⟩
    · intro hk
      have hk' : k ≤ max (k - prec) emin := by simpa [fltExp] using hk
      have hk_cases : k ≤ k - prec ∨ k ≤ emin := (le_max_iff).1 hk'
      have hprec0 : 0 ≤ prec := le_of_lt h
      cases hk_cases with
      | inl hk_le =>
          exfalso
          have : k - prec < k := by omega
          exact (not_le_of_gt this) hk_le
      | inr hk_le_emin =>
          have hk_fexp : fltExp emin prec k = emin := by
            apply max_eq_right
            have : k - prec ≤ emin - prec := sub_le_sub_right hk_le_emin prec
            exact this.trans (sub_le_self emin hprec0)
          constructor
          · have hleft : emin + 1 - prec ≤ emin := by omega
            simp only [hk_fexp, ge_iff_le]
            dsimp [fltExp]
            exact (max_le_iff).2 ⟨hleft, le_rfl⟩
          · intro l hl
            have hl' : l ≤ emin := by simpa [hk_fexp] using hl
            have hle : l - prec ≤ emin := (sub_le_self l hprec0).trans hl'
            rw [hk_fexp]
            dsimp [fltExp]
            exact max_eq_right hle

/-- `fltExp emin prec` satisfies the exponent axioms if and only if the precision is positive. -/
theorem validExp_flt_iff (emin prec : ℤ) : ValidExp (fltExp emin prec) ↔ 0 < prec := by
  constructor
  · intro hvalid
    by_contra hprec
    have hk : emin ≤ fltExp emin prec emin := by simp [fltExp]
    have hnext := ((hvalid.flocq_valid emin).2 hk).1
    have hlower : fltExp emin prec (fltExp emin prec emin + 1) ≥
        fltExp emin prec emin + 1 := by
      apply le_max_of_le_left
      omega
    omega
  · exact validExp_flt emin prec

namespace FormatPrecision

/-- The gradual-underflow exponent selector associated with a checked precision. -/
def fltExp (precision : FormatPrecision) (emin : ℤ) : ℤ → ℤ :=
  Flocq.fltExp emin precision.toInt

/-- A checked precision automatically discharges the gradual-underflow validity obligation. -/
instance fltExpValid (precision : FormatPrecision) (emin : ℤ) :
    ValidExp (precision.fltExp emin) :=
  validExp_flt emin precision.toInt precision.toInt_pos

end FormatPrecision


/-- The gradual-underflow FLT exponent selector has bounded one-step growth. -/
theorem boundedExpGrowth_flt (emin prec : ℤ) :
    BoundedExpGrowth (fltExp emin prec) where
  bounded_growth := by
    intro k
    simpa [fltExp] using abs_max_sub_max_le_abs (k + 1 - prec) (k - prec) emin

/-- The gradual-underflow FLT exponent selector is monotone. -/
theorem monotoneExp_flt (emin prec : ℤ) : MonotoneExp (fltExp emin prec) where
  monotone := by
    intros k1 k2 hk
    exact max_le_max (sub_le_sub_right hk prec) le_rfl

/--
Exact representability predicate for `FLT`.

The precision is positive, and $x=m\beta^e$ with $|m|<\beta^{\mathtt{prec}}$ and
$\mathtt{emin}\le e$. In particular, every nonzero value has magnitude at least
$\beta^{\mathtt{emin}}$.
-/
def FLTFormat (emin prec : ℤ) (x : ℝ) : Prop :=
  0 < prec ∧
    ∃ f : FloatRep β, x = toReal f ∧
      Int.natAbs f.mantissa < β.base ^ prec.toNat ∧ emin ≤ f.exponent

/-- With nonpositive precision, the bounded-mantissa predicate `FLTFormat` holds for no value. -/
theorem not_fltFormat_of_nonpos (emin prec : ℤ) (hprec : prec ≤ 0) (x : ℝ) :
    ¬FLTFormat (β := β) emin prec x := by
  simp [FLTFormat, not_lt_of_ge hprec]

/-- FLT has a negligible-exponent witness at `emin`. -/
theorem exists_negligibleExp_flt (emin prec : ℤ) :
    ∃ n, IsNegligibleExp (fltExp emin prec) n := by
  refine ⟨emin, ?_⟩
  exact le_max_right _ _

/-- The ULP at zero for FLT is the smallest grid step $\beta^{\mathtt{emin}}$. -/
theorem ulp_zero_flt (emin prec : ℤ) (hprec : 0 < prec) :
    @ulp β (fltExp emin prec) (validExp_flt emin prec hprec) 0 = bpow β emin := by
  let : ValidExp (fltExp emin prec) := validExp_flt emin prec hprec
  rw [ulp.zero_of_isNegligibleExp β (fltExp emin prec) (le_max_right (emin - prec) emin)]
  rw [fltExp, max_eq_right (sub_le_self emin hprec.le)]

end FloatLib.Floats.Formats.Flocq
