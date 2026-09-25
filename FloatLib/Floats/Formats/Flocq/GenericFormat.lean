/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Generic
public import FloatLib.Numerics.Core.Representation
public import FloatLib.Numerics.Quantization.Spec

/-!
# Flocq-style generic formats as ordinary FloatLib formats

The radix/exponent-function model of `FloatRep` supplies a representation-independent
`EncodedFormat` interface.

The runtime code is a canonical integer-mantissa/integer-exponent pair.  Its proof of canonicality
is erased by Lean, while its denotation is the corresponding real number.  The central theorem
`representable_iff_genericFormat` proves that common-system representability is exactly
`genericFormat`.

The definitions mirror the separation in Flocq between:

- `generic_format`, which characterizes representable real values;
- `Valid_exp`, which constrains exponent-selection functions; and
- a rounding operator proved to return a generic-format value.

Primary references:

- S. Boldo and G. Melquiond, “Flocq: A Unified Library for Proving Floating-Point Algorithms in
  Coq,” ARITH 2011, pp. 243–252, §III-D, DOI 10.1109/ARITH.2011.40.
- Flocq 4.2.2 release, `src/Core/Generic_fmt.v`, definitions `generic_format` and `Valid_exp`:
  <https://flocq.gitlabpages.inria.fr/releases/flocq-4.2.2.tar.gz>.
- Flocq project documentation: <https://flocq.gitlabpages.inria.fr/flocq/>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

open FloatLib.Numerics

/--
Type-level identity of the generic radix/exponent-function format.

The constructor carries no format data.  The radix and exponent function are type parameters, so
specialized users do not pass a runtime descriptor through arithmetic kernels.
-/
inductive GenericFormat (β : Numerics.Radix) (fexp : ℤ → ℤ) where
  | format

/-- Canonical mantissa/exponent codes of a valid Flocq-style generic format. -/
abbrev CanonicalCode (β : Numerics.Radix) (fexp : ℤ → ℤ) [ValidExp fexp] :=
  { value : FloatRep β // Canonical β fexp value }

instance (β : Numerics.Radix) (fexp : ℤ → ℤ) [ValidExp fexp] :
    EncodedFormat (GenericFormat β fexp) where
  Code := CanonicalCode β fexp
  Scalar := ℝ

noncomputable instance (β : Numerics.Radix) (fexp : ℤ → ℤ) [ValidExp fexp] :
    FormatSemantics (GenericFormat β fexp) where
  denote code := .finite (toReal code.1)

variable (β : Numerics.Radix) (fexp : ℤ → ℤ) [ValidExp fexp]

/-- A canonical code represents exactly the real obtained from its mantissa and exponent. -/
@[simp] theorem represents_iff (code : FormatCode (GenericFormat β fexp)) (x : ℝ) :
    FormatRepresents (GenericFormat β fexp) code x ↔ toReal code.1 = x := by
  change
    NumericalValue.finite (toReal code.1) = NumericalValue.finite x ↔
      toReal code.1 = x
  simp

/--
Common FloatLib representability coincides exactly with the Flocq-style `generic_format`
predicate.
-/
theorem representable_iff_genericFormat (x : ℝ) :
    (formatSystem (GenericFormat β fexp)).Representable x ↔
      genericFormat β fexp x := by
  constructor
  · rintro ⟨code, hcode⟩
    have hvalue : toReal code.1 = x :=
      (represents_iff β fexp code x).1 hcode
    rw [← hvalue]
    exact generic_format_of_canonical code.1 code.2
  · intro hx
    obtain ⟨value, hvalue, hcanonical⟩ :=
      canonical_exists_of_generic (β := β) (fexp := fexp) hx
    exact ⟨⟨value, hcanonical⟩, (represents_iff β fexp _ x).2 hvalue.symm⟩

/--
Choose a canonical code for a value already known to belong to the generic format.

This function is proof-facing and noncomputable.  Concrete fixed-precision format families supply
their own executable packing kernels.
-/
noncomputable def encodeGeneric (x : ℝ) (hx : genericFormat β fexp x) :
    FormatCode (GenericFormat β fexp) :=
  let witness := canonical_exists_of_generic (β := β) (fexp := fexp) hx
  ⟨Classical.choose witness, (Classical.choose_spec witness).2⟩

/-- `encodeGeneric` denotes the real value from which it was chosen. -/
theorem encodeGeneric_represents (x : ℝ) (hx : genericFormat β fexp x) :
    FormatRepresents (GenericFormat β fexp) (encodeGeneric β fexp x hx) x := by
  apply (represents_iff β fexp _ x).2
  exact (Classical.choose_spec
    (canonical_exists_of_generic (β := β) (fexp := fexp) hx)).1.symm

/-- Round a real input and choose a canonical code for the rounded generic-format value. -/
noncomputable def roundCode (mode : RoundingMode) (x : ℝ) :
    FormatCode (GenericFormat β fexp) :=
  encodeGeneric β fexp
    (mode.round (β := β) (fexp := fexp) x)
    (generic_format_round mode.roundingFunction x)

/-- The selected code denotes exactly the standard-mode rounded result. -/
theorem roundCode_represents (mode : RoundingMode) (x : ℝ) :
    FormatRepresents (GenericFormat β fexp) (roundCode β fexp mode x)
      (mode.round (β := β) (fexp := fexp) x) := by
  exact encodeGeneric_represents β fexp _ _

/-- Relational quantization contract for standard Flocq-style rounding modes. -/
noncomputable def roundingSpec :
    Numerics.Quantization.Spec RoundingMode ℝ
      (FormatCode (GenericFormat β fexp)) :=
  Numerics.Quantization.Spec.represents
    (formatSystem (GenericFormat β fexp))
    fun mode x => mode.round (β := β) (fexp := fexp) x

/-- `roundCode` implements the common relational quantization contract. -/
theorem roundCode_refines :
    (roundingSpec β fexp).Implements (roundCode β fexp) := by
  intro mode x
  exact roundCode_represents β fexp mode x

/-- Rounding an already representable real denotes that same real. -/
theorem roundCode_of_representable {x : ℝ}
    (hx : (formatSystem (GenericFormat β fexp)).Representable x) :
    FormatRepresents (GenericFormat β fexp)
      (roundCode β fexp .nearestEven x) x := by
  rw [representable_iff_genericFormat β fexp x] at hx
  simpa [RoundingMode.round_eq_of_generic .nearestEven hx] using
    roundCode_represents β fexp .nearestEven x

end FloatLib.Floats.Formats.Flocq
