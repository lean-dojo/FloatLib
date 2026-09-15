/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Accumulation
public import FloatLib.Floats.Formats.Posit.Quire.Arithmetic.Proof
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Constants

/-!
# Correctness of the configured posit quire interface

The public raw-word operations are lossless, posit-to-quire conversion preserves exact rational
meaning, and the distinguished zero and NaR values are preserved across both conversion
directions. The fold theorems at the end transport the standard capacity guarantees to
accumulation loops written against the configured carrier.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 5.11, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit.Quire

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Re-encoding a configured quire's complete bit pattern preserves it. -/
@[simp, grind =] theorem ofNatBits_toNatBits (value : Formats.Posit.Quire.Model format) :
    ofNatBits value.toNatBits = value :=
  Formats.Posit.Quire.Model.ofNatBits_toNatBits value

/-- An in-range unsigned word is unchanged by configured-quire encoding. -/
@[simp, grind =] theorem toNatBits_ofNatBits_of_lt (bits : Nat)
    (bits_lt : bits < 2 ^ Formats.Posit.Quire.width format) :
    toNatBits (ofNatBits (format := format) bits) = bits :=
  Formats.Posit.Quire.Model.toNatBits_ofNatBits_of_lt format bits bits_lt

/-- Converting posit NaR to its associated quire produces the reserved quire NaR. -/
@[simp, grind =] theorem pToQ_nar :
    pToQ
        (ExecFloat.Posit.nar
          (format := format) (plan := plan) (code := code)) =
      nar (format := format) := by
  change
    Formats.Posit.Quire.Model.pToQ
        (ExecFloat.Posit.toModel
          (ExecFloat.Posit.nar
            (format := format) (plan := plan) (code := code))) =
      Formats.Posit.Quire.Model.nar format
  change
    Formats.Posit.Quire.Model.pToQ
        (Configured.Family.toModel
          (Configured.Family.ofModel
            (Formats.Posit.Model.nar format))) =
      Formats.Posit.Quire.Model.nar format
  rw [Configured.Family.toModel_ofModel,
    Formats.Posit.Quire.Model.pToQ_nar]

/-- Converting posit zero to its associated quire produces the all-zero quire. -/
@[simp, grind =] theorem pToQ_zero :
    pToQ
        (ExecFloat.Posit.zero
          (format := format) (plan := plan) (code := code)) =
      zero (format := format) := by
  change
    Formats.Posit.Quire.Model.pToQ
        (ExecFloat.Posit.toModel
          (ExecFloat.Posit.zero
            (format := format) (plan := plan) (code := code))) =
      Formats.Posit.Quire.Model.zero format
  change
    Formats.Posit.Quire.Model.pToQ
        (Configured.Family.toModel
          (Configured.Family.ofModel
            (Formats.Posit.Model.zero format))) =
      Formats.Posit.Quire.Model.zero format
  rw [Configured.Family.toModel_ofModel,
    Formats.Posit.Quire.Model.pToQ_zero]

/--
Configured posit-to-quire conversion preserves the complete optional exact rational meaning.

The theorem is unconditional: ordinary values are proved to fit the standard quire exactly, and
posit NaR maps to quire NaR.
-/
@[simp, grind =]
theorem toRat?_pToQ
    (value : FloatLib.Floats.ExecFloat
      (Configured.Family format code plan)) :
    toRat? (pToQ value) = ExecFloat.Posit.toRat? value :=
  Formats.Posit.Quire.Model.toRat?_pToQ
    (ExecFloat.Posit.toModel value)

/-- Rounding the reserved quire NaR to a posit produces posit NaR. -/
@[simp, grind =] theorem qToP_nar :
    qToP (plan := plan) (code := code)
        (nar (format := format)) =
      ExecFloat.Posit.nar
        (format := format) (plan := plan) (code := code) := by
  change
    ExecFloat.Posit.ofModel
        (plan := plan) (code := code)
        (Formats.Posit.Quire.Model.qToP
          (Formats.Posit.Quire.Model.nar format)) =
      ExecFloat.Posit.nar
        (format := format) (plan := plan) (code := code)
  rw [Formats.Posit.Quire.Model.qToP_nar]
  rfl

/-- Rounding the all-zero quire to a posit produces the unique posit zero. -/
@[simp, grind =] theorem qToP_zero :
    qToP (plan := plan) (code := code)
        (zero (format := format)) =
      ExecFloat.Posit.zero
        (format := format) (plan := plan) (code := code) := by
  change
    ExecFloat.Posit.ofModel
        (plan := plan) (code := code)
        (Formats.Posit.Quire.Model.qToP
          (Formats.Posit.Quire.Model.zero format)) =
      ExecFloat.Posit.zero
        (format := format) (plan := plan) (code := code)
  rw [Formats.Posit.Quire.Model.qToP_zero]
  rfl

/-! ## Accumulation loops -/

/-- Configured exact values are the model's exact values of the decoded posits. -/
theorem exactValues?_eq_model
    (addends : List (FloatLib.Floats.ExecFloat (Configured.Family format code plan))) :
    exactValues? addends =
      Formats.Posit.Quire.Model.exactValues? (addends.map ExecFloat.Posit.toModel) := by
  induction addends with
  | nil => rfl
  | cons addend rest ih =>
      simp only [exactValues?, Formats.Posit.Quire.Model.exactValues?, List.map_cons, ih]
      rfl

/-- Configured exact products are the model's exact products of the decoded posit pairs. -/
theorem exactProducts?_eq_model
    (pairs : List (FloatLib.Floats.ExecFloat (Configured.Family format code plan) ×
      FloatLib.Floats.ExecFloat (Configured.Family format code plan))) :
    exactProducts? pairs =
      Formats.Posit.Quire.Model.exactProducts?
        (pairs.map fun pair => (ExecFloat.Posit.toModel pair.1, ExecFloat.Posit.toModel pair.2)) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp only [exactProducts?, Formats.Posit.Quire.Model.exactProducts?, List.map_cons, ih]
      rfl

/--
Folding `qMulAdd` over fewer than `2^31` pairs of ordinary configured posits, starting from the
zero quire, is exact: the result is not NaR and denotes the exact rational sum of the products.

`exactProducts? pairs = some products` records that no input is NaR and identifies the exact
products. Callers need no additional bounds on the quire coefficients.
-/
theorem toRat?_foldl_qMulAdd_zero
    (pairs : List (FloatLib.Floats.ExecFloat (Configured.Family format code plan) ×
      FloatLib.Floats.ExecFloat (Configured.Family format code plan)))
    (products : List Rat)
    (hproducts : exactProducts? pairs = some products)
    (hlength : pairs.length < Formats.Posit.Quire.Model.productSumTermLimit) :
    toRat?
        (pairs.foldl (fun quire pair => qMulAdd quire pair.1 pair.2)
          (zero (format := format))) =
      some products.sum := by
  rw [exactProducts?_eq_model] at hproducts
  have hfold :=
    Formats.Posit.Quire.Model.toRat?_foldMulAdd_zero
      (pairs.map fun pair => (ExecFloat.Posit.toModel pair.1, ExecFloat.Posit.toModel pair.2))
      products hproducts (by simpa using hlength)
  simpa [Formats.Posit.Quire.Model.foldMulAdd, List.foldl_map, toRat?, zero, qMulAdd]
    using hfold

/--
Folding `qAddP` over fewer than `2^(23 + 4n)` ordinary configured posits, starting from the zero
quire, is exact.
-/
theorem toRat?_foldl_qAddP_zero
    (addends : List (FloatLib.Floats.ExecFloat (Configured.Family format code plan)))
    (values : List Rat)
    (hvalues : exactValues? addends = some values)
    (hlength : addends.length < Formats.Posit.Quire.Model.positSumTermLimit format) :
    toRat? (addends.foldl qAddP (zero (format := format))) = some values.sum := by
  rw [exactValues?_eq_model] at hvalues
  have hfold :=
    Formats.Posit.Quire.Model.toRat?_foldAddP_zero
      (addends.map ExecFloat.Posit.toModel) values hvalues (by simpa using hlength)
  show Formats.Posit.Quire.Model.toRat?
      (addends.foldl
        (fun quire addend =>
          Formats.Posit.Quire.Model.qAddP quire (ExecFloat.Posit.toModel addend))
        (Formats.Posit.Quire.Model.zero format)) =
    some values.sum
  simpa [Formats.Posit.Quire.Model.foldAddP, List.foldl_map] using hfold

end ExecFloat.Posit.Quire
end FloatLib.Floats
