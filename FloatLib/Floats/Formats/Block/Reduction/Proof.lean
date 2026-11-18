/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Reduction
public import FloatLib.Floats.Formats.Block.CodedDot
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError

/-!
# Error of finite binary reduction states

OCP MX v1.0, §§6.1–6.2, permits finite intermediate precision. These bounds
reuse the binary summation theorem, retaining finite partial sums as explicit
hypotheses. The product projection can have any proved mixed-error contract;
nearest-even projection supplies a concrete instance.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

open FloatLib.Numerics FloatLib.Floats.Formats.BinaryInterchange

/-- Exact decoding of a finite binary word has its rational finite value. -/
theorem Codec.map_decodeModel_of_isFinite {fmt : FloatFormat} (word : Model fmt)
    (hfinite : Model.isFinite word = true) :
    (Codec.decodeModel word).map SignedRat.value =
      .finite (finiteValue (Codec.decodeModel word)) := by
  obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite hfinite
  simp [Codec.decodeModel, Model.exactNumericalSystem, hd, finiteValue]

namespace Reduction

/--
Absolute error of a zero-seeded finite binary fold with possibly inexact terms.
The first addition is exact, hence the exponent `values.length - 1`.
-/
noncomputable def binaryErrorBound (fmt : FloatFormat) (values : List Rat)
    (rel err : Rat → ℝ) : ℝ :=
  ((1 + Model.unitRoundoffAt fmt) ^ (values.length - 1) - 1) *
      (values.map fun q : Rat => |(q : ℝ)|).sum +
    (1 + Model.unitRoundoffAt fmt) ^ (values.length - 1) *
      (values.map fun q => rel q * |(q : ℝ)| + err q).sum

/--
OCP MX v1.0, §6.1: finite binary accumulation has the existing cancellation-safe
absolute bound, for every ordered list and every proved product projection.
-/
theorem mixedError_fold_binary (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (project : NumericalValue Rat → Model fmt) (values : List Rat) (rel err : Rat → ℝ)
    (hfinite : ∀ word ∈ values.scanl
      (fun sum q => Model.add sum (project (.finite q))) (Model.zero fmt false),
      Model.isFinite word = true)
    (hterm : ∀ q ∈ values, Model.isFinite (project (.finite q)) = true)
    (eterm : ∀ q ∈ values,
      MixedError (Model.toReal (project (.finite q))) (q : ℝ) (rel q) (err q)) :
    MixedError (Model.toReal ((binary fmt project).fold (values.map .finite)))
      (values.map fun q : Rat => (q : ℝ)).sum 0 (binaryErrorBound fmt values rel err) := by
  simpa only [fold, binary, List.foldl_map, binaryErrorBound, List.sum_map_add] using
    Model.mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero hfmt
      (Model.toReal_zero fmt false) hfinite hterm eterm

/--
OCP MX v1.0, §6.1: final nearest-even output rounding composes with the
finite-accumulator absolute error, including cancellation and subnormal outputs.
-/
theorem mixedError_round_binary (fmt output : FloatFormat)
    (hfmt : fmt.isIEEE = true) (houtput : output.isIEEE = true)
    (project : NumericalValue Rat → Model fmt) (values : List Rat) (rel err : Rat → ℝ)
    (hfinite : ∀ word ∈ values.scanl
      (fun sum q => Model.add sum (project (.finite q))) (Model.zero fmt false),
      Model.isFinite word = true)
    (hterm : ∀ q ∈ values, Model.isFinite (project (.finite q)) = true)
    (eterm : ∀ q ∈ values,
      MixedError (Model.toReal (project (.finite q))) (q : ℝ) (rel q) (err q))
    (hout : Model.isFinite
      (Extended.round output ((binary fmt project).run (values.map .finite))) = true) :
    MixedError
      (Model.toReal (Extended.round output ((binary fmt project).run (values.map .finite))))
      (values.map fun q : Rat => (q : ℝ)).sum (Model.unitRoundoffAt output)
      ((1 + Model.unitRoundoffAt output) * binaryErrorBound fmt values rel err +
        Model.underflowErrorAt output) := by
  let state := values.foldl (fun sum q => Model.add sum (project (.finite q)))
    (Model.zero fmt false)
  have hstate : (binary fmt project).fold (values.map .finite) = state := by
    simp [fold, binary, List.foldl_map, state]
  have hs : Model.isFinite state = true :=
    hfinite _ (List.mem_of_getLast? List.getLast?_scanl)
  have hrun : (binary fmt project).run (values.map .finite) =
      .finite (finiteValue (Codec.decodeModel state)) := by
    dsimp only [run]
    rw [hstate]
    exact Codec.map_decodeModel_of_isFinite state hs
  have hround := Extended.toReal_round_finite output houtput
    (finiteValue (Codec.decodeModel state)) (by simpa [hrun] using hout)
  rw [Codec.cast_finiteValue_decodeModel] at hround
  have he := mixedError_fold_binary fmt hfmt project values rel err hfinite hterm eterm
  rw [hstate] at he
  simpa [hrun] using (Model.mixedError_toReal_of_eq_roundAt hround).trans he

/--
The reference product projection has the accumulator's usual nearest-even
mixed error whenever its output is finite.
-/
theorem mixedError_round_finite (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (value : Rat) (hfinite : Model.isFinite (Extended.round fmt (.finite value)) = true) :
    MixedError (Model.toReal (Extended.round fmt (.finite value))) (value : ℝ)
      (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt) :=
  Model.mixedError_toReal_of_eq_roundAt (Extended.toReal_round_finite fmt hfmt value hfinite)

end Reduction

end FloatLib.Floats.Formats.Block
