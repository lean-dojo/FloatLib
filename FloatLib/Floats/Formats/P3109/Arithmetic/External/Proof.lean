/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Bounds
public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Rounding
public import FloatLib.Floats.Formats.P3109.Arithmetic.Mixed.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Exact encoding of external P3109 results

Report precision rounding and saturation produce representable dyadics. The binary encoder
therefore preserves every finite projected value, including a significand carry. The executable
result decodes to that exact rational, with no second rounding. Exceptional results use the
specified signed infinity or canonical quiet NaN; zero is encoded with positive sign.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic.External

open BinaryInterchange

/-- A grid value in the external finite range is encoded exactly, including a binade carry. -/
theorem encode_finite (format : FloatFormat) (hformat : format.isIEEE = true)
    (value : Numerics.Dyadic) (hgrid : FitsGrid format value)
    (hbound : |value.toReal| ≤ Model.toReal (Model.posMaxFinite format)) :
    Model.isFinite (encode format (.finite value)) = true ∧
      Model.toReal (encode format (.finite value)) = value.toReal := by
  simp only [encode]
  split
  next hzero =>
    have hsig : value.significand = 0 := by simpa using hzero
    refine ⟨Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero format false), ?_⟩
    simp [Model.toReal_zero, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hsig]
  next hnonzero =>
    by_cases hcarry : value.significand = 2 ^ (format.fracWidth + 1)
    · apply Model.roundDyadic_of_representable format hformat value
        (2 ^ format.fracWidth) 1
      · simpa [pow_succ] using hcarry
      · have hpos := Nat.two_pow_pos format.fracWidth
        rw [pow_succ]
        omega
      · exact hgrid.2
      · exact hbound
    · exact Model.roundDyadic_of_representable format hformat value value.significand 0
        (by simp) (lt_of_le_of_ne hgrid.1 hcarry) hgrid.2 hbound

/-- Every finite projected result is encoded with its exact real value. -/
theorem project_finite (format : FloatFormat) (hformat : format.isIEEE = true)
    (policy : ProjectionPolicy) (input : NumericalValue Rat) (result : Numerics.Dyadic)
    (hresult : projectValue format policy input = .finite result) :
    Model.isFinite (project format hformat policy input) = true ∧
      Model.toReal (project format hformat policy input) = result.toReal := by
  have hgrid : ∀ value, roundValue format policy.rounding input = .finite value →
      FitsGrid format value := by
    cases input with
    | finite exact =>
        intro value hvalue
        cases hvalue
        exact roundFinite_fitsGrid format policy.rounding exact
    | infinity negative => intro value hvalue; cases hvalue
    | exceptional value => intro value hvalue; cases hvalue
  obtain ⟨hprecision, hbound⟩ :=
    saturate_finite format hformat policy _ hgrid result hresult
  simpa only [project, hresult] using encode_finite format hformat result hprecision hbound

/-- The exact external decoder agrees with the real interpretation on every finite word. -/
theorem decode_eq_finite_of_isFinite (format : FloatFormat) (word : Model format)
    (value : Numerics.Dyadic) (hfinite : Model.isFinite word = true)
    (hreal : Model.toReal word = value.toReal) :
    decode word = .finite value.toRat := by
  obtain ⟨decoded, hdecode⟩ := Model.exists_toDyadic?_of_isFinite hfinite
  have hdyadic : decoded.toReal = value.toReal := by
    simpa only [Model.toReal_eq, hdecode] using hreal
  have hrat : decoded.toRat = value.toRat := by
    apply Rat.cast_injective (α := Real)
    simpa only [Numerics.Dyadic.cast_toRat] using hdyadic
  simp [decode, Model.exactNumericalSystem, hdecode, Arithmetic.toRat, hrat]

/-- Finite external results refine the exact report projection through the executable decoder. -/
theorem decode_project_finite (format : FloatFormat) (hformat : format.isIEEE = true)
    (policy : ProjectionPolicy) (input : NumericalValue Rat) (result : Numerics.Dyadic)
    (hresult : projectValue format policy input = .finite result) :
    decode (project format hformat policy input) = .finite result.toRat := by
  obtain ⟨hfinite, hreal⟩ := project_finite format hformat policy input result hresult
  exact decode_eq_finite_of_isFinite format _ result hfinite hreal

/-- A projected infinity retains its sign in the external encoding. -/
theorem project_infinity (format : FloatFormat) (hformat : format.isIEEE = true)
    (policy : ProjectionPolicy) (input : NumericalValue Rat) (negative : Bool)
    (hresult : projectValue format policy input = .infinity negative) :
    project format hformat policy input =
      if negative then Model.negInf format else Model.posInf format := by
  simp [project, hresult, encode]

/-- A projected NaN becomes the canonical quiet external NaN. -/
theorem project_nan (format : FloatFormat) (hformat : format.isIEEE = true)
    (policy : ProjectionPolicy) (input : NumericalValue Rat) (exception : ExceptionalValue)
    (hresult : projectValue format policy input = .exceptional exception) :
    project format hformat policy input = Model.canonicalNaN format := by
  simp [project, hresult, encode]

/-- Every projected zero uses the external positive-zero encoding. -/
theorem project_zero (format : FloatFormat) (hformat : format.isIEEE = true)
    (policy : ProjectionPolicy) (input : NumericalValue Rat) (result : Numerics.Dyadic)
    (hresult : projectValue format policy input = .finite result)
    (hzero : result.significand = 0) :
    project format hformat policy input = Model.zero format false := by
  simp [project, hresult, encode, hzero]

/-- Exact finite decoding, with the report's prescribed external exceptional encodings. -/
def Encodes {format : FloatFormat} (word : Model format) :
    NumericalValue Numerics.Dyadic → Prop
  | .finite value => decode word = .finite value.toRat
  | .infinity negative => word = if negative then Model.negInf format else Model.posInf format
  | .exceptional _ => word = Model.canonicalNaN format

/-- External projection refines its rounded and saturated datum on every input class. -/
theorem project_refines (format : FloatFormat) (hformat : format.isIEEE = true)
    (policy : ProjectionPolicy) (input : NumericalValue Rat) :
    Encodes (project format hformat policy input) (projectValue format policy input) := by
  cases hresult : projectValue format policy input with
  | finite value => exact decode_project_finite format hformat policy input value hresult
  | infinity negative => exact project_infinity format hformat policy input negative hresult
  | exceptional exception => exact project_nan format hformat policy input exception hresult

/-- A configured carrier preserves every bit of the external report projection. -/
theorem configuredDestination_toModel (format : FloatFormat)
    (plan : Configured.StoragePlan format) (code : Type)
    [ExecFloat.ModelCodec plan (Model format) code]
    (hformat : format.isIEEE = true) (policy : ProjectionPolicy) (input : NumericalValue Rat) :
    ExecFloat.Binary.toModel
      ((configuredDestination format plan code hformat).project policy input) =
        project format hformat policy input := by
  simp [configuredDestination, ExecFloat.Binary.toModel_ofModel]

/-- External mixed binary arithmetic has the same total refinement as direct projection. -/
theorem mixed_binary_refines
    {Left LeftExact Right RightExact : Type}
    [ExecFloat.ExactDecoder Left LeftExact] [ExecFloat.ExactMap LeftExact Rat]
    [ExecFloat.ExactDecoder Right RightExact] [ExecFloat.ExactMap RightExact Rat]
    (format : FloatFormat) (hformat : format.isIEEE = true) (policy : ProjectionPolicy)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat)
    (left : Left) (right : Right) :
    Encodes (Mixed.binary (destination format hformat) policy operation left right)
      (projectValue format policy (operation (Mixed.decode left) (Mixed.decode right))) :=
  project_refines format hformat policy _

/-- External fused arithmetic preserves the complete ternary expression through encoding. -/
theorem mixed_ternary_refines
    {Left LeftExact Right RightExact Third ThirdExact : Type}
    [ExecFloat.ExactDecoder Left LeftExact] [ExecFloat.ExactMap LeftExact Rat]
    [ExecFloat.ExactDecoder Right RightExact] [ExecFloat.ExactMap RightExact Rat]
    [ExecFloat.ExactDecoder Third ThirdExact] [ExecFloat.ExactMap ThirdExact Rat]
    (format : FloatFormat) (hformat : format.isIEEE = true) (policy : ProjectionPolicy)
    (operation : NumericalValue Rat → NumericalValue Rat → NumericalValue Rat →
      NumericalValue Rat) (left : Left) (right : Right) (third : Third) :
    Encodes (Mixed.ternary (destination format hformat) policy operation left right third)
      (projectValue format policy
        (operation (Mixed.decode left) (Mixed.decode right) (Mixed.decode third))) :=
  project_refines format hformat policy _

end FloatLib.Floats.Formats.P3109.Arithmetic.External
