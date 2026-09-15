/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Range
public import FloatLib.Floats.Formats.P3109.Projection.Encoding

/-!
# Correctness of P3109 projection

P3109 projection rounds first, saturates second, and encodes last. This module proves that the
executable code decodes to the same datum as that exact round-then-saturate specification for
every valid descriptor and every supported policy.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109
namespace Format

private theorem sameDatum_decode_encodeMaxFinite (format : Format) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format
            (.finite format.maxFinite))))
      (.finite format.maxFinite) :=
  format.sameDatum_decode_encodeFinite format.maxFinite
    format.maxFinite_fitsPrecisionGrid
    format.minFinite_toRat_le_maxFinite le_rfl

private theorem sameDatum_decode_encodeMinFinite (format : Format) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format
            (.finite format.minFinite))))
      (.finite format.minFinite) :=
  format.sameDatum_decode_encodeFinite format.minFinite
    format.minFinite_fitsPrecisionGrid le_rfl
    format.minFinite_toRat_le_maxFinite

private theorem sameDatum_decode_encodeNan (format : Format) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format
            (.exceptional (.nan)))))
      (.exceptional (.nan)) := by
  rw [show
    Internal.encodeDatumNat format (.exceptional (.nan)) =
      format.nanBits by rfl]
  rw [format.decode_nanBits]
  trivial

private theorem sameDatum_decode_encodePositiveInfinity
    (format : Format) (extended : format.domain = .extended) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format
            (.infinity false))))
      (.infinity false) := by
  rw [show
    Internal.encodeDatumNat format (.infinity false) =
      format.positiveInfinityBits by rfl]
  rw [format.decode_positiveInfinityBits extended]
  rfl

private theorem sameDatum_decode_encodeNegativeInfinity
    (format : Format)
    (signed : format.signedness = .signed)
    (extended : format.domain = .extended) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format
            (.infinity true))))
      (.infinity true) := by
  rw [show
    Internal.encodeDatumNat format (.infinity true) =
      format.negativeInfinityBits by rfl]
  rw [format.decode_negativeInfinityBits signed extended]
  rfl

private theorem sameDatum_decode_encodeSaturateBelow
    (format : Format) (mode : SaturationMode)
    (rounding : RoundingMode) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format
            (Internal.saturateBelow format mode rounding))))
      (Internal.saturateBelow format mode rounding) := by
  cases mode <;> cases rounding <;>
    cases signed : format.signedness <;>
    cases extended : format.domain <;>
    simp [Internal.saturateBelow, signed, extended,
      format.sameDatum_decode_encodeMinFinite,
      format.sameDatum_decode_encodeNan,
      format.sameDatum_decode_encodeNegativeInfinity]

private theorem sameDatum_decode_encodeSaturateAbove
    (format : Format) (mode : SaturationMode)
    (rounding : RoundingMode) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format
            (Internal.saturateAbove format mode rounding))))
      (Internal.saturateAbove format mode rounding) := by
  cases mode <;> cases rounding <;>
    cases extended : format.domain <;>
    simp [Internal.saturateAbove, extended,
      format.sameDatum_decode_encodeMaxFinite,
      format.sameDatum_decode_encodeNan,
      format.sameDatum_decode_encodePositiveInfinity]

/--
Direct encoding and decoding preserve any saturated datum whose finite branch lies on the
descriptor precision grid.

This theorem is the shared representation boundary for dyadic and exact-rational projection.
-/
theorem sameDatum_decode_encodeSaturate
    (format : Format) (mode : SaturationMode)
    (rounding : RoundingMode)
    (value : NumericalValue Numerics.Dyadic)
    (hgrid :
      match value with
      | .finite finite => format.FitsPrecisionGrid finite
      | _ => True) :
    SameDatum
      (format.decode
        (BitVec.ofNat format.bitWidth
          (Internal.encodeDatumNat format
            (format.saturate mode rounding value))))
      (format.saturate mode rounding value) := by
  cases value with
  | exceptional category =>
      simpa [saturate] using format.sameDatum_decode_encodeNan
  | infinity negative =>
      cases negative <;> cases mode <;>
        cases signed : format.signedness <;>
        cases extended : format.domain <;>
        simp [saturate, signed, extended,
          format.sameDatum_decode_encodeMaxFinite,
          format.sameDatum_decode_encodeMinFinite,
          format.sameDatum_decode_encodeNan,
          format.sameDatum_decode_encodePositiveInfinity,
          format.sameDatum_decode_encodeNegativeInfinity]
  | finite finite =>
      simp only at hgrid
      unfold saturate
      simp only [beq_iff_eq]
      split
      next _ =>
        exact format.sameDatum_decode_encodeSaturateBelow mode rounding
      next hnotBelow =>
        split
        next _ =>
          exact format.sameDatum_decode_encodeSaturateAbove mode rounding
        next hnotAbove =>
          apply format.sameDatum_decode_encodeFinite finite hgrid
          · apply not_lt.mp
            intro hlt
            apply hnotBelow
            rw [Numerics.Dyadic.Internal.compareScalable_eq_compare]
            exact (Numerics.Dyadic.compare_eq_lt_iff _ _).2 hlt
          · apply not_lt.mp
            intro hlt
            apply hnotAbove
            rw [Numerics.Dyadic.Internal.compareScalable_eq_compare]
            exact (Numerics.Dyadic.compare_eq_lt_iff _ _).2 hlt

/--
Decoding an executable projection returns its exact round-then-saturate datum.

The theorem is uniform over every valid P3109 descriptor and every rounding and saturation
policy. No descriptor width or named low-precision format is treated as a special proof case.
-/
theorem sameDatum_decode_projectCode
    (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Numerics.Dyadic) :
    SameDatum
      (format.decode (format.projectCode policy value))
      (format.projectValue policy value) := by
  unfold projectCode projectValue
  apply format.sameDatum_decode_encodeSaturate
  cases value with
  | finite finite =>
      exact format.roundFiniteToPrecision_fitsPrecisionGrid
        policy.rounding finite
  | infinity _ =>
      trivial
  | exceptional _ =>
      trivial

/-- Checked encoding accepts the exact datum produced by projection. -/
@[simp] theorem encode?_projectValue
    (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Numerics.Dyadic) :
    format.encode? (format.projectValue policy value) =
      some (format.projectCode policy value) := by
  unfold encode? projectCode
  dsimp only
  have hsame := format.sameDatum_decode_projectCode policy value
  have hequal :
      datumEqual
          (format.decode
            (BitVec.ofNat format.bitWidth
              (Internal.encodeDatumNat format
                (format.projectValue policy value))))
          (format.projectValue policy value) =
        true :=
    (datumEqual_eq_true_iff _ _).2 hsame
  simp [hequal]

end Format
end FloatLib.Floats.Formats.P3109

namespace FloatLib.Floats.ExecFloat.P3109

variable {format : Formats.P3109.Format}

/-- Decoding `project` exposes the exact P3109 round-then-saturate specification. -/
theorem decode_project
    (policy : Formats.P3109.ProjectionPolicy)
    (value : NumericalValue Numerics.Dyadic) :
    Formats.P3109.Format.SameDatum
      (decode (project (format := format) policy value))
      (format.projectValue policy value) := by
  exact
    Formats.P3109.Format.sameDatum_decode_projectCode
      format policy value

end FloatLib.Floats.ExecFloat.P3109
