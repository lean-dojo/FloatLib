/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib

/-!
# Packed rows of format values and bounds from them

`packed_values` decodes values of any format with an exact rational meaning into one row at a
common denominator, and the kernel checks the link once. `interval` reads such values itself.

## Main statements

* Small rows in five representations: binary32 `[1.5, -0.25, 3]` is `[6, -1, 12]` over `4`, a
  16-bit posit row, decimal fixed point with two digits over `100`, rationals over `6`, and two
  shared-scale blocks of three lanes, flattened to six lanes over `8`.
* A cosine polynomial with 24 binary64 coefficients `aₖ`, drawn by Python's `random` with seed
  `20261107` (Gaussian, decaying like `1.3 ^ (-k)`, `a₀ = 0.75`). A sum-of-squares certificate
  from `scripts/coeff_cert.py` proves `∑ aₖ cos (k u) ≥ -0.43828138` for every `u`, where the
  minimum is `-0.43828114`.
* A cosine polynomial with 40 binary32 coefficients (Gaussian, decaying like `1.15 ^ (-k)`,
  `a₀ = 1.25`), whose maximum `3.06698857` is certified up to `3.0669892`, while the `l1` norm is
  `6.16`.
* The bound from the coefficients alone on a sine polynomial with OCP E4M3 coefficients.
* Negative controls: the kernel refuses the link with a wrong denominator, with an infinity and
  with an extra lane, a bound above the minimum is refused, and `packed_values` rejects an
  infinity and a lane that is too narrow.

## Implementation notes

The certificates were made with
`python3 -I scripts/coeff_cert.py coeffs.txt --ieee 64 --lower -0.43828138 -o PackedValuesLower.txt`
and `--ieee 32 --upper auto --slack 1e-7 -o PackedValuesUpper.txt`, from files of the bit patterns
below.

Every check runs under `set_option maxHeartbeats`, or `interval (maxHeartbeats := B)` for the
kernel check of `interval`, at about three times the heartbeats it uses, so the build fails if its
kernel cost grows.

## References

* *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
* *OCP 8-bit Floating Point Specification (OFP8)*, Revision 1.0 (2023), for E4M3,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Formats.PackedValues

open FloatLib.Numerics FloatLib.Floats FloatLib.Floats.ExecFloat FloatLib.Floats.ExecFloat.Packed
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics.Packed FloatLib.Numerics.Coeff Finset

/-! ## Five representations -/

/-- `1.5`, `-0.25` and `3` in binary32. -/
def single : List Binary32 := [.ofNatBits 0x3FC00000, .ofNatBits 0xBE800000, .ofNatBits 0x40400000]

set_option maxHeartbeats 1000 in
packed_values singleRow (width := 8) := single

set_option maxHeartbeats 400 in
/-- The row is `[6, -1, 12]`, over the denominator `4` of the link `singleRow.link`. -/
theorem single_row : entries 8 3 singleRow = [6, -1, 12] := by
  decide +kernel

/-- `1`, `1/4`, `-1` and `8` as 16-bit posits. -/
def posits : List (ExecFloat.Posit (bits := 16)) :=
  [.ofNatBits 0x4000, .ofNatBits 0x3000, .ofNatBits 0xC000, .ofNatBits 0x5800]

set_option maxHeartbeats 8000 in
packed_values positRow (width := 8) := posits

/-- `1.25`, `-0.03` and `0.40` on the decimal grid with two digits. -/
def cents : List (ExecFloat.FixedPoint decimalRadix 2) :=
  [.ofCoefficient 125, .ofCoefficient (-3), .ofCoefficient 40]

set_option maxHeartbeats 1000 in
packed_values centRow (width := 16) := cents

/-- `1/3`, `-1/6` and `5`. -/
def fractions : List ℚ := [1 / 3, -1 / 6, 5]

set_option maxHeartbeats 400 in
packed_values fractionRow (width := 16) := fractions

/-- Two blocks of three lanes, `2 ^ (-3) * [1, -2, 5]` and `2 * [7, 0, -1]`. -/
def blocks : List (ExecFloat.SharedScale 3) :=
  [.ofCode ⟨-3, #v[1, -2, 5]⟩, .ofCode ⟨1, #v[7, 0, -1]⟩]

set_option maxHeartbeats 1000 in
packed_values blockRow (width := 16) := blocks

set_option maxHeartbeats 2000 in
/-- The rows of the other four representations, over the denominators `4`, `100`, `6` and `8`. -/
theorem other_rows :
    entries 8 4 positRow = [4, 1, -4, 32] ∧ entries 16 3 centRow = [125, -3, 40] ∧
      entries 16 3 fractionRow = [2, -1, 30] ∧ entries 16 6 blockRow = [1, -2, 5, 112, 0, -16] ∧
      link 16 100 (values cents) centRow = true := by
  decide +kernel

set_option maxHeartbeats 1000 in
/-- What a link says, lane by lane: the decoded value of `-0.25` is entry `1` over `4`. -/
theorem single_value : (values single)[1]'(by decide) = some (-1 / 4) := by
  rw [(link_sound singleRow.link).2 1 (by decide)]
  decide +kernel

/-! ## Bounds from binary64, binary32 and E4M3 coefficients -/

/-- The 24 binary64 coefficients. -/
def coefficients : List (Model FloatFormat.binary64) := [
    0x3FE8000000000000, 0xBFE61FC918F653B5, 0xBFCD41D06F8606F0, 0x3FB79023BB653FED,
    0xBFC7E0CC9506A76A, 0xBFC4101E7E55101E, 0xBFB8E5298AFE6150, 0x3F896E2E5AE4F589,
    0x3FA7A705463D2866, 0xBFA086113F618017, 0xBF83152B7113F09C, 0x3F74AD93516A0594,
    0x3F90E56CB23883C5, 0x3F95A92DBB13AB9D, 0xBF5846909591AD80, 0x3F7D1E5DC54DCE46,
    0x3F839A434A38A9F4, 0xBF73BCA300B9C246, 0x3F8EE18E94F891FC, 0xBF81A5F5C983B6D9,
    0x3F6B2EDB237564BD, 0x3F7CC845D3955DB9, 0xBF5D0888ED259E80, 0x3F1BE5C5C6873D2B].map
  Model.ofNatBits

/-- The exact values of the binary64 coefficients. -/
def doubleValues : List ℚ := (values coefficients).map (·.getD 0)

/-- The lower bound for every `u`, from the binary64 values and one certificate. -/
theorem lower_bound : ∀ u : ℝ,
    -0.43828138 ≤ ∑ k ∈ range 24, (doubleValues.getD k 0 : ℝ) * Real.cos (k * u) := by
  interval (lower := "PackedValuesLower.txt") (maxHeartbeats := 400)

/-- The 40 binary32 coefficients. -/
def singles : List Binary32 := [
    .ofNatBits 0x3FA00000, .ofNatBits 0xBF7DFE41, .ofNatBits 0xB974A783, .ofNatBits 0x3F1C84DA,
    .ofNatBits 0x3E172049, .ofNatBits 0xBEF0BD42, .ofNatBits 0x3EBD359E, .ofNatBits 0x3DA7CFA8,
    .ofNatBits 0x3EDE09F1, .ofNatBits 0x3E8798F8, .ofNatBits 0x3DFB2F8D, .ofNatBits 0x3E5E739B,
    .ofNatBits 0x3E602C21, .ofNatBits 0x3E89E11E, .ofNatBits 0x3DC61BE6, .ofNatBits 0x3E1EABC2,
    .ofNatBits 0x3D6CB98D, .ofNatBits 0xBD9FC4CC, .ofNatBits 0x3D3D1FD6, .ofNatBits 0x3B754DF3,
    .ofNatBits 0x3D16C8F3, .ofNatBits 0xBBFB33E8, .ofNatBits 0x3C6725D1, .ofNatBits 0xBB1E728A,
    .ofNatBits 0x3D0A07CE, .ofNatBits 0x3C903E83, .ofNatBits 0x3C09DCF8, .ofNatBits 0x3CA66A81,
    .ofNatBits 0xBC064F5A, .ofNatBits 0xBCEA3C5B, .ofNatBits 0x3C620DF2, .ofNatBits 0xBCA5EE68,
    .ofNatBits 0x3BC17109, .ofNatBits 0x3C189417, .ofNatBits 0xBB7B5227, .ofNatBits 0xBC8044C5,
    .ofNatBits 0x3C5EF314, .ofNatBits 0xBB8C250A, .ofNatBits 0x3B8019EB, .ofNatBits 0x3B8A56A5]

/-- The exact values of the binary32 coefficients. -/
def singleValues : List ℚ := (values singles).map (·.getD 0)

/-- The upper bound for every `u`, about half the `l1` norm, from the binary32 values. -/
theorem upper_bound : ∀ u : ℝ,
    ∑ k ∈ range 40, (singleValues.getD k 0 : ℝ) * Real.cos (k * u) ≤ 3.0669892 := by
  interval (upper := "PackedValuesUpper.txt") (maxHeartbeats := 400)

/-- Four E4M3 values, `0.5`, `-1.5`, `0.25` and `2`. -/
def eights : List (Model FloatFormat.e4m3fn) := [0x30, 0xBC, 0x28, 0x40].map Model.ofNatBits

/-- The exact values of the E4M3 coefficients. -/
def smallValues : List ℚ := (values eights).map (·.getD 0)

/-- The bound from the coefficients alone on the sine polynomial of the E4M3 values. -/
theorem sine_bound : ∀ u : ℝ,
    |∑ k ∈ range 4, (smallValues.getD k 0 : ℝ) * Real.sin (k * u)| ≤ 4.25 := by
  interval (maxHeartbeats := 100)

/-! ## Negative controls -/

/-- `1.5` and the binary32 infinity. -/
def withInfinity : List Binary32 := [.ofNatBits 0x3FC00000, .ofNatBits 0x7F800000]

set_option maxHeartbeats 1000 in
/-- The link refuses twice the true denominator, a lane with no finite value, and a row with a
lane beyond the values. -/
theorem wrong_denominator :
    link 8 8 (values single) singleRow = false ∧
      link 8 4 (values withInfinity) (pack 8 [6, 0]) = false ∧
      link 8 4 (values single) (singleRow + 2 ^ 24) = false := by
  decide +kernel

/--
error: interval: the certificate fails: the centre entry
-60253050786109418452860783230262457198 of the defect is below the sum
83884840310941099892290087183524007022 of the absolute values of the others
-/
#guard_msgs (error, whitespace := lax) in
example : ∀ u : ℝ,
    -0.4382811 ≤ ∑ k ∈ range 24, (doubleValues.getD k 0 : ℝ) * Real.cos (k * u) := by
  interval (lower := "PackedValuesLower.txt")

/-- error: value 1 has no finite exact value -/
#guard_msgs (error) in
packed_values infiniteRow (width := 8) := withInfinity

/-- error: entry 2 is 12, which does not fit a signed lane of width 4 -/
#guard_msgs (error) in
packed_values narrowRow (width := 4) := single

end FloatLibTests.Conformance.Formats.PackedValues
