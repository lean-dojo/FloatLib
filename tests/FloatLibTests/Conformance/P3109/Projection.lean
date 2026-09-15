/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Conversion.Proof
public meta import FloatLib.Floats.ExecFloat.Conversion.Core
public meta import FloatLib.Floats.Formats.P3109.Conversion.Instances
public meta import FloatLib.Floats.Formats.P3109.Conversion.Runtime
public meta import FloatLib.Floats.Formats.P3109.Projection.Runtime
public meta import Mathlib.Algebra.GroupWithZero.Nat

/-!
# P3109 projection regression matrix

These compiled checks exercise the parameterized projection kernel independently of its proof
layer. The small matrix covers every valid signedness, domain, bit width, precision, and code point
for `K = 3...10`. Larger descriptors use boundary samples so validation remains quick while still
exercising arbitrary-width natural-number storage.

The mode checks include P3109's special `P = 1` nearest-even parity rule, to-odd rounding,
stochastic A/B/C, directed overflow, finite saturation, infinity propagation, and unsigned
negative inputs. Configured conversion checks exercise exact, inexact, overflow, underflow,
saturation, and special-value status through the ordinary shared API.
-/

@[expose] public section

open FloatLib.Numerics
open FloatLib.Floats

namespace FloatLibTests.Conformance.P3109.Projection

open FloatLib

open FloatLib.Floats.Formats

/-!
The fixed rows below provide an independent anchor for the generated round-trip matrix. They
come from the working group's hexadecimal value tables for Binary6p1sf, Binary6p1uf, and
Binary6p5se at commit `aa9d236d7a31b38fbe43b703a0bfdfc3d8be5d45`:
<https://github.com/P3109/Public/tree/aa9d236d7a31b38fbe43b703a0bfdfc3d8be5d45/Value%20Tables/Hexadecimal/K6>.
These checks follow the cited P3109 working-group tables.
-/

example :
    let format := P3109.Format.signed 6 1 .finite
    ([0x01, 0x1f, 0x21, 0x20].map fun bits =>
      format.decode (BitVec.ofNat 6 bits)) =
        [ .finite { negative := false, significand := 1, exponent := -15 }
        , .finite { negative := false, significand := 1, exponent := 15 }
        , .finite { negative := true, significand := 1, exponent := -15 }
        , .exceptional .nan ] := by
  decide +kernel

example :
    let format := P3109.Format.unsigned 6 1 .finite
    ([0x01, 0x20, 0x3e, 0x3f].map fun bits =>
      format.decode (BitVec.ofNat 6 bits)) =
        [ .finite { negative := false, significand := 1, exponent := -31 }
        , .finite { negative := false, significand := 1, exponent := 0 }
        , .finite { negative := false, significand := 1, exponent := 30 }
        , .exceptional .nan ] := by
  decide +kernel

example :
    let format := P3109.Format.signed 6 5 .extended
    ([0x01, 0x10, 0x1e, 0x1f, 0x20, 0x21, 0x3f].map fun bits =>
      format.decode (BitVec.ofNat 6 bits)) =
        [ .finite { negative := false, significand := 1, exponent := -4 }
        , .finite { negative := false, significand := 16, exponent := -4 }
        , .finite { negative := false, significand := 30, exponent := -4 }
        , .infinity false
        , .exceptional .nan
        , .finite { negative := true, significand := 1, exponent := -4 }
        , .infinity true ] := by
  decide +kernel

/-- Every valid descriptor with `3 ≤ K ≤ 10`, generated from the four defining parameters. -/
def smallFormats : List P3109.Format :=
  (List.range 8).flatMap fun widthOffset =>
    let bitWidth := widthOffset + 3
    (List.range bitWidth).flatMap fun precisionOffset =>
      let precision := precisionOffset + 1
      [.signed, .unsigned].flatMap fun signedness =>
        [.finite, .extended].filterMap fun domain =>
          P3109.Format.ofParameters? bitWidth precision signedness domain

/-- Number of stored words that change after exact decode and nearest-even projection. -/
def roundTripFailures (format : P3109.Format) : Nat :=
  (List.range format.modulus).countP fun bits =>
    let code := BitVec.ofNat format.bitWidth bits
    (format.projectCode {} (format.decode code)).toNat != bits

/-- The exhaustive small matrix contains 192 distinct valid descriptors. -/
example : smallFormats.length = 192 := by
  native_decide

/-- Every code point in every generated small descriptor round-trips exactly. -/
example : (smallFormats.map roundTripFailures).sum = 0 := by
  native_decide

/-- Representative arbitrary-width descriptors used by the sampled boundary sweep. -/
def wideFormats : List P3109.Format :=
  [ .signed 16 1 .finite,
    .unsigned 16 16 .extended,
    .signed 64 53 .extended,
    .unsigned 64 64 .finite,
    .signed 256 113 .extended,
    .unsigned 256 256 .extended,
    .signed 4096 113 .extended,
    .unsigned 4096 4096 .extended ]

/-- Semantically important code points without enumerating an arbitrary-width code space. -/
def boundaryCodes (format : P3109.Format) : List Nat :=
  [ 0,
    1,
    format.maxFiniteBits,
    format.positiveInfinityBits,
    format.nanBits,
    format.signBoundary,
    format.signBoundary + 1,
    format.modulus - 1 ]

/-- Number of sampled arbitrary-width code points that fail exact round-trip projection. -/
def boundaryRoundTripFailures (format : P3109.Format) : Nat :=
  (boundaryCodes format).countP fun bits =>
    let bounded := bits % format.modulus
    let code := BitVec.ofNat format.bitWidth bounded
    (format.projectCode {} (format.decode code)).toNat != bounded

/-- Boundary samples pass through descriptors as wide as 4096 bits. -/
example : (wideFormats.map boundaryRoundTripFailures).sum = 0 := by
  native_decide

/-- Six-bit, one-bit-precision signed finite profile used for tie-rule checks. -/
def binary6p1sf : P3109.Format :=
  .signed 6 1 .finite

/-- Six-bit, five-bit-precision signed extended profile used for overflow checks. -/
def binary6p5se : P3109.Format :=
  .signed 6 5 .extended

/-- Six-bit, five-bit-precision unsigned extended profile used for negative-input checks. -/
def binary6p5ue : P3109.Format :=
  .unsigned 6 5 .extended

/-- Project a finite dyadic and expose the resulting code for concise mode checks. -/
def projectFiniteBits
    (format : P3109.Format)
    (policy : P3109.ProjectionPolicy)
    (value : Numerics.Dyadic) : Nat :=
  (format.projectCode policy (.finite value)).toNat

/-- At `P = 1`, nearest-even uses code parity rather than significand parity. -/
example :
    projectFiniteBits binary6p1sf {}
      { negative := false, significand := 3, exponent := -16 } = 2 := by
  native_decide

/-- To-odd keeps the odd lower code at the same `P = 1` tie. -/
example :
    projectFiniteBits binary6p1sf { rounding := .toOdd }
      { negative := false, significand := 3, exponent := -16 } = 1 := by
  native_decide

/-- To-odd moves upward when the lower `P = 1` code is even. -/
example :
    projectFiniteBits binary6p1sf { rounding := .toOdd }
      { negative := false, significand := 3, exponent := -15 } = 3 := by
  native_decide

/-- Each stochastic variant can select the lower endpoint with the supplied random bits. -/
example :
    [ P3109.RoundingMode.stochasticA (.ofNat 2 0),
      .stochasticB (.ofNat 2 0),
      .stochasticC (.ofNat 2 0) ].map
        (fun rounding =>
          projectFiniteBits binary6p1sf { rounding }
            { negative := false, significand := 3, exponent := -16 }) =
      [1, 1, 1] := by
  native_decide

/-- Each stochastic variant can select the upper endpoint with the supplied random bits. -/
example :
    [ P3109.RoundingMode.stochasticA (.ofNat 2 3),
      .stochasticB (.ofNat 2 3),
      .stochasticC (.ofNat 2 3) ].map
        (fun rounding =>
          projectFiniteBits binary6p1sf { rounding }
            { negative := false, significand := 3, exponent := -16 }) =
      [2, 2, 2] := by
  native_decide

/-- No-saturation nearest rounding maps positive overflow to infinity in an extended profile. -/
example :
    projectFiniteBits binary6p5se {}
      { negative := false, significand := 1, exponent := 1 } =
      binary6p5se.positiveInfinityBits := by
  native_decide

/-- Finite saturation clamps the same overflow to the largest finite datum. -/
example :
    projectFiniteBits binary6p5se { saturation := .finite }
      { negative := false, significand := 1, exponent := 1 } =
      binary6p5se.maxFiniteBits := by
  native_decide

/-- Directed no-saturation overflow keeps a finite endpoint when the P3109 report requires it. -/
example :
    projectFiniteBits binary6p5se { rounding := .towardZero }
      { negative := false, significand := 1, exponent := 1 } =
      binary6p5se.maxFiniteBits := by
  native_decide

/-- Unsigned no-saturation projection maps a negative finite result to NaN. -/
example :
    projectFiniteBits binary6p5ue {}
      { negative := true, significand := 1, exponent := 0 } =
      binary6p5ue.nanBits := by
  native_decide

/-- Directed projection toward zero clamps a negative unsigned input to zero. -/
example :
    projectFiniteBits binary6p5ue { rounding := .towardZero }
      { negative := true, significand := 1, exponent := 0 } = 0 := by
  native_decide

/-! ## Configured conversion and truthful status -/

/-- Configured carrier used to exercise the shared scalar conversion interface. -/
abbrev Binary6p5seValue :=
  ExecFloat.P3109 binary6p5se

/-- Exact rational conversion preserves both the value and an all-clear status. -/
example :
    let outcome :=
      ExecFloat.convert (target := Binary6p5seValue) (3 / 16 : Rat)
    outcome.value?.map ExecFloat.P3109.Conversion.decodeRat =
        some (.finite (3 / 16)) ∧
      outcome.status? = some {} := by
  native_decide

/-- A non-grid rational reports inexact without reporting overflow or underflow. -/
example :
    let outcome :=
      ExecFloat.convert (target := Binary6p5seValue) (1 / 3 : Rat)
    outcome.status?.map (fun status =>
        (status.inexact, status.overflow, status.underflow)) =
      some (true, false, false) := by
  native_decide

/-- A nonzero value below the least positive datum reports underflow and inexact. -/
example :
    let outcome :=
      ExecFloat.convert (target := Binary6p5seValue) (1 / 100 : Rat)
    outcome.status?.map (fun status =>
        (status.inexact, status.underflow)) =
      some (true, true) := by
  native_decide

/-- Finite saturation reports the exact overflow and the endpoint clamp separately. -/
example :
    let outcome :=
      ExecFloat.convertWith (target := Binary6p5seValue) (2 : Rat)
        Formats.P3109.ProjectionPolicy.finite
    outcome.value?.map ExecFloat.P3109.toNatBits =
        some binary6p5se.maxFiniteBits ∧
      outcome.status?.map (fun status =>
        (status.inexact, status.overflow, status.saturated)) =
      some (true, true, true) := by
  native_decide

/-- Preserved infinity is successful and does not claim a special-value mapping. -/
example :
    let outcome :=
      ExecFloat.P3109.Conversion.run
        (format := binary6p5se)
        .nearestEven
        (.infinity false)
    outcome.value?.map ExecFloat.P3109.toNatBits =
        some binary6p5se.positiveInfinityBits ∧
      outcome.status?.map (fun status =>
        (status.saturated, status.mappedSpecial)) =
      some (false, false) := by
  native_decide

end FloatLibTests.Conformance.P3109.Projection
