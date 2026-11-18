/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Standard
public import FloatLib.Tactic.KernelEval
import all Mathlib.Data.Nat.Digits.Defs

/-!
# Shared inputs for the N1169 timing matrix

The generator in `benchmarks/scripts/fixed-point-matrix.py` calls the standard names
directly. All lengths have the requested value width. Fract uses every nonsign bit
as fractional precision; accum splits its bits between integral and fractional
precision. The whole layout satisfies the mandatory C constraints from width 48.
Smaller layouts are explicitly extensions used to measure the same definitions.

Native operands are materialized before timing. Every result contributes to an
output checksum. `fixed_sample%` elaborates the same deterministic sample to
literal coefficients with kernel-checked range proofs, so kernel timings also
start from stored inputs. No overhead is subtracted from either reported result.

WG14 N1169 (2006 TR 18037 draft), §§4.1.1 and 4.2 (C clause 6.2.5), gives the type constraints.
-/

@[expose] public section

namespace FloatLibBenchmarks.Standards.FixedPoint

open FloatLib.Numerics FloatLib.Floats.Formats.FixedPoint.Embedded

/-- Equal value widths at all C lengths, with explicit small-width extensions. -/
def layout (width : Nat) : Layout where
  fractionalBits signed kind _ :=
    if kind = .fract then width - signed.toNat
    else width - width / 2 - signed.toNat
  integralBits _ _ := width / 2

/-- The benchmark layout meets all mandatory constraints from width 48. -/
theorem layout_valid (width : Nat) (h : 48 ≤ width) : (layout width).Valid := by
  constructor
  · intro signed kind length
    cases signed <;> cases kind <;> cases length <;>
      simp [layout, Length.minFractionalBits] <;> omega
  · intro signed length
    simp [layout]
    omega
  · intro length
    simp [layout]
    omega
  · intro signed kind left right _
    exact Nat.le_refl _
  · intro signed left right _
    exact Nat.le_refl _
  · intro length
    exact Nat.le_refl _

/-- Two already stored, nonzero dense coefficients for one format. -/
structure Sample (format : Format) where
  x : format.Code
  y : format.Code

/-- Reproducible code inputs spanning signs and nearby low coefficient bits. -/
def sample (format : Format) (seed : Nat) : Sample format :=
  let magnitude := (2 ^ format.precision - 1) / 3 + seed % 17
  let second := (2 ^ format.precision - 1) / 5 + seed % 7 + 1
  let sign := if format.signed && seed % 2 == 1 then 2 ^ format.precision else 0
  { x := format.ofBits (BitVec.ofNat format.width (sign + magnitude))
    y := format.ofBits (BitVec.ofNat format.width second) }

/-- Undefined results have a separate checksum value from every defined code. -/
def observe {format : Format} (value : Option format.Code) : Nat :=
  match value with
  | none => 0
  | some value => 1 + (Format.toBits value).toNat

/-- Signed integer observations retain both magnitude and sign. -/
def observeInt (value : Int) : Nat :=
  2 * value.natAbs + (decide (value < 0)).toNat

/-- Integer support functions distinguish undefined and defined outputs. -/
def observeInteger (value : Option Int) : Nat :=
  match value with
  | none => 0
  | some value => 1 + observeInt value

/-- A complete text-conversion observation includes end and range outcomes. -/
def observeText {format : Format} (value : Text.Result format) : Nat :=
  (Format.toBits value.value).toNat + value.endptr + value.rangeError.toNat

/-- A complete formatted-input observation includes consumption and status. -/
def observeScan {format : Format} (value : Formatted.ScanResult format) : Nat :=
  observe value.value + 5 * value.consumed +
    match value.status with
    | .success => 1
    | .matchingFailure => 2
    | .inputFailure => 3
    | .undefined => 4

/-- Parsing observations force the spelling, exact rational and type-selection fields. -/
def observeLiteral (value : Option Constant.Literal) : Nat :=
  match value with
  | none => 0
  | some value =>
    1 + value.spelling.length + observeInt value.value.num + value.value.den +
      value.type.signed.toNat + value.type.saturating.toNat + value.hexadecimal.toNat +
      (match value.type.kind with | .fract => 0 | .accum => 1) +
      (match value.type.length with | .short => 0 | .default => 1 | .long => 2)

/-- A fixed complete subject for input and constant parsing benchmarks. -/
def text : String := "-0x1.23456789abcdefp-3!"

/-- Nearest-even adjacent rounding, shared by every timed conversion. -/
def rounding : Rounding := NearestRounding.even.toRounding

/-- The ordinary full-precision nearest-even environment with saturation. -/
def environment : Environment where
  rounding _ := rounding
  FX_FRACT_OVERFLOW := .SAT
  FX_ACCUM_OVERFLOW := .SAT

attribute [kernel_optimize unfold] layout sample observe observeInt observeInteger
  observeText observeScan observeLiteral text rounding environment

/-- Three native trials over 32 preconstructed samples; no baseline subtraction. -/
@[noinline] def measure (label : String) (width : Nat) (format : Format)
    (operation : Sample format → Nat) : IO Unit := do
  let inputs := (List.range 32).toArray.map (sample format)
  let observation := operation (sample format 1)
  for trial in [0:3] do
    let mut sink := 0
    let start ← IO.monoNanosNow
    for _ in [0:4] do
      for input in inputs do
        sink := sink + operation input
    let elapsed := (← IO.monoNanosNow) - start
    IO.println s!"FIXED_NATIVE {label} width={width} trial={trial} ns={elapsed / 128} \
      sink={sink} value={observation}"

end FloatLibBenchmarks.Standards.FixedPoint

public meta section

open Lean Elab Term

/-- A materialized sample with literal coefficients and checked interval membership.
The expression's expected type supplies the format; an incorrect width/sign argument
cannot bypass either coefficient's range proof. This is benchmark input construction. -/
elab "fixed_sample% " width:num signed:ident seed:num : term <= expectedType => do
  let signed ← match signed.getId with
    | `true => pure true
    | `false => pure false
    | _ => throwError "expected true or false"
  let width := width.getNat
  let precision := width - signed.toNat
  let magnitude := (2 ^ precision - 1) / 3 + seed.getNat % 17
  let second := (2 ^ precision - 1) / 5 + seed.getNat % 7 + 1
  let modulus := 2 ^ width
  let first := ((if signed && seed.getNat % 2 == 1 then 2 ^ precision else 0) + magnitude) %
    modulus
  let decode (word : Nat) : Int :=
    if signed && 2 * word ≥ modulus then (word : Int) - modulus else word
  let integer (value : Int) : TermElabM Term := do
    let magnitude : Term := ⟨Syntax.mkNumLit value.natAbs.repr⟩
    if value < 0 then `(-$magnitude) else pure magnitude
  let x ← integer (decode first)
  let y ← integer (decode (second % modulus))
  elabTerm (← `({ x := ⟨$x, by decide +kernel⟩, y := ⟨$y, by decide +kernel⟩ })) expectedType
