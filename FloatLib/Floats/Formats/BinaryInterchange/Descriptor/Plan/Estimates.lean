/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Format.Definition
public import FloatLib.Floats.ExecFloat.Backends.Selection.Metadata

/-!
# Cost estimates for binary descriptor execution

These engineering priors guide static candidate selection; they never affect semantics or
refinement. The model follows the threshold selection used by GMP and the separation of planning
from execution used by FFTW.

Generated-code inspection and benchmark calibration remain necessary because Lean's compiler,
target architecture, and workload can move useful thresholds.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/--
Coarse superlinear work estimate for exact significand arithmetic.

This is intentionally cheap to reduce at specialization time. It is an engineering feature, not
an asymptotic-complexity theorem.
-/
@[inline] def quadraticWork (bits : Nat) : Nat :=
  bits * bits / 16

/--
Width- and operation-sensitive estimate for the generic kernel.

The constants are calibrated with `benchmarks/scripts/format-comparison.sh`, in units of
approximately 100 ns. Above 128 bits, fixed allocation costs dominate the measured range;
limb-count terms account for the remaining arbitrary-precision work.
-/
def genericEstimate (format : FloatFormat) (operation : Operation) : Candidate :=
  let bits := format.bitWidth
  let limbs := (bits + 31) / 32
  let work :=
    if bits ≤ 8 then
      -- Calibrated in approximately 100 ns units; only relative costs affect selection.
      match operation with
      | .add => 18
      | .sub => 31
      | .mul => 18
      | .div => 20
      | .sqrt => 29
      | .fma => 16
    else if bits ≤ 128 then
      match operation with
      | .add | .sub => 80 + 4 * bits
      | .mul => 120 + quadraticWork bits
      | .div => 180 + 2 * quadraticWork bits
      | .sqrt => 220 + 2 * quadraticWork bits
      | .fma => 180 + 2 * quadraticWork bits
    else
      match operation with
      | .add => 41 + limbs / 10
      | .sub => 47 + limbs / 10
      | .mul => 39 + limbs / 4
      | .div => 45 + limbs / 2
      | .sqrt => 80 + 5 * limbs / 2
      | .fma => 37 + limbs / 4
  {
    name := s!"binary-interchange {operation.longLabel} exact baseline"
    kind := .generic
    steadyCost := work
    allocations := if bits ≤ 8 then 0 else if bits ≤ 64 then 1 else 3
  }

/--
Estimate for a monomorphic binary32 or binary64 specialization.

The shared addition, multiplication, and division estimates use geometric means of measured
binary32 and binary64 costs, on the same approximately 100 ns scale as `genericEstimate`.
-/
def fixedFormatEstimate (operation : Operation) : Candidate where
  name := s!"binary-interchange {operation.longLabel} fixed-format kernel"
  kind := .fixedFormat
  steadyCost :=
    match operation with
    | .add | .sub => 1
    | .mul => 1
    | .div => 3
    | .sqrt => 55
    | .fma => 28

/--
Estimate for a reusable one-word kernel on a structurally eligible descriptor.

Tiny-format constants are calibrated against the same descriptor carrier as the table candidate.
Wider-format estimates use measured binary16 and 24-bit costs.
-/
def nativeWordEstimate (format : FloatFormat) (operation : Operation) : Candidate where
  name := s!"binary-interchange {operation.longLabel} native-word kernel"
  kind := .nativeWord
  steadyCost :=
    if format.bitWidth ≤ 8 then
      -- The word FMA repeatedly measured near 18 units, independently of tiny encoded width.
      match operation with
      | .add => 12
      | .sub => 14
      | .mul => 8
      | .div => 11
      | .sqrt => 22 + format.bitWidth
      | .fma => 18
    else
      match operation with
      | .add | .sub => 1
      | .mul => 1
      | .div => 4
      | .sqrt => 82
      | .fma => 46

/-- Estimate for a fixed-count native-limb kernel. -/
def fixedLimbEstimate (operation : Operation) : Candidate where
  name := s!"binary-interchange {operation.longLabel} fixed-limb kernel"
  kind := .fixedLimbs
  steadyCost :=
    match operation with
    | .add | .sub => 48
    | .mul => 80
    | .div => 190
    | .sqrt => 230
    | .fma => 150

/--
Estimate for a kernel over a runtime-sized buffer of 32-bit limbs.

Measured addition and subtraction costs grow linearly in the limb count; multiplication and FMA
include the quadratic schoolbook product. Both this kernel and the generic kernel allocate on
every call. Their allocation estimates are equal, so selection compares the estimated times.
Division and square root have no wide-limb kernel and receive the generic cost.
-/
def wideLimbEstimate (format : FloatFormat) (operation : Operation) : Candidate :=
  let limbs := (format.bitWidth + 31) / 32
  {
    name := s!"binary-interchange {operation.longLabel} wide-limb kernel"
    kind := .wideLimbs
    storage := .wideLimbs
    steadyCost :=
      match operation with
      | .add | .sub => 6 + 17 * limbs / 20
      | .mul => 3 + 6 * limbs / 5 + limbs * limbs / 20
      | .fma => 6 + 2 * limbs + limbs * limbs / 20
      | .div | .sqrt => (genericEstimate format operation).steadyCost
    allocations := 3
  }

/--
Calibrated table-generation work per encoded result.

The small width bands capture the measured decrease in generator overhead per entry as a table
gets larger. They depend only on encoded width and operation, never on a catalogued format name.
-/
def tableGenerationCost (format : FloatFormat) (operation : Operation) : Nat :=
  let bits := format.bitWidth
  match operation with
  | .add =>
      if bits ≤ 4 then 28 else if bits ≤ 6 then 24 else 22
  | .sub =>
      if bits ≤ 4 then 30 else if bits ≤ 6 then 29 else 25
  | .mul =>
      if bits ≤ 4 then 28 else if bits ≤ 6 then 26 else 22
  | .div =>
      if bits ≤ 4 then 28 else if bits ≤ 6 then 26 else 23
  | .sqrt =>
      if bits ≤ 4 then 36 else if bits ≤ 6 then 24 else 23
  | .fma =>
      if bits ≤ 4 then 34 else if bits ≤ 5 then 31 else 28

/--
Estimate for a dense byte table over all encoded operands.

One result occupies one byte because this candidate is only constructed when `bitWidth ≤ 8`.
The selector's memory policy independently rejects tables that are valid but too large.

`execFloatBackendCalibration` showed table construction to be approximately linear in the number
of encoded results for each operation. The operation-specific coefficient is therefore a more
accurate and more stable prior than multiplying by the public generic-kernel estimate: table
generation runs below the `ExecFloat` carrier boundary and has a different constant factor.
-/
def tableEstimate (format : FloatFormat) (operation : Operation) : Candidate :=
  let radix := 2 ^ format.bitWidth
  let entries := radix ^ operation.arity
  {
    name := s!"binary-interchange {operation.longLabel} exhaustive table"
    kind := .exhaustiveTable
    steadyCost := 3
    setupCost := entries * tableGenerationCost format operation
    setupAllocations := 1
    residentBytes := entries
  }

end FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan
