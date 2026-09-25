/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Basic
public import FloatLib.Numerics.Enclosure.Interval.BinaryGrid
public import FloatLib.Numerics.Enclosure.Interval.Elementary
public import FloatLib.Numerics.Enclosure.Interval.Fused
public import FloatLib.Numerics.Enclosure.Interval.Hyperbolic
public import FloatLib.Numerics.Enclosure.Interval.InverseTrig
public import FloatLib.Numerics.Enclosure.Interval.Operations

/-!
# Rational and binary-grid expression backends

`Backend.ofRounding` combines the interval operations with any rational outward rounder.
`Backend.rational` keeps exact rational endpoints. `Backend.binaryGrid` uses integer arithmetic
for algebraic operations and rounds rational elementary-function bounds back onto its grid.

The elementary enclosures and their domain checks are shared by all endpoint backends.
`BackendsProof` proves the common `Backend.Sound` contract for all three backends.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Backend

variable {α : Type*}

/-- Accuracy controls shared by the expression backends. Both settings allow zero. -/
structure Config where
  /-- Fractional bits for square-root bounds and, when selected, the binary endpoint grid. -/
  precision : Nat := 64
  /-- Taylor approximation degree for exponential, logarithmic, and trigonometric bounds. -/
  degree : Nat := 16
  deriving DecidableEq, Repr, Inhabited

/--
Rational enclosures for elementary expression operations.

Arithmetic constructors return `none`; the backends dispatch them to their own arithmetic.
Logarithm requires a positive lower endpoint, and square root requires a nonnegative one.
Inverse sine and cosine require inputs in `[-1, 1]`; tangent requires a cosine enclosure
that excludes zero.
-/
def elementaryBounds? (config : Config) : UnaryOp → Interval ℚ → Option (Interval ℚ)
  | .exp, I => some (expBounds I config.degree)
  | .log, I => logBounds? I config.degree
  | .sin, I => some (sinBounds I config.degree)
  | .cos, I => some (cosBounds I config.degree)
  | .tan, I => tanBounds? I config.degree
  | .asin, I => asinBounds? I config.degree config.precision
  | .acos, I => acosBounds? I config.degree config.precision
  | .atan, I => some (atanBounds I config.degree)
  | .sinh, I => some (sinhBounds I config.degree)
  | .cosh, I => some (coshBounds I config.degree)
  | .tanh, I => some (tanhBounds I config.degree)
  | .sqrt, I => sqrtBounds? I config.precision
  | _, _ => none

/--
Build an expression backend from a partial rational outward rounder.

Algebraic operations compute exact rational endpoint bounds before rounding. Elementary
operations first produce rational enclosures at the configured accuracy, then round outward.
Failed decoding, rejected domains, and unrepresentable output bounds propagate as `none`.
-/
def ofRounding (R : OutwardRounding α ℚ) (config : Config := {}) : Backend α where
  decode := R.decode
  const? := R.enclose?
  unary? op I :=
    match op with
    | .neg => neg? R I
    | .abs => abs? R I
    | .inv => inv? R I
    | .pow n => pow? R I n
    | _ =>
      match I.decode? R.decode with
      | none => none
      | some a =>
        match elementaryBounds? config op a with
        | none => none
        | some b => encloseInterval? R b
  binary? op I J :=
    match op with
    | .add => add? R I J
    | .sub => sub? R I J
    | .mul => mul? R I J
    | .div => div? R I J
    | .min => min? R I J
    | .max => max? R I J
  ternary? op I J K :=
    match op with
    | .fma => fma? R I J K

/-- Exact rational endpoints, with configurable rational elementary-function enclosures. -/
def rational (config : Config := {}) : Backend ℚ :=
  ofRounding Internal.rationalOutwardRounding config

/--
Integer endpoints representing multiples of `2^(-config.precision)`.

Arithmetic, absolute value, powers, and endpoint comparisons stay in integer arithmetic.
Elementary functions decode their input once and round the rational result bounds onto the
same grid. The scale is supplied by this backend, so intervals from different grids must be
converted before they are combined.
-/
def binaryGrid (config : Config := {}) : Backend Int where
  decode := BinaryGrid.decode config.precision
  const? q := some (BinaryGrid.enclose config.precision q)
  unary? op I :=
    match op with
    | .neg => some (BinaryGrid.neg I)
    | .abs => some (BinaryGrid.abs I)
    | .inv => BinaryGrid.div? config.precision (point (BinaryGrid.scale config.precision)) I
    | .pow n =>
      some (if n = 2 then BinaryGrid.square config.precision I
        else BinaryGrid.pow config.precision I n)
    | _ =>
      match elementaryBounds? config op (I.map (BinaryGrid.toRat config.precision)) with
      | none => none
      | some b =>
        let lo := BinaryGrid.enclose config.precision b.lo
        let hi := BinaryGrid.enclose config.precision b.hi
        some ⟨lo.lo, hi.hi⟩
  binary? op I J :=
    match op with
    | .add => some (BinaryGrid.add I J)
    | .sub => some (BinaryGrid.sub I J)
    | .mul => some (BinaryGrid.mul config.precision I J)
    | .div => BinaryGrid.div? config.precision I J
    | .min => some ⟨min I.lo J.lo, min I.hi J.hi⟩
    | .max => some ⟨max I.lo J.lo, max I.hi J.hi⟩
  ternary? op I J K :=
    match op with
    | .fma => some (BinaryGrid.fma config.precision I J K)

end FloatLib.Numerics.Interval.Backend
