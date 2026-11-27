/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.ElementaryTable
public import FloatLib.Numerics.Enclosure.Interval.Fused
public import FloatLib.Numerics.Enclosure.Interval.InverseHyperbolic
public import FloatLib.Numerics.Enclosure.Interval.InverseTrig
public import FloatLib.Numerics.Enclosure.Interval.Powers

/-!
# Rational and binary-grid expression backends

`Backend.ofRoundings` combines the interval operations with three rational outward rounders on one
endpoint carrier. One rounds the algebraic operations, one rounds reciprocals and quotients, and
one rounds the elementary functions, whose enclosures come from a table that you pass in.
`Backend.ofRounding` uses one rounder for all three and the table `elementaryBounds?`, and
`Backend.rational` is that backend with exact rational endpoints. `Backend.binaryGrid` uses
integer arithmetic for algebraic operations and rounds the bounds of `elementaryBounds?` back onto
its grid. `BackendsProof` proves the common `Backend.Sound` contract for each.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Backend

variable {α : Type*}

/--
Rational enclosures for elementary expression operations.

Arithmetic constructors return `none`, because each backend sends them to its own arithmetic.
Logarithm needs a positive lower endpoint and square root a nonnegative one. Inverse sine and cosine
need inputs in `[-1, 1]`, and tangent needs a cosine enclosure that excludes zero.
-/
def elementaryBounds? (config : Config) : UnaryOp → Interval ℚ → Option (Interval ℚ) :=
  elementaryWith (.legacy config)

/--
Build an expression backend from three partial rational outward rounders on one endpoint carrier
and a table of rational elementary enclosures.

`algebra` encloses constants and rounds negation, absolute value, natural powers, addition,
subtraction, multiplication, minimum, maximum and fused multiply-add. `quotient` rounds
reciprocals and quotients, and `elementary` rounds the enclosures that `table` gives for the
other unary operations. Each operation decodes its inputs with the rounder of its result,
computes rational bounds exactly and then rounds them outward. The backend reads endpoints with
`algebra.decode`, so `ofRoundings_sound` asks the three decoders to agree. Failed decoding, a
domain that the operation or the table rejects, and bounds that a rounder cannot represent all
give `none`.
-/
def ofRoundings (algebra quotient elementary : OutwardRounding α ℚ)
    (table : UnaryOp → Interval ℚ → Option (Interval ℚ)) : Backend α where
  decode := algebra.decode
  const? := algebra.enclose?
  unary? op I :=
    match op with
    | .neg => neg? algebra I
    | .abs => abs? algebra I
    | .inv => inv? quotient I
    | .pow n => pow? algebra I n
    | _ =>
      match I.decode? elementary.decode with
      | none => none
      | some a =>
        match table op a with
        | none => none
        | some b => encloseInterval? elementary b
  binary? op I J :=
    match op with
    | .add => add? algebra I J
    | .sub => sub? algebra I J
    | .mul => mul? algebra I J
    | .div => div? quotient I J
    | .min => min? algebra I J
    | .max => max? algebra I J
  ternary? op I J K :=
    match op with
    | .fma => fma? algebra I J K

/--
Build an expression backend from one partial rational outward rounder: `ofRoundings` with `R`
for every operation and the elementary enclosures `elementaryBounds? config`.

Algebraic operations compute exact rational endpoint bounds before rounding. Elementary
operations first produce rational enclosures at the configured accuracy, then round outward.
Failed decoding, rejected domains, and unrepresentable output bounds propagate as `none`.
-/
def ofRounding (R : OutwardRounding α ℚ) (config : Config := {}) : Backend α :=
  ofRoundings R R R (elementaryBounds? config)

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

/-- Adapt an existing unary elementary enclosure to the extension interface. -/
def elementaryExtension (op : UnaryOp) : Extension :=
  Extension.unary (fun config I => elementaryBounds? config op I)

/-- Inverse hyperbolic sine enclosure for registered evaluation. -/
def asinhExtension : Extension :=
  Extension.unary (fun config I => asinhBounds? I config.degree config.precision)

/-- Inverse hyperbolic cosine enclosure for registered evaluation. -/
def acoshExtension : Extension :=
  Extension.unary (fun config I => acoshBounds? I config.degree config.precision)

/-- Inverse hyperbolic tangent enclosure for registered evaluation. -/
def atanhExtension : Extension :=
  Extension.unary (fun config I => atanhBounds? I config.degree)

/-- Real powers on positive bases for registered evaluation. -/
def rpowExtension : Extension :=
  Extension.binary (fun config I J => rpowBounds? I J config.degree)

/-- Logarithms with a supplied positive base separated from one. -/
def logbExtension : Extension :=
  Extension.binary (fun config I J => logbBounds? I J config.degree)

end FloatLib.Numerics.Interval.Backend
