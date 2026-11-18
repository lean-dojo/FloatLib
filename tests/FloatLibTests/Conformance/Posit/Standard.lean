/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit
public import FloatLib.Tactic.FloatDecide

/-!
# Posit Standard (2022) names and refinement

The public §5.4 names use the existing certified arithmetic. These clients
exercise their refinement theorems and registered kernel forms. Section 5.3
compares complete signed words, including NaR.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Posit.Standard

open FloatLib.Floats
open Formats.Posit

example (x y : Posit16) :
    ExecFloat.Posit.addition x y = Configured.Spec.addition x y :=
  congrFun (congrFun ExecFloat.Posit.addition_eq_spec x) y

example (x y : Posit16) :
    ExecFloat.Posit.subtraction x y = Configured.Spec.subtraction x y :=
  congrFun (congrFun ExecFloat.Posit.subtraction_eq_spec x) y

example (x y : Posit16) :
    ExecFloat.Posit.multiplication x y = Configured.Spec.multiplication x y :=
  congrFun (congrFun ExecFloat.Posit.multiplication_eq_spec x) y

example (x y : Posit16) :
    ExecFloat.Posit.division x y = Configured.Spec.division x y :=
  congrFun (congrFun ExecFloat.Posit.division_eq_spec x) y

example (x : Posit16) :
    ExecFloat.Posit.sqrt x = Configured.Spec.sqrt x :=
  congrFun ExecFloat.Posit.sqrt_eq_spec x

example :
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.addition (3 : Posit8) 5) =
      ExecFloat.Posit.toNatBits (8 : Posit8) ∧
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.subtraction (5 : Posit8) 3) =
      ExecFloat.Posit.toNatBits (2 : Posit8) ∧
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.multiplication (3 : Posit8) 5) =
      ExecFloat.Posit.toNatBits (15 : Posit8) ∧
    ExecFloat.Posit.isNaR (ExecFloat.Posit.division (3 : Posit8) 0) = true := by
  float_decide

example :
    ExecFloat.Posit.compareEqual (ExecFloat.Posit.nar : Posit8) ExecFloat.Posit.nar = true ∧
    ExecFloat.Posit.compareNotEqual (ExecFloat.Posit.nar : Posit8) 0 = true ∧
    ExecFloat.Posit.compareLess (ExecFloat.Posit.nar : Posit8) (-1) = true ∧
    ExecFloat.Posit.compareLessEqual (ExecFloat.Posit.nar : Posit8) ExecFloat.Posit.nar = true ∧
    ExecFloat.Posit.compareGreater (0 : Posit8) ExecFloat.Posit.nar = true ∧
    ExecFloat.Posit.compareGreaterEqual (0 : Posit8) 0 = true := by
  float_decide

example :
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.negate (0 : Posit8)) = 0 ∧
    ExecFloat.Posit.toNatBits
      (ExecFloat.Posit.negate (ExecFloat.Posit.nar : Posit8)) = 128 := by
  float_decide

/-- Section 5.2 absolute value has exact numerical semantics for every width and carrier. -/
example {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]
    (x : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Posit.toRat? (ExecFloat.Posit.abs x) =
      (ExecFloat.Posit.toRat? x).map (fun q => |q|) :=
  ExecFloat.Posit.toRat?_abs x

/-- Section 5.2 sign has exact numerical semantics for every width and carrier. -/
example {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]
    (x : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Posit.toRat? (ExecFloat.Posit.sign x) =
      (ExecFloat.Posit.toRat? x).map
        (fun q => if q < 0 then -1 else if q = 0 then 0 else 1) :=
  ExecFloat.Posit.toRat?_sign x

/-- Posit Standard (2022), §5.2: the integer −2^24, the eight-bit word 129, is fixed by
nearest-integer rounding. `tests/oracles/posit_standard.py` lists this input as its one known
difference from the reference. -/
example :
    ExecFloat.Posit.nearestInt (ExecFloat.Posit.ofNatBits 129 : Posit8) =
      ExecFloat.Posit.ofNatBits 129 := by
  apply ExecFloat.Posit.nearestInt_of_int (n := -16777216)
  decide +kernel

/-- Section 5.2 successors wrap through NaR, whose other basic functions propagate it. -/
example :
    ExecFloat.Posit.toNatBits
      (ExecFloat.Posit.next (ExecFloat.Posit.ofNatBits 127 : Posit8)) = 128 ∧
    ExecFloat.Posit.toNatBits
      (ExecFloat.Posit.prior (ExecFloat.Posit.nar : Posit8)) = 127 ∧
    ExecFloat.Posit.toNatBits
      (ExecFloat.Posit.sign (ExecFloat.Posit.nar : Posit8)) = 128 := by
  float_decide

/-- Sections 5.5–5.8 distinguish real-domain failures from finite endpoint values. -/
example :
    ExecFloat.Posit.isNaR (ExecFloat.Posit.rSqrt (0 : Posit8)) = true ∧
    ExecFloat.Posit.isNaR (ExecFloat.Posit.logPlus1 (-1 : Posit8)) = true ∧
    ExecFloat.Posit.isNaR (ExecFloat.Posit.pow (0 : Posit8) 0) = true ∧
    ExecFloat.Posit.isNaR (ExecFloat.Posit.rootN (-1 : Posit8) 2) = true ∧
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.rootN (-1 : Posit8) (-3)) =
      ExecFloat.Posit.toNatBits (-1 : Posit8) ∧
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.compound (-1 : Posit8) 0) =
      ExecFloat.Posit.toNatBits (1 : Posit8) := by
  float_decide

/-- Section 5.6 uses the argument of x+iy; this differs from atan2(y,x) APIs. -/
example :
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.arcTan2Pi (0 : Posit8) 1) =
      ExecFloat.Posit.toNatBits (ExecFloat.Posit.ofRat (1 / 2) : Posit8) ∧
    ExecFloat.Posit.toNatBits (ExecFloat.Posit.arcTan2Pi (-1 : Posit8) 0) =
      ExecFloat.Posit.toNatBits (1 : Posit8) ∧
    ExecFloat.Posit.isNaR (ExecFloat.Posit.arcTan2 (0 : Posit8) 0) = true := by
  float_decide

/-- Section 6.1 widens every encoding exactly, without a finite-input restriction. -/
example {source : Format} (target : Format) (hwidth : source.bits ≤ target.bits)
    (x : Model source) :
    Model.pₘToₙ target x =
      Model.ofNatBits (x.toNatBits * 2 ^ (target.bits - source.bits)) :=
  Model.pₘToₙ_eq_append_zero target hwidth x

/-- Section 6.1 leaves every word unchanged when the precision is unchanged. -/
example {format : Format} (x : Model format) :
    Model.pₘToₙ format x = x :=
  Model.pₘToₙ_self x

/-- Section 6.1 preserves the selected codec and the exact destination model. -/
example {source target : Format}
    {sp : Configured.StoragePlan source} {tp : Configured.StoragePlan target}
    {sc tc : Type} [ExecFloat.ModelCodec sp (Model source) sc]
    [ExecFloat.ModelCodec tp (Model target) tc]
    (x : ExecFloat (Configured.Family source sc sp)) :
    ExecFloat.Posit.toModel (ExecFloat.Posit.pₘToₙ x :
      ExecFloat (Configured.Family target tc tp)) =
      Model.pₘToₙ target (ExecFloat.Posit.toModel x) :=
  ExecFloat.Posit.toModel_pₘToₙ x

/-- Section 6.1: exact signed widening, finite narrowing and NaR across two storage widths. -/
example :
    ExecFloat.Posit.toNatBits
      (ExecFloat.Posit.pₘToₙ (ExecFloat.Posit.ofNatBits 129 : Posit8) : Posit16) = 33024 ∧
    ExecFloat.Posit.toNatBits
      (ExecFloat.Posit.pₘToₙ (ExecFloat.Posit.ofNatBits 33024 : Posit16) : Posit8) = 129 ∧
    ExecFloat.Posit.toNatBits
      (ExecFloat.Posit.pₘToₙ (ExecFloat.Posit.nar : Posit8) : Posit16) = 32768 := by
  float_decide

end FloatLibTests.Conformance.Posit.Standard

namespace FloatLibTests.Conformance.Posit.Interchange

open FloatLib.Floats FloatLib.Numerics

variable {posit : Formats.Posit.Format}
  {pp : Formats.Posit.Configured.StoragePlan posit} {pc : Type}
  [ExecFloat.ModelCodec pp (Formats.Posit.Model posit) pc]
  {binary : Formats.BinaryInterchange.FloatFormat}
  {bp : Formats.BinaryInterchange.Configured.StoragePlan binary} {bc : Type}
  [ExecFloat.ModelCodec bp (Formats.BinaryInterchange.Model binary) bc]

local notation "P" => ExecFloat (Formats.Posit.Configured.Family posit pc pp)
local notation "B" => ExecFloat (Formats.BinaryInterchange.Configured.Family binary bc bp)

example (x : B) :
    x.cast (target := P) =
      ExecFloat.Posit.Conversion.run ExecFloat.Posit.Conversion.Context.default
        ((ExecFloat.Binary.decode x).map SignedRat.value) :=
  ExecFloat.Posit.cast_fromIEEE x

example (x : P) (mode : RoundingMode) :
    x.cast (target := B) (mode := mode) =
      ExecFloat.Binary.Conversion.run
        (ExecFloat.Binary.Conversion.Policy.default.withRounding mode)
        ((ExecFloat.Posit.decode x).map SignedRat.ofRat) :=
  ExecFloat.Posit.cast_toIEEE x mode

end FloatLibTests.Conformance.Posit.Interchange
