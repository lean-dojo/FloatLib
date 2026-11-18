/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLibBenchmarks.Standards.Posit
public import FloatLibBenchmarks.Standards.P3109
public meta import FloatLibBenchmarks.Standards.Posit
public meta import FloatLibBenchmarks.Standards.P3109

/-!
# Literal inputs for the standard timing matrices

The elaborators evaluate the same input constructors used by the native
clients, then emit their complete stored words. This constructs input data
only and makes no assertion about operation results.
-/

public meta section

open Lean Elab Term FloatLib.Floats FloatLibBenchmarks.Standards

/-- Materialize all posit and quire input words before kernel timing. -/
elab "posit_sample% " width:num seed:num : term <= expectedType => do
  let w := width.getNat
  if valid : 2 ≤ w then
    let input := Posit.sample w valid seed.getNat
    let numeral (n : Nat) : Term := ⟨Syntax.mkNumLit n.repr⟩
    let x := numeral (ExecFloat.Posit.toNatBits input.x)
    let y := numeral (ExecFloat.Posit.toNatBits input.y)
    let z := numeral (ExecFloat.Posit.toNatBits input.z)
    let q := numeral input.q.toNatBits
    let r := numeral input.r.toNatBits
    let ieee := numeral (ExecFloat.Binary.toNatBits input.ieee)
    elabTerm (← `({
      x := ExecFloat.Posit.ofNatBits $x
      y := ExecFloat.Posit.ofNatBits $y
      z := ExecFloat.Posit.ofNatBits $z
      q := Formats.Posit.Quire.Model.ofNatBits _ $q
      r := Formats.Posit.Quire.Model.ofNatBits _ $r
      ieee := ExecFloat.Binary.ofNatBits $ieee
    })) expectedType
  else throwError "posit width must be at least two"

/-- Materialize P3109 words; scale and carrier construction remain in the timed term. -/
elab "p3109_sample% " width:num seed:num : term <= expectedType => do
  let w := width.getNat
  if valid : 4 ≤ w then
    let input := P3109.sample w valid seed.getNat
    let numeral (n : Nat) : Term := ⟨Syntax.mkNumLit n.repr⟩
    let x := numeral input.x.toNatBits
    let y := numeral input.y.toNatBits
    let z := numeral input.z.toNatBits
    elabTerm (← `(P3109.sampleFromWords $width (by decide) $x $y $z)) expectedType
  else throwError "matrix width must be at least four"
