/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Instances
public import FloatLibBenchmarks.Standards.Protocol

/-!
# Inputs for the Posit Standard timing matrix

Posit Standard (2022), es = 2. All eight requested widths use the same code
formula: a dense positive fraction below one, a positive value above one and
the first operand's negative. `arcCosH` uses the second operand to stay in its
real domain. Quire values are prepared by exact `pToQ` before native timing.
Kernel inputs use literal posit and quire words; carrier construction remains
inside the observed term and has its own control row.

Posit Standard (2022), §§3.3 and 6.2, specifies the encoding and `pToQ`.
-/

@[expose] public section

namespace FloatLibBenchmarks.Standards.Posit

open FloatLib.Floats

/-- Stored scalar and quire operands for one valid posit width. -/
structure Sample (width : Nat) (valid : 2 ≤ width) where
  x : ExecFloat.Posit width valid
  y : ExecFloat.Posit width valid
  z : ExecFloat.Posit width valid
  q : Formats.Posit.Quire.Model { bits := width, bits_ge_two := valid }
  r : Formats.Posit.Quire.Model { bits := width, bits_ge_two := valid }
  ieee : Binary32

/-- Common deterministic word construction, with small changes in the low bits. -/
def sample (width : Nat) (valid : 2 ≤ width) (seed : Nat) : Sample width valid :=
  let one := 2 ^ (width - 2)
  let unit := 2 ^ (width - 5)
  let a := one - unit / 3 - seed % 3
  let b := one + unit / 5 + 1 + seed % 3
  let x : ExecFloat.Posit width valid := ExecFloat.Posit.ofNatBits a
  let y : ExecFloat.Posit width valid := ExecFloat.Posit.ofNatBits b
  { x, y, z := ExecFloat.Posit.ofNatBits (2 ^ width - a)
    q := ExecFloat.Posit.Quire.pToQ x
    r := ExecFloat.Posit.Quire.pToQ y
    ieee := ExecFloat.Binary.ofNatBits (0x3f5abcde + seed % 3) }

/-- Observe a decimal parse, distinguishing failure from every successful code. -/
def observeParse {width : Nat} {valid : 2 ≤ width}
    (value : Except Formats.Posit.Model.ParseError (ExecFloat.Posit width valid)) : Nat :=
  match value with
  | .error reason => 2 * observeString (reprStr reason)
  | .ok value => 1 + 2 * ExecFloat.Posit.toNatBits value

attribute [kernel_optimize unfold] sample observeParse

end FloatLibBenchmarks.Standards.Posit
