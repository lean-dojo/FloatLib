/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Configured.Core
public import FloatLib.Floats.Formats.Block.SharedScale.Runtime

/-!
# Executable configured shared-scale blocks

These operations expose complete storage, exact decoding, and contextual quantization at a
caller-selected exponent.

The caller supplies the shared exponent, so different calibration strategies can use the same
quantizer. Exponents and significands are unbounded integers; the vector type fixes the lane count.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.SharedScale

variable {lanes : Nat}

/-- Wrap a complete shared-scale block code without conversion. -/
@[inline] def ofCode (code : Formats.Block.SharedScaleCode lanes) :
    ExecFloat.SharedScale lanes :=
  ExecFloat.ofRaw code

/-- Recover the complete shared-scale block code without conversion. -/
@[inline] def toCode (value : ExecFloat.SharedScale lanes) :
    Formats.Block.SharedScaleCode lanes :=
  value.raw

/-- Construct a block from one exponent and exactly `lanes` stored significands. -/
@[inline] def ofComponents (exponent : Int) (significands : Vector Int lanes) :
    ExecFloat.SharedScale lanes :=
  ofCode { exponent, significands }

/-- Stored shared binary exponent. -/
@[inline] def exponent (value : ExecFloat.SharedScale lanes) : Int :=
  value.toCode.exponent

/-- Stored integer significands. -/
@[inline] def significands (value : ExecFloat.SharedScale lanes) : Vector Int lanes :=
  value.toCode.significands

/-- Decode every lane to its exact rational value. -/
@[inline] def decode (value : ExecFloat.SharedScale lanes) : Vector Rat lanes :=
  Formats.Block.decode value.toCode

/-- Quantize every lane at an explicitly supplied shared exponent. -/
@[inline] def quantizeAt (exponent : Int) (input : Vector Rat lanes) :
    ExecFloat.SharedScale lanes :=
  ofCode (Formats.Block.quantizeAt exponent input)

end FloatLib.Floats.ExecFloat.SharedScale
