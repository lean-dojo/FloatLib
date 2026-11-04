/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Configured.Runtime
public import FloatLib.Floats.Formats.OCP.MX.Standard.DotProduct.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Type
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core

/-!
# Configured MX dot products

These entry points take two standard MX operands, each with its own element profile, and return a
configured IEEE binary32, so you can take the dot product of an E4M3 block with an INT8 block.
Packing keeps the policy of `Standard.dot` and `Standard.dotGeneral`, which accumulate exactly and
round once.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.OCP.MX.Standard

open FloatLib.Floats.Formats.OCP.MX.Standard

/-- Exact block accumulation followed by one configured binary32 projection. -/
@[inline] def dot {leftProfile rightProfile : Profile}
    (left : Standard leftProfile) (right : Standard rightProfile) : Binary32 :=
  ExecFloat.Binary.ofModel (Formats.OCP.MX.Standard.dot left.toCode right.toCode)

/-- Exact accumulation across all blocks, with one final configured binary32 rounding. -/
@[inline] def dotGeneral {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Standard leftProfile) n) (right : Vector (Standard rightProfile) n) :
    Binary32 :=
  ExecFloat.Binary.ofModel
    (Formats.OCP.MX.Standard.dotGeneral (left.map toCode) (right.map toCode))

end FloatLib.Floats.ExecFloat.OCP.MX.Standard
