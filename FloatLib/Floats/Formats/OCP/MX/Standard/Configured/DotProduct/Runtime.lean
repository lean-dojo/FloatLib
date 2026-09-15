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

These entry points accept the standard MX carrier with independently chosen element profiles
and return configured IEEE binary32. Packing preserves the one-rounding exact-accumulation
policy of `Standard.dot` and `Standard.dotGeneral`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.OCP.MX.Standard

open FloatLib.Floats.Formats.OCP.MX.Standard

/-- Exact block accumulation followed by one configured binary32 projection. -/
@[inline] def dot {leftProfile rightProfile : Profile}
    (left : Standard leftProfile) (right : Standard rightProfile) : ExecFloat.Binary 8 23 :=
  ExecFloat.Binary.ofModel (Formats.OCP.MX.Standard.dot left.toCode right.toCode)

/-- Exact accumulation across all blocks, with one final configured binary32 rounding. -/
@[inline] def dotGeneral {leftProfile rightProfile : Profile} {n : Nat}
    (left : Vector (Standard leftProfile) n) (right : Vector (Standard rightProfile) n) :
    ExecFloat.Binary 8 23 :=
  ExecFloat.Binary.ofModel
    (Formats.OCP.MX.Standard.dotGeneral (left.map toCode) (right.map toCode))

end FloatLib.Floats.ExecFloat.OCP.MX.Standard
