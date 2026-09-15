/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.Codebook.Core.Runtime

/-!
# Configured codebook identity

A complete lookup denotation determines a codebook family on the common `ExecFloat` carrier. The
selected codebook remains in the type, so equal-width lookup tables are never interchangeable.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

universe u

namespace ExecFloat
namespace Codebook

/-- Type-level identity retaining a complete lookup denotation. -/
inductive Family {width : Nat} {α : Type u} (book : Formats.Codebook width α) where
  | format

instance {width : Nat} {α : Type u} (book : Formats.Codebook width α) :
    EncodedFormat (Family book) where
  Code := Formats.Codebook.Code book
  Scalar := α

instance {width : Nat} {α : Type u} (book : Formats.Codebook width α) :
    FormatSemantics (Family book) where
  denote := book.denote

end Codebook

/-- Exact-width executable lookup encoding selected by its complete denotation table. -/
abbrev Codebook {width : Nat} {α : Type u} (book : Formats.Codebook width α) :=
  FloatLib.Floats.ExecFloat (Codebook.Family book)

end ExecFloat
end FloatLib.Floats
