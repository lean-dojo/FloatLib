/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Configured.Core

/-!
# Value display of codebook formats

A codebook value prints the table entry it denotes, so `toString` and `#eval` of a P3109 value
show its exact dyadic value, `inf`, `-inf` or `nan` rather than its stored word.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Codebook

universe u

/-- Codebook values print their denotation, using the text of the table's scalars. -/
instance {width : Nat} {α : Type u} [ToString α] (book : Formats.Codebook width α) :
    FormatDisplay (Family book) where
  format code := toString (book.denote code)

end FloatLib.Floats.ExecFloat.Codebook
