/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Configured.Runtime
public import FloatLib.Floats.Formats.Codebook.Core.Nearest
public import FloatLib.Floats.ExecFloat.Conversion.Core

/-!
# Runtime conversion source for configured codebooks

Every word of a configured codebook has a finite or exceptional entry in its table, so the
codebook can be an exact source when you convert from it. Going the other way, the one quantizer
supplied is `nearest?`. It scans the table and returns the first finite codeword minimizing
`|x - c|`, so ties go to the lower word (see `Formats.Codebook.nearestCode`). We don't install it as
a generic conversion instance, because how to treat reserved words and which tie rule to use depend
on what a particular codebook is for.
-/

@[expose] public section

namespace FloatLib.Floats

namespace ExecFloat.Codebook
namespace Conversion

universe u

variable {width : Nat} {α : Type u} {book : Formats.Codebook width α}

/-- A configured codebook decodes through its complete selected lookup table. -/
instance exactDecoder :
    FloatLib.Floats.ExecFloat.ExactDecoder
      (ExecFloat.Codebook book) α where
  decode := ExecFloat.Codebook.decode

/--
The nearest configured codeword to `x`, or `none` when the table has no finite word.

Ties resolve to the lower word. `Formats.Codebook.nearestCode_spec` proves that the selected
word is finite and minimizes `|x - c|` over every finite codeword `c`.
-/
def nearest? [AddGroup α] [LinearOrder α] (x : α) : Option (ExecFloat.Codebook book) :=
  (Formats.Codebook.nearestCode book x).map ExecFloat.Codebook.ofCode

/-- Decoding the nearest configured codeword gives the closest finite table value. -/
theorem decode_nearest? [AddGroup α] [LinearOrder α] (x : α)
    (value : ExecFloat.Codebook book) (hnearest : nearest? (book := book) x = some value) :
    ∃ decoded, ExecFloat.Codebook.decode value = .finite decoded ∧
      ∀ other otherValue, book.denote other = .finite otherValue →
        |x - decoded| ≤ |x - otherValue| := by
  unfold nearest? at hnearest
  obtain ⟨code, hcode, rfl⟩ := Option.map_eq_some_iff.1 hnearest
  exact Formats.Codebook.nearestCode_spec book x code hcode

end Conversion
end ExecFloat.Codebook
end FloatLib.Floats
