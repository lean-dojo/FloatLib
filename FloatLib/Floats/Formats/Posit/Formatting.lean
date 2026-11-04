/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Decode
public import FloatLib.Floats.Formats.Posit.Formatting.Parsing
public import FloatLib.Numerics.Exact.DecimalText.Notation

/-!
# Exact user-facing posit formatting

An ordinary posit prints as its exact decimal value with no redundant fractional zeros, so `1.5`
prints as `1.5` and `6` as `6`. When fixed notation would be longer, as it is for tiny magnitudes,
the output switches to a decimal exponent. As for the one exceptional word, it prints as `NaR`,
the Posit Standard's name for it. At every width the printed string denotes the exact value.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/--
Host-independent display string of one posit value.

Ordinary values print through the compact exact decimal formatter, and the unique exceptional
word prints as `NaR`. There is no radix-two fallback. `Formatting.Proof` proves that `parse`
recovers every input word, including NaR.
-/
def display {format : Format} (value : Model format) : String :=
  match value.toDyadic? with
  | some exact => FloatLib.Numerics.DecimalText.formatDyadicCompact exact
  | none => "NaR"

instance {format : Format} : ToString (Model format) where
  toString := Model.display

end FloatLib.Floats.Formats.Posit.Model
