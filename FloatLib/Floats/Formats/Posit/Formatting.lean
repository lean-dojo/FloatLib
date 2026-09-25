/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Decode
public import FloatLib.Floats.Formats.Posit.Formatting.Parsing
public import FloatLib.Numerics.Exact.Dyadic.Format
public import FloatLib.Numerics.Exact.DecimalText.Notation

/-!
# Exact user-facing posit formatting

Ordinary posits print as exact decimals without redundant fractional zeros, so `1.5` prints as
`1.5` and `6` as `6`. Values whose fixed notation would be longer, such as tiny magnitudes, use a
decimal exponent instead. The unique exceptional word is printed as `NaR`, matching the Posit
Standard terminology. The output always denotes the exact value at every width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/--
Host-independent display string of one posit value.

Ordinary values print through the compact exact decimal formatter; the unique exceptional word
prints as `NaR`. There is no radix-two fallback. `Formatting.Proof` proves that `parse` recovers
every input word, including NaR.
-/
def display {format : Format} (value : Model format) : String :=
  match value.toDyadic? with
  | some exact => FloatLib.Numerics.DecimalText.formatDyadicCompact exact
  | none => "NaR"

instance {format : Format} : ToString (Model format) where
  toString := Model.display

end FloatLib.Floats.Formats.Posit.Model
