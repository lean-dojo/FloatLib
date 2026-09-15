/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Model.Decode
public import FloatLib.Floats.Formats.Posit.Formatting.Parsing
public import FloatLib.Numerics.Exact.Dyadic.Format

/-!
# Exact user-facing posit formatting

Ordinary posits print as exact decimals, using a decimal exponent for fractional values. The
unique exceptional word is printed as `NaR`, matching the Posit Standard terminology. Formatting
does not require a shortest decimal expansion; it preserves the exact value at every width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/--
Host-independent display string of one posit value.

Ordinary values print through the exact decimal formatter; the unique exceptional word prints as
`NaR`. There is no radix-two fallback. `Formatting.Proof` proves that `parse` recovers every input
word, including NaR.
-/
def display {format : Format} (value : Model format) : String :=
  match value.toDyadic? with
  | some exact => FloatLib.Numerics.DecimalText.formatDyadic exact
  | none => "NaR"

instance {format : Format} : ToString (Model format) where
  toString := Model.display

end FloatLib.Floats.Formats.Posit.Model
