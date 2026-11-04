/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.DPD.Declet

/-!
# Packing trailing decimal digits into consecutive DPD declets

Below its combination field, a DPD word stores the rest of the coefficient: the trailing digits are
split into base-1000 groups, and each group goes into its own ten-bit declet, least significant
first. Decoding reads every declet as three decimal digits, redundant patterns included.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.DPD

/-- Pack `groups` base-1000 digits into consecutive ten-bit declets, least significant first. -/
def encodeTrailing : Nat → Nat → Nat
  | 0, _ => 0
  | groups + 1, n => encodeDeclet (n % 1000) + 1024 * encodeTrailing groups (n / 1000)

/-- Decode all declets, including redundant patterns, into a decimal coefficient. -/
def decodeTrailing : Nat → Nat → Nat
  | 0, _ => 0
  | groups + 1, n => decodeDeclet (n % 1024) + 1000 * decodeTrailing groups (n / 1024)

end FloatLib.Floats.Formats.DecimalInterchange.DPD
