/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Codec.Runtime

/-!
# Decimal sign operations

IEEE 754-2019 §5.5.1 specifies bit operations, including on noncanonical
representations. `Bits.copy`, `negate`, `abs`, and `copySign` preserve every bit
below the sign. They neither quiet signaling NaNs nor report exceptions.
The corresponding datum operations retain the quantum and NaN metadata.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

namespace Datum

/-- Read the sign, including the sign of a zero or NaN. -/
def isSignMinus : Datum → Bool
  | .finite s _ _ | .infinity s | .nan s _ _ => s

/-- Replace just the sign, without quieting a signaling NaN. -/
def withSign (negative : Bool) : Datum → Datum
  | .finite _ c q => .finite negative c q
  | .infinity _ => .infinity negative
  | .nan _ t p => .nan negative t p

/-- Copy a complete datum. Stored-word copying is `Bits.copy`. -/
def copy (d : Datum) : Datum := d

/-- Clear the sign, including on zeros and NaNs. -/
def abs (d : Datum) : Datum := d.withSign false

/-- Preserve the first datum except for the sign supplied by the second. -/
def copySign (x y : Datum) : Datum := x.withSign y.isSignMinus

end Datum

namespace Bits

/-- Copy every bit, including noncanonical coefficient and special-value bits. -/
def copy (f : Format) (word : BitVec f.bitWidth) : BitVec f.bitWidth := word

/-- Replace the stored sign while retaining all lower bits. -/
def withSign (f : Format) (negative : Bool) (word : BitVec f.bitWidth) :
    BitVec f.bitWidth :=
  pack f negative (payload f word)

/-- Reverse the stored sign, preserving signaling NaNs and noncanonical encodings. -/
def negate (f : Format) (word : BitVec f.bitWidth) : BitVec f.bitWidth :=
  withSign f (!negative f word) word

/-- Clear the stored sign without canonicalizing the representation. -/
def abs (f : Format) (word : BitVec f.bitWidth) : BitVec f.bitWidth :=
  withSign f false word

/-- Copy the second word's sign onto the otherwise unchanged first word. -/
def copySign (f : Format) (x y : BitVec f.bitWidth) : BitVec f.bitWidth :=
  withSign f (negative f y) x

end Bits
end FloatLib.Floats.Formats.DecimalInterchange
