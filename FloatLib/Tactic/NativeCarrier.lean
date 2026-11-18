/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.IEEE754.Native.Carrier

/-!
# Named native carriers

The command specializes the common carrier API and its proved conversion equations.
-/

public meta section

namespace FloatLib.Floats.Native

open FloatLib.Floats.Formats.BinaryInterchange

open Lean Elab Command in
/-- Generate a named carrier API; instances and proofs stay in the common family. -/
elab "native_carrier " name:ident " := " format:term : command => do
  elabCommand (← `(/-- A native 16-bit carrier with the stated layout. -/
    abbrev $name := Carrier $format))
  for method in [`mk, `toBits, `canonical, `ofBits, `val, `ofFloat32, `ofFloat, `ofRat,
      `toFloat, `isNaN] do
    let aliasName := mkIdent (name.getId ++ method)
    let common := mkIdent (`FloatLib.Floats.Native.Carrier ++ method)
    let input ← match method with
      | `mk | `ofBits => `(UInt16)
      | `ofFloat32 => `(Float32)
      | `ofFloat => `(Float)
      | `ofRat => `(Rat)
      | _ => `($name)
    elabCommand (← `(@[inherit_doc $common] abbrev $aliasName (x : $input) :=
      $common (format := $format) x))
  let ofBits := mkIdent (name.getId ++ `ofBits)
  let roundtrip := mkIdent (name.getId ++ `ofBits_toBits)
  let bits := mkIdent (name.getId ++ `toBits_ofBits)
  let nan := mkIdent (name.getId ++ `toBits_ofBits_nan)
  elabCommand (← `(/-- Every native carrier value is recovered from its word. -/
    theorem $roundtrip (x : $name) : $ofBits x.toBits = x := Carrier.ofBits_toBits x))
  elabCommand (← `(/-- Non-NaN interchange words are preserved. -/
    theorem $bits (word : UInt16) (h : word &&& 0x7FFF ≤ ($format).infinity) :
        ($ofBits word).toBits = word := Carrier.toBits_ofBits word h))
  elabCommand (← `(/-- The format's quiet NaN word is preserved. -/
    theorem $nan : ($ofBits ($format).nan).toBits = ($format).nan :=
      Carrier.toBits_ofBits_nan))
  for (method, type, src, common) in
      [(`ofFloat32, ← `(Float32), ← `(FloatFormat.binary32), ``Carrier.ofFloat32_eq_spec),
        (`ofFloat, ← `(Float), ← `(FloatFormat.binary64), ``Carrier.ofFloat_eq_spec)] do
    let conversion := mkIdent (name.getId ++ method)
    let spec := mkIdent (name.getId ++ Name.mkSimple s!"{method}_eq_spec")
    let common := mkIdent common
    elabCommand (← `(/-- Conversion agrees with the reference cast, with NaNs normalized. -/
      theorem $spec (x : $type) :
          $conversion x = $ofBits (Model.cast $src ($format).model
            (Model.ofNatBits x.toBits.toNat) .nearest).toNatBits.toUInt16 := $common x))

end FloatLib.Floats.Native
