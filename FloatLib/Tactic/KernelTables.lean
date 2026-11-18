/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lanes

/-!
# Certified kernel operation tables

The command builds packed tables and registers proved lookup rules for stored values.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Packed

/--
`kernel_tables name (size := n) for F := format` declares the packed tables of the nearest-even
kernel addition, subtraction and multiplication of the family `F`, whose format `format` has `n`
encodings, and the three tagged rules that turn an operation on stored values into a lookup.
See the module documentation.
-/
macro "kernel_tables " name:ident " (" &"size" " := " size:num ")" " for " family:term " := "
    format:term : command => do
  let declared (suffix : String) := Lean.mkIdent (name.getId ++ Lean.Name.mkSimple suffix)
  let lookup (suffix : String) :=
    Lean.mkIdent (name.getId ++ Lean.Name.mkSimple suffix ++ `lookup)
  let add ← `(command|
    /-- The packed table of the nearest-even kernel addition on all pairs of encodings. -/
    lane_table $(declared "kernelAdd") (width := 8) (size := $size) :=
      KernelPath.add $format Model.IEEERoundingMode.nearest)
  let sub ← `(command|
    /-- The packed table of the nearest-even kernel subtraction on all pairs of encodings. -/
    lane_table $(declared "kernelSub") (width := 8) (size := $size) :=
      KernelPath.sub $format Model.IEEERoundingMode.nearest)
  let mul ← `(command|
    /-- The packed table of the nearest-even kernel multiplication on all pairs of encodings. -/
    lane_table $(declared "kernelMul") (width := 8) (size := $size) :=
      KernelPath.mul $format Model.IEEERoundingMode.nearest)
  `($add:command
    $sub:command
    $mul:command
    /-- The encoding of a nearest-even sum is one lane of the packed addition table. -/
    @[kernel_optimize (cost := 4)]
    theorem $(declared "toNat_add_nearest") (x y : FloatLib.Floats.ExecFloat $family) :
        toNat (Value.add Model.IEEERoundingMode.nearest x y) =
          Nat.land (Nat.shiftRight $(declared "kernelAdd")
            (Nat.mul 8 (Nat.add (Nat.mul (toNat x) $size) (toNat y)))) 255 :=
      Value.toNat_of_table (Value.toNat_add _ x y) (Flat.add_eq_add _) rfl rfl
        $(lookup "kernelAdd")

    /-- The encoding of a nearest-even difference is one lane of the packed subtraction table. -/
    @[kernel_optimize (cost := 4)]
    theorem $(declared "toNat_sub_nearest") (x y : FloatLib.Floats.ExecFloat $family) :
        toNat (Value.sub Model.IEEERoundingMode.nearest x y) =
          Nat.land (Nat.shiftRight $(declared "kernelSub")
            (Nat.mul 8 (Nat.add (Nat.mul (toNat x) $size) (toNat y)))) 255 :=
      Value.toNat_of_table (Value.toNat_sub _ x y) (Flat.sub_eq_sub _) rfl rfl
        $(lookup "kernelSub")

    /-- The encoding of a nearest-even product is one lane of the packed multiplication table. -/
    @[kernel_optimize (cost := 4)]
    theorem $(declared "toNat_mul_nearest") (x y : FloatLib.Floats.ExecFloat $family) :
        toNat (Value.mul Model.IEEERoundingMode.nearest x y) =
          Nat.land (Nat.shiftRight $(declared "kernelMul")
            (Nat.mul 8 (Nat.add (Nat.mul (toNat x) $size) (toNat y)))) 255 :=
      Value.toNat_of_table (Value.toNat_mul _ x y) (Flat.mul_eq_mul _) rfl rfl
        $(lookup "kernelMul"))

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
