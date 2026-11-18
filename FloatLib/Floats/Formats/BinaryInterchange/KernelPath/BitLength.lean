/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Proof.Arithmetic
public import FloatLib.Numerics.Kernel.Bits.Proof.PopCount

/-!
# Bit length of a significand in few kernel steps

Normalizing a significand needs the position of its leading bit. The bit length of a natural
number by the kernel's fast operations (`laneLength`, `searchLength`, `windowLength`, `bitLength`
and their theorems) is in `FloatLib.Numerics.Kernel.Bits` and
`FloatLib.Numerics.Kernel.BitsProof`, where the exact layer uses it too.

`significandLength F m` answers `F + 1` for a significand with its leading bit set after one
comparison, and calls `bitLength` for a subnormal one. A search step costs the kernel about as much
as the whole lane method at a few hundred bits, which is why the narrow widths keep the lanes.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics.Kernel (bitLength bitLength_eq)

/--
The bit length of a significand that has no leading bit at position `F`: `bitLength` with the
bound `F + 1`. It is a definition of its own so that an operation calls it and does not carry
its code on the path of a normal significand.
-/
def subnormalLength (F m : Nat) : Nat :=
  bitLength (Nat.succ F) m

/--
The bit length of a significand `m < 2 ^ (F + 1)` (`significandLength_eq`): `F + 1` when its
leading bit is set, which one comparison decides, and `subnormalLength` otherwise. A normal
significand costs the same at every width.
-/
def significandLength (F m : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.pow 2 F) m)
    (subnormalLength F m)
    (Nat.succ F)

/-- `significandLength F m` is the bit length of `m`, for every `m < 2 ^ (F + 1)`. -/
theorem significandLength_eq {F m : Nat} (hm : m < 2 ^ (F + 1)) :
    significandLength F m = if m = 0 then 0 else m.log2 + 1 := by
  unfold significandLength
  cases hnormal : Nat.ble (Nat.pow 2 F) m
  · exact bitLength_eq hm
  · have hle : 2 ^ F ≤ m := Nat.le_of_ble_eq_true hnormal
    have hm0 : m ≠ 0 := by
      have := Nat.two_pow_pos F
      omega
    change F + 1 = _
    rw [ite_eq_right hm0, (Nat.log2_eq_iff hm0).2 ⟨hle, hm⟩]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
