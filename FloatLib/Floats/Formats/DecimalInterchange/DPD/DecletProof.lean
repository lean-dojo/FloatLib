/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.DPD.Declet
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.SplitIfs

/-!
# Correctness of Cowlishaw's ten-bit declet table

This file checks Cowlishaw's table in both directions. Encoding a value below 1000 gives a ten-bit
declet, and decoding that declet gives back all three decimal digits. Going the other way,
re-encoding a ten-bit pattern clears the ignored high bits in the redundant cases and in no others.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.DPD

/-- The canonical encoding uses at most ten bits. -/
theorem encodeDeclet_lt (n : Nat) : encodeDeclet n < 1024 := by
  dsimp [encodeDeclet]
  split_ifs <;> omega

/-- Every ten-bit pattern denotes three decimal digits. -/
theorem decodeDeclet_lt (n : Nat) : decodeDeclet n < 1000 := by
  dsimp [decodeDeclet]
  split_ifs <;> omega

/-- The DPD table preserves all three input digits. -/
theorem decodeDeclet_encodeDeclet (n : Nat) (h : n < 1000) :
    decodeDeclet (encodeDeclet n) = n := by
  have table : ∀ n : Fin 1000, decodeDeclet (encodeDeclet n.val) = n.val := by
    decide +kernel
  exact table ⟨n, h⟩

/-- The only redundant declets have all three digits in `{8, 9}`.
Their canonical representative clears the two ignored high bits, as IEEE 754-2019 Tables 3.3
and 3.4 require, and every other ten-bit pattern is already canonical. -/
theorem encodeDeclet_decodeDeclet (n : Nat) (h : n < 1024) :
    encodeDeclet (decodeDeclet n) =
      if n / 2 % 8 = 7 ∧ n / 32 % 4 = 3 then n % 256 else n := by
  have table : ∀ n : Fin 1024, encodeDeclet (decodeDeclet n.val) =
      if n.val / 2 % 8 = 7 ∧ n.val / 32 % 4 = 3 then n.val % 256 else n.val := by
    decide +kernel
  exact table ⟨n, h⟩

end FloatLib.Floats.Formats.DecimalInterchange.DPD
