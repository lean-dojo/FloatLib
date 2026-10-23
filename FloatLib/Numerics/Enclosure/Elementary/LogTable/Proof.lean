/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridProof
public import FloatLib.Numerics.Enclosure.Elementary.LogTable.Runtime

/-!
# Containment for the cached logarithms of `j / 32`

Each cached entry is `logUnreduced` on the grid of `Internal.logTableBits` fractional bits, so it
encloses its logarithm (`containsReal_logUnreduced`), and outward coarsening keeps every real member
on a coarser grid (`Interval.BinaryGrid.containsReal_coarsen`). `containsReal_logTableAt?` combines
the two for every read the table answers.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.BinaryGrid

/-- A table read encloses the logarithm of its entry. -/
theorem containsReal_logTableAt? {index precision : Nat} {I : Interval Int}
    (h : logTableAt? index precision = some I) :
    I.ContainsReal (Interval.BinaryGrid.decode precision)
      (Real.log ((((index + 24 : ℕ) : ℚ) / 32 : ℚ) : ℝ)) := by
  unfold logTableAt? at h
  split at h
  · rename_i hbound
    cases Option.some.inj h
    apply Interval.BinaryGrid.containsReal_coarsen
    rw [Nat.add_sub_cancel' hbound.2]
    simp only [Internal.logTable, Array.getElem_ofFn, Internal.forceCache, Thunk.get,
      Internal.logTableEntry]
    exact containsReal_logUnreduced (by positivity) Internal.logTableBits
  · simp at h

end FloatLib.Numerics.Enclosure.BinaryGrid
