/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Constants.Runtime
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime

/-!
# Cached logarithms of `j / 32`

`Internal.logTable` holds `log (j / 32)` for `j` from 24 through 48 on the grid of
`Internal.logTableBits` fractional bits. Each entry is computed with `logUnreduced` at most once per
process, on first use, and a read on a coarser grid rounds the cached entry outward. The certified
binary power reads the table to bring a logarithm argument in `[3/4, 3/2)` within `1/48` of one.

Module initialization only allocates the cells: the table disables closed-term extraction, and
every read goes through `Internal.forceCache`.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.BinaryGrid

/-- Fractional bits of the cached logarithms of `j / 32`. -/
def Internal.logTableBits : Nat := 512

/-- `log ((index + 24) / 32)` on the grid of `Internal.logTableBits` fractional bits. -/
def Internal.logTableEntry (index : Nat) : Interval Int :=
  logUnreduced ((index + 24 : ℕ) / 32) Internal.logTableBits

set_option compiler.extract_closed false in
/-- `log (j / 32)` for `j` from 24 through 48, each computed on first use and then shared. -/
def Internal.logTable : Array (Thunk (Interval Int)) :=
  Array.ofFn (n := 25) fun index => Thunk.mk fun _ => Internal.logTableEntry index.val

/--
`log ((index + 24) / 32)` on the grid of `precision` fractional bits, coarsened from its cached
entry, or `none` beyond the table and for grids finer than `Internal.logTableBits`.
-/
def logTableAt? (index precision : Nat) : Option (Interval Int) :=
  if h : index < Internal.logTable.size ∧ precision ≤ Internal.logTableBits then
    some (Interval.BinaryGrid.coarsen (Internal.logTableBits - precision)
      (Internal.forceCache Internal.logTable[index]))
  else none

end FloatLib.Numerics.Enclosure.BinaryGrid
