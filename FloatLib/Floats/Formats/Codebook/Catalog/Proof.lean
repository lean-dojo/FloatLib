/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Catalog.Runtime

/-!
# Denotation theorems for named tiny codebooks

These lemmas expose the exact meaning of each catalog word without adding runtime code.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Codebook.Catalog

/-- The zero bit pattern of `bipolar1` denotes negative one. -/
@[simp] theorem bipolar1_denote_zero :
    bipolar1.denote (BitVec.ofNat 1 0) = .finite (-1) := by
  decide

/-- The one bit pattern of `bipolar1` denotes positive one. -/
@[simp] theorem bipolar1_denote_one :
    bipolar1.denote (BitVec.ofNat 1 1) = .finite 1 := by
  decide

/-- The `00` ternary code denotes zero. -/
@[simp] theorem ternary2_denote_zero :
    ternary2.denote (BitVec.ofNat 2 0) = .finite 0 := by
  decide

/-- The `01` ternary code denotes positive one. -/
@[simp] theorem ternary2_denote_positive :
    ternary2.denote (BitVec.ofNat 2 1) = .finite 1 := by
  decide

/-- The `10` ternary code denotes negative one. -/
@[simp] theorem ternary2_denote_negative :
    ternary2.denote (BitVec.ofNat 2 2) = .finite (-1) := by
  decide

/-- The `11` ternary code is the reserved exceptional word. -/
@[simp] theorem ternary2_denote_reserved :
    ternary2.denote (BitVec.ofNat 2 3) =
      .exceptional (.reserved (some 3)) := by
  decide

end FloatLib.Floats.Formats.Codebook.Catalog
