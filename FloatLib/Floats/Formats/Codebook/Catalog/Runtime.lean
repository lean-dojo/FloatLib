/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Core.Runtime
public import Mathlib.Data.Int.Notation

/-!
# Named tiny-codebook definitions

Two tiny executable tables live here. One is a one-bit bipolar code with `0 ↦ -1` and `1 ↦ +1`,
and the other a two-bit ternary code for `0`, `+1` and `-1` with one reserved word. They show that
a lookup encoding needs no IEEE-style field layout. The theorems about each word's denotation are
in `Catalog.Proof`.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.Codebook.Catalog

/-- One-bit bipolar encoding: `0 ↦ -1` and `1 ↦ +1`. -/
def bipolar1 : Codebook 1 ℤ where
  denote code :=
    match code.toNat with
    | 0 => .finite (-1)
    | _ => .finite 1

/--
Two-bit signed ternary encoding: `00 ↦ 0`, `01 ↦ +1`, `10 ↦ -1`, and `11 ↦ reserved`.
-/
def ternary2 : Codebook 2 ℤ where
  denote code :=
    match code.toNat with
    | 0 => .finite 0
    | 1 => .finite 1
    | 2 => .finite (-1)
    | bits => .exceptional (.reserved (some bits))

end FloatLib.Floats.Formats.Codebook.Catalog
