/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Type
public import FloatLib.Floats.Formats.Posit.Quire.Model.Core

/-!
# Configured posit quire types

The public configured quire type associates a standard quire with its posit width. Other modules
install runtime operations, semantic views, and proofs.

A standard `n`-bit posit uses a `16n`-bit quire. The shared `bits` parameter makes mismatched posit
and quire widths a type error.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 3.4, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats

namespace ExecFloat.Posit

/-- Standard `16n`-bit quire associated with a configured `n`-bit posit. -/
abbrev Quire
    (bits : Nat)
    (bits_ge_two : 2 ≤ bits := by decide) :=
  Formats.Posit.Quire.Model (Posit.format bits bits_ge_two)

end ExecFloat.Posit

/-! ## Standard quires -/

/-- The 128-bit quire of `Posit8`. -/
abbrev Quire8 := ExecFloat.Posit.Quire (bits := 8)

/-- The 256-bit quire of `Posit16`. -/
abbrev Quire16 := ExecFloat.Posit.Quire (bits := 16)

/-- The 512-bit quire of `Posit32`. -/
abbrev Quire32 := ExecFloat.Posit.Quire (bits := 32)

/-- The 1024-bit quire of `Posit64`. -/
abbrev Quire64 := ExecFloat.Posit.Quire (bits := 64)

end FloatLib.Floats
