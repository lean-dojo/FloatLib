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

A standard `n`-bit posit uses a `16n`-bit quire, so `Posit32` goes with the 512-bit `Quire32`.
Through the shared `bits` parameter, the public configured quire type ties each standard quire to
its posit width, and that makes a mismatch between posit and quire widths a type error. Runtime
operations, semantic views, and proofs come from other modules.

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
    (bits_ge_two : 2 ≤ bits := by
      first
      | decide
      | fail "ExecFloat.Posit.Quire requires bits ≥ 2") :=
  Formats.Posit.Quire.Model (Posit.descriptor bits bits_ge_two)

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
