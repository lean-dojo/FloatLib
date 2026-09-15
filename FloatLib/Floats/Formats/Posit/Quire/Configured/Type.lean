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

The public configured quire type associates a standard quire with its posit width. Runtime
operations, semantic views, and proofs are installed by separate modules.

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
end FloatLib.Floats
