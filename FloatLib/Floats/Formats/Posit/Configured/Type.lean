/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Parameterized posit `ExecFloat` types

The public configured posit type is parameterized by its total encoded width, which selects both
the mathematical descriptor and the persistent storage plan. Other modules install arithmetic
capabilities, value operations, notation instances, and proofs.

Type construction does not depend on operation dispatch, so tooling, serialization code, and new
backends get a small dependency boundary, and users still see the single type
`ExecFloat.Posit (bits := n)`.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat
namespace Posit

/-- The validated descriptor selected by `ExecFloat.Posit`. -/
abbrev format
    (bits : Nat)
    (bits_ge_two : 2 ≤ bits := by decide) : Format :=
  { bits
    bits_ge_two }

/--
The encoded-format family underlying `ExecFloat.Posit`.

Most users need only `ExecFloat.Posit`. Generic planners and capability inspection use `Family`
to refer to the same format, storage plan, and carrier as the public type.
-/
abbrev Family
    (bits : Nat)
    (bits_ge_two : 2 ≤ bits := by decide) :=
  let format := Posit.format bits bits_ge_two
  let plan := Configured.StoragePlan.forKnownWidth format bits rfl
  Configured.Family format (Configured.Code plan) plan

end Posit

/--
An executable Posit Standard (2022) value selected by its total encoded width.

Storage and operation backends are selected statically from the descriptor and certified
capability policy.
-/
abbrev Posit
    (bits : Nat)
    (bits_ge_two : 2 ≤ bits := by decide) :=
  FloatLib.Floats.ExecFloat (Posit.Family bits bits_ge_two)

end ExecFloat

/-! ## Standard formats -/

/-- The 8-bit posit of the Posit Standard (2022). -/
abbrev Posit8 := ExecFloat.Posit (bits := 8)

/-- The 16-bit posit of the Posit Standard (2022). -/
abbrev Posit16 := ExecFloat.Posit (bits := 16)

/-- The 32-bit posit of the Posit Standard (2022). -/
abbrev Posit32 := ExecFloat.Posit (bits := 32)

/-- The 64-bit posit of the Posit Standard (2022). -/
abbrev Posit64 := ExecFloat.Posit (bits := 64)

end FloatLib.Floats
