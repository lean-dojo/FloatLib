/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Proof

/-!
# Parameterized posit `ExecFloat` types

`ExecFloat.Posit (bits := n)` takes one parameter, the total encoded width, and that width picks
both the mathematical descriptor and the persistent storage plan. `Posit8`, `Posit16`, `Posit32`,
and `Posit64` are the standard widths. Arithmetic capabilities, value operations, notation
instances, and proofs all come from other modules.

Building the type doesn't depend on operation dispatch. So tooling, serialization code, and new
backends get a small dependency boundary, while users see one type, `ExecFloat.Posit (bits := n)`.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat
namespace Posit

/--
The validated descriptor selected by `ExecFloat.Posit`, the record `{ bits := bits }`.

Quantities derived from the width, such as `payloadBits` and `regimeExponentStep`, are read from
this record, independently of the storage carrier.
-/
abbrev descriptor
    (bits : Nat)
    (bits_ge_two : 2 ≤ bits := by
      first
      | decide
      | fail "ExecFloat.Posit requires bits ≥ 2") : Format :=
  { bits
    bits_ge_two }

/--
The encoded-format family underlying `ExecFloat.Posit`.

Most users need only `ExecFloat.Posit`. Generic planners and capability inspection use `Family`
to refer to the same format, storage plan, and carrier as the public type.
-/
abbrev Family
    (bits : Nat)
    (bits_ge_two : 2 ≤ bits := by
      first
      | decide
      | fail "ExecFloat.Posit requires bits ≥ 2") :=
  let format := Posit.descriptor bits bits_ge_two
  let plan := Configured.StoragePlan.forKnownWidth format bits rfl
  Configured.Family format (Configured.Code plan) plan

end Posit

/--
An executable Posit Standard (2022) value selected by its total encoded width.

Storage and operation backends are selected statically from the descriptor and certified
capability policy. The standard requires at least two bits: a numeral width is checked by
`decide`, and any other width needs the proof `bits_ge_two`.
-/
abbrev Posit
    (bits : Nat)
    (bits_ge_two : 2 ≤ bits := by
      first
      | decide
      | fail "ExecFloat.Posit requires bits ≥ 2") :=
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
