/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats
public meta import Lean.Elab.Command

/-!
# Theorem headings of `#float_info` reports

A report titles a theorem group "about T values" only when the group is stated about values of
`T`. A configured posit lists its own theorems, including those of the packed kernels its storage
uses, then the proof model's and the quire's, each reached by a named function; the proof model's
report lists no configured theorem. A configured fixed-point value is split from its code in the
same way. A report whose groups are about several types, such as P3109's or `Float32`'s, uses one
neutral heading. This module uses the module system, so the reports also check that every theorem
they list is visible to a module that imports the families.
-/

public meta section

open Lean Elab Command Meta
open FloatLib.Floats.Formats.Posit
open FloatLib.Floats.ExecFloat

/-- Whether any theorem group in `surfaces` lists `name`. -/
private def lists (surfaces : List TheoremSurface) (name : Name) : Bool :=
  surfaces.any fun surface => surface.declarations.contains name

/-- Every theorem group of a profile, its own and its related types'. -/
private def allSurfaces (profile : FormatProfile) : List TheoremSurface :=
  profile.theoremSurfaces ++ profile.relatedTheorems.flatMap (·.surfaces)

run_cmd liftTermElabM do
  let all := Backend.Operation.all.map fun operation => (operation, true)
  let word := FloatInfo.profile 32 "" .word all
  let pair := FloatInfo.profile 100 "" .pair all
  let wide := FloatInfo.profile 200 "" .wide all
  let model := FloatInfo.profile 32 ""
  -- The packed kernels' theorems are about the configured carrier that uses them.
  unless lists word.theoremSurfaces ``Configured.Backend.storedNativeWordAdd_eq_spec &&
      lists word.theoremSurfaces ``Configured.NativeCode.toModel_pack &&
      !lists word.theoremSurfaces ``Configured.Backend.storedNativeLimbAdd_eq_spec &&
      lists pair.theoremSurfaces ``Configured.Backend.storedNativeLimbAdd_eq_spec &&
      lists pair.theoremSurfaces ``Configured.PairCode.toModel_pack &&
      !lists pair.theoremSurfaces ``Configured.Backend.storedNativeWordAdd_eq_spec &&
      !lists (allSurfaces wide) ``Configured.Backend.storedNativeWordAdd_eq_spec &&
      !lists (allSurfaces wide) ``Configured.Backend.storedNativeLimbAdd_eq_spec do
    throwError "the configured posit reports do not list the packed kernels their storage uses"
  -- `x + y` reaches the model through its lifted reference operation and the codec's decoding.
  unless lists word.theoremSurfaces ``FloatLib.Floats.ExecFloat.ModelCodec.decode_liftBinary do
    throwError "the configured posit report gives no route from `x + y` to the proof model"
  -- The proof model's report lists no theorem about configured values.
  for name in [``Configured.Backend.storedNativeWordAdd_eq_spec,
      ``Configured.Backend.storedNativeLimbAdd_eq_spec, ``Configured.NativeCode.toModel_pack,
      ``Configured.PairCode.toModel_pack, ``FloatLib.Floats.ExecFloat.Posit.toModel_ofModel,
      ``FloatLib.Floats.ExecFloat.Posit.Quire.toRat?_pToQ] do
    if lists (allSurfaces model) name then
      throwError "the posit proof model's report lists the configured theorem {name}"
  -- The quire theorems appear only in the section about the quire, reached by `pToQ`.
  for (profile, embedding) in [(word, ``FloatLib.Floats.ExecFloat.Posit.Quire.pToQ),
      (model, ``Quire.Model.pToQ)] do
    let quire := profile.relatedTheorems.filter (·.type == ``Quire.Model)
    let [section_] := quire
      | throwError "a posit report has no single section about the quire"
    unless section_.embedding == embedding &&
        lists section_.surfaces ``Quire.Model.toRat?_pToQ &&
        !lists profile.theoremSurfaces ``Quire.Model.toRat?_pToQ do
      throwError "a posit report lists the quire theorems outside the section about the quire"

end

/-! ## Reports

Theorem names in a report print relative to the open namespaces, so this section opens only
`FloatLib.Floats`, as the guide does.
-/

section Reports

open FloatLib.Floats

/--
Theorems about Posit32 values:
  [verified] arithmetic equals its reference operation: ExecFloat.Proof.add_notation_eq_spec and 9 more
-/
#guard_msgs (substring := true) in
#float_info Posit32

/--
Theorems about Formats.Posit.Model values, reached with ExecFloat.Posit.toModel:
-/
#guard_msgs (substring := true) in
#float_info Posit32

/--
Theorems about Formats.Posit.Quire.Model values, reached with ExecFloat.Posit.Quire.pToQ:
-/
#guard_msgs (substring := true) in
#float_info Posit32

/-- A configured fixed-point type with two decimal places. -/
abbrev Cents := ExecFloat.FixedPoint FloatLib.Numerics.decimalRadix 2

-- The theorems about `Cents` values come first; the code's follow under their own heading. A
-- `Unit` destination context leaves no conversion option to name.
/--
Theorems about Cents values:
  [verified] arithmetic equals its reference operation: ExecFloat.Proof.add_notation_eq_spec and 3 more
  [verified] exact rational arithmetic: ExecFloat.FixedPoint.toRat_add and 3 more
  [verified] decoding to the code: ExecFloat.FixedPoint.toCode_ofCode and 2 more

Theorems about Formats.FixedPoint.Code values, reached with ExecFloat.FixedPoint.toCode:
-/
#guard_msgs (substring := true) in
#float_info Cents

/--
as a target: `cast` and `ExecFloat.convert` round once into this type from ℚ; it takes no conversion options
-/
#guard_msgs (substring := true) in
#float_info Cents

-- A native float's groups are about `Float32` values and about the configured software kernels,
-- so their heading claims neither.
/--
Theorems:
  [verified] native binary32 conversion boundary: ExecFloat.Binary.toBits32_ofFloat32 and 6 more
-/
#guard_msgs (substring := true) in
#float_info Float32

/-- The signed, extended, precision-four P3109 format of the guide. -/
abbrev B8P4SE := ExecFloat.P3109 Formats.P3109.Format.binary8p4se

-- The P3109 groups are about values, codes, datums, and blocks, so their heading claims none.
/--
Theorems:
  [verified] exact representation and checked encoding: ExecFloat.P3109.decode_eq_format_decode and 5 more
-/
#guard_msgs (substring := true) in
#float_info B8P4SE

end Reports
