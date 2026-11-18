/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Compiled.TinyTable.Table
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Routes
public import FloatLib.Tactic.CompilerOptimize

/-!
# The `descriptor_backends` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

set_option hygiene false in
/--
`descriptor_backends op := table, structural, generic` declares the three tagged candidates of
the descriptor operation `op`: `opTable` (an alternative: the exhaustive table `table`, offered
to descriptors of at most eight bits), `opStructural` (an alternative: `structural route` for
the descriptor's structural route, when it has one) and `opGeneric` (the baseline `generic`).
-/
macro "descriptor_backends " op:ident " := " table:term ", " structural:term ", "
    generic:term : command => do
  let spec := Lean.mkIdent (`Descriptor.Spec ++ op.getId)
  let tableName := Lean.mkIdent (op.getId.appendAfter "Table")
  let structuralName := Lean.mkIdent (op.getId.appendAfter "Structural")
  let genericName := Lean.mkIdent (op.getId.appendAfter "Generic")
  let operation := Lean.mkIdent (`FloatLib.Floats.ExecFloat.Backend.Operation ++ op.getId)
  `(/--
    The exhaustive table of this operation, offered to descriptors of at most eight encoded
    bits.
    -/
    @[compiler_optimize]
    def $tableName (format : FloatFormat) : Option (Certified (@$spec format)) :=
      $table

    /-- The structural kernel of this operation, offered when the descriptor has a route. -/
    @[compiler_optimize]
    def $structuralName (format : FloatFormat) : Option (Certified (@$spec format)) :=
      (structuralRoute? format $operation).map $structural

    /-- The width-generic kernel of this operation: the baseline of every descriptor. -/
    @[compiler_optimize baseline]
    def $genericName (format : FloatFormat) : Certified (@$spec format) :=
      $generic)

end FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan
