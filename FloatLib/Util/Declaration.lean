/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public import Mathlib.Init -- Standard source linters.

/-!
# Documentation for generated declarations

Shared syntax construction for commands that generate documented declarations.
-/

public meta section

/--
The docstring of a declaration that a command generates, as syntax. The commands that
generate the per-operation declarations of a family use it.

The node has the shape that Lean's parser gives a plain documentation comment since Lean 4.36:
the opening `/--`, then a `commentBody` node that holds the text and the closing `-/` as two atoms.
-/
def FloatLib.Floats.ExecFloat.generatedDoc (text : String) :
    Lean.TSyntax `Lean.Parser.Command.docComment :=
  ⟨Lean.mkNode `Lean.Parser.Command.docComment #[Lean.mkAtom "/--",
    Lean.mkNode `Lean.Parser.Command.commentBody #[Lean.mkAtom text, Lean.mkAtom "-/"]]⟩
