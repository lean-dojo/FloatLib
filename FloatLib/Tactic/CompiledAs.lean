/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean
public meta import FloatLib.Util.Declaration
public import Mathlib.Init -- Standard source linters.

/-!
# The `compiled_as` command

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

/--
`compiled_as f := g by lemma` declares the theorem `f_eq_compiled : @f = @g` and tags it
`@[csimp]`, so that compiled code runs `g` in place of `f`. `lemma` states
`f x₁ … xₙ = g x₁ … xₙ` for all arguments. A kernel-shaped definition has no compiled code of
its own or slow code, and this is how each one gets the code of the ordinary function it equals.
A docstring before the command replaces the generated one.
-/
macro doc?:(docComment)? "compiled_as " f:ident " := " g:ident " by " proofName:ident :
    command => do
  let name := Lean.mkIdentFrom f (f.getId.appendAfter "_eq_compiled")
  let text := s!"Compiled code runs `{g.getId}` in place of `{f.getId}`."
  let doc := doc?.getD (FloatLib.Floats.ExecFloat.generatedDoc text)
  `($doc:docComment @[csimp] theorem $name : @$f = @$g := by funext; exact $proofName ..)
