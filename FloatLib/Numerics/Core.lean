/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Value
public import FloatLib.Numerics.Core.System
public import FloatLib.Numerics.Core.Proof
public import FloatLib.Numerics.Core.ExactSemantics
public import FloatLib.Numerics.Core.Representation

/-!
# Universal numerical-system core

This core describes complete values, numerical systems, optional exact observations, and
type-directed runtime representations, all without reference to a representation, and it assumes no
radix, exponent field, storage width, exceptional-value convention, or arithmetic backend.

Static format declaration syntax is exported on its own from `FloatLib.Numerics.Core.Declaration`,
which keeps the semantic core free of elaborator infrastructure.
-/

@[expose] public section
