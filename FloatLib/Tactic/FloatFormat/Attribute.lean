/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Numerics.Attribute

/-!
# Static format reduction attribute

`float_format` registers a static descriptor for numerical reduction.
-/

public meta section

/--
Register a static `FloatFormat` definition for concrete `Model` proof reduction.

The format stays ordinary compile-time data. This attribute only lets `numerics` unfold its
name when checking a closed encoded value.
-/
macro (name := attrFloatFormat) "float_format" : attr => `(attr| numerics_reduction)
