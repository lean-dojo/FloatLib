/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Real.Basic

/-!
# Elementary scalar capabilities

`MathFunctions` supplies elementary functions, absolute value, and π for a scalar domain.
The interface is independent of encoded formats, storage layouts, and execution backends.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Scalar functions and π shared by numerical and model code.

This class records which operations a scalar domain can evaluate; it does not by itself promise
exactness, an error bound, correct rounding, a selectable rounding mode, or IEEE status flags.
Those guarantees belong to separate contracts supplied by each implementation.
-/
class MathFunctions (α : Type) where
  /-- Exponential function. -/
  exp : α → α
  /-- Hyperbolic tangent. -/
  tanh : α → α
  /-- Hyperbolic cosine. -/
  cosh : α → α
  /-- Principal square root. -/
  sqrt : α → α
  /-- Absolute value. -/
  abs : α → α
  /-- Natural logarithm. -/
  log : α → α
  /-- Circular constant π. -/
  pi : α
  /-- Cosine. -/
  cos : α → α
  /-- Sine. -/
  sin : α → α
  /-- Hyperbolic sine. -/
  sinh : α → α

/-- Host floating-point implementations of the scalar functions and π. -/
instance : MathFunctions Float where
  exp := Float.exp
  tanh := Float.tanh
  cosh := Float.cosh
  sqrt := Float.sqrt
  abs := Float.abs
  log := Float.log
  pi := 3.14159265358979323846
  cos := Float.cos
  sin := Float.sin
  sinh := Float.sinh

/-- Real interpretations of the scalar functions and π. -/
noncomputable instance : MathFunctions ℝ where
  exp := Real.exp
  tanh := Real.tanh
  cosh := Real.cosh
  sinh := Real.sinh
  sqrt := Real.sqrt
  abs := fun x => |x|
  log := Real.log
  pi := Real.pi
  cos := Real.cos
  sin := Real.sin

end FloatLib.Numerics
