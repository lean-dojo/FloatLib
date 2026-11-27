/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Interval.Registry
public import FloatLib.Numerics.Enclosure.Expression.StandardProof
public import FloatLib.Tactic.Interval.Functions

/-!
# The standard calls

`π`, the real power and `e` are the calls `0`, `1` and `2` of `Standard.extensions`. These
checks cover:

* the enclosure of `π`: its ends are in order at every precision (`piBounds_lo_le_hi`), and its
  width is below `2 ^ (-precision)`, which the kernel checks at 16, 64 and 256 bits and
  `piBounds_width_lt` proves at every precision;
* the width of the enclosure of `e`, which the kernel compares with `2 ^ (-precision)` at 16, 64
  and 256 bits;
* closed checks by the exact backend with the standard calls added. They prove bounds on `π` at 16,
  64 and 256 bits, on `2 ^ (1 / 2)` and on `e`, so `Standard.extensions_sound` is not vacuous, and
  the bounds on `π` tighten with the precision;
* `Backend.Sound.of_noCalls` on the exact backend;
* the enclosures that `interval` registers: their containment theorems make one sound call table,
  each enclosure accepts a sample input, and `FloatLib.Tactic.Interval.Functions` registers each
  theorem for its function.
-/

public section

namespace FloatLibTests.Numerics.Standard

open FloatLib.Numerics FloatLib.Numerics.Interval FloatLib.Numerics.Interval.Backend

/-! ## The enclosure of `π` -/

example : (piBounds 16).hi - (piBounds 16).lo < 1 / 2 ^ 16 ∧
    (piBounds 64).hi - (piBounds 64).lo < 1 / 2 ^ 64 ∧
    (piBounds 256).hi - (piBounds 256).lo < 1 / 2 ^ 256 := by
  decide +kernel

example : (piBounds 4096).hi - (piBounds 4096).lo < 1 / 2 ^ 4096 :=
  piBounds_width_lt 4096

example (precision : Nat) : (piBounds precision).lo ≤ (piBounds precision).hi :=
  piBounds_lo_le_hi precision

example : piExtension.enclose? { precision := 64 } [] = some (piBounds 64) := rfl

/-! ## The enclosure of `e` -/

example : (eBounds 16).hi - (eBounds 16).lo < 1 / 2 ^ 16 ∧
    (eBounds 64).hi - (eBounds 64).lo < 1 / 2 ^ 64 ∧
    (eBounds 256).hi - (eBounds 256).lo < 1 / 2 ^ 256 := by
  decide +kernel

example : eExtension.enclose? { precision := 64 } [] = some (eBounds 64) := rfl

/-! ## Closed checks with the standard calls -/

/-- The exact backend at `precision` bits, with the standard calls. -/
def standard (precision : Nat) : Backend ℚ :=
  (rational { precision }).withExtensions { precision } Standard.extensions

/-- `standard` is sound for the real functions of the standard calls. -/
theorem standard_sound (precision : Nat) :
    (standard precision).Sound (extensionValues Standard.functions) :=
  withExtensions_sound (rational_sound _) _ Standard.extensions_sound

/-- The closed expression `max (lo - e) (e - hi)`, negative exactly when `lo < e < hi`. -/
def between (lo : ℚ) (e : Expr) (hi : ℚ) : Expr :=
  .binary .max (.binary .sub (.const lo) e) (.binary .sub e (.const hi))

/-- A passing closed check of `between lo e hi` puts the value `x` of `e` between `lo` and
`hi`. -/
theorem lt_and_lt_of_check {e : Expr} {x : ℝ}
    (hx : e.eval (fun _ => 0) (extensionValues Standard.functions) = x)
    {lo hi : ℚ} {precision : Nat}
    (h : (between lo e hi).checkZero (standard precision) .negative [] 0 = true) :
    (lo : ℝ) < x ∧ x < hi := by
  have hholds := Expr.checkZero_sound _ (standard_sound precision) h
    (Box.containsReal_nil fun _ => 0)
  simpa only [between, Relation.Holds, Expr.eval, BinaryOp.eval, hx, max_lt_iff, sub_neg]
    using hholds

example : (3.14157 : ℝ) < Real.pi ∧ Real.pi < 3.14161 := by
  exact_mod_cast lt_and_lt_of_check (e := .call 0 []) rfl (lo := 3.14157) (hi := 3.14161)
    (precision := 16) (by decide +kernel)

example : (3.1415926535897932384 : ℝ) < Real.pi ∧ Real.pi < 3.1415926535897932386 := by
  exact_mod_cast lt_and_lt_of_check (e := .call 0 []) rfl (lo := 3.1415926535897932384)
    (hi := 3.1415926535897932386) (precision := 64) (by decide +kernel)

example :
    (3.1415926535897932384626433832795028841971693993751058209749445923078164062862 : ℝ) <
      Real.pi ∧
    Real.pi < 3.1415926535897932384626433832795028841971693993751058209749445923078164062864 := by
  exact_mod_cast lt_and_lt_of_check (e := .call 0 []) rfl
    (lo := 3.1415926535897932384626433832795028841971693993751058209749445923078164062862)
    (hi := 3.1415926535897932384626433832795028841971693993751058209749445923078164062864)
    (precision := 256) (by decide +kernel)

-- Sixteen bits do not pin `π` down to nineteen decimals.
example : (between 3.1415926535897932384 (.call 0 []) 3.1415926535897932386).checkZero
    (standard 16) .negative [] 0 = false := by
  decide +kernel

example : (1.4142 : ℝ) < 2 ^ (1 / 2 : ℝ) ∧ (2 : ℝ) ^ (1 / 2 : ℝ) < 1.4143 := by
  have hx : (Expr.call 1 [.const 2, .const (1 / 2)]).eval (fun _ => 0)
      (extensionValues Standard.functions) = 2 ^ (1 / 2 : ℝ) := by
    change Real.rpow ((2 : ℚ) : ℝ) ((1 / 2 : ℚ) : ℝ) = _
    norm_num
  exact_mod_cast lt_and_lt_of_check hx (lo := 1.4142) (hi := 1.4143) (precision := 64)
    (by decide +kernel)

example : (2.7182818 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 2.7182819 := by
  exact_mod_cast lt_and_lt_of_check (e := .call 2 []) rfl (lo := 2.7182818) (hi := 2.7182819)
    (precision := 64) (by decide +kernel)

/-! ## Backends without calls -/

example (config : Config) : (rational config).Sound (extensionValues Standard.functions) :=
  (rational_sound config).of_noCalls fun _ _ => rfl

/-! ## The enclosures that `interval` registers -/

/-- The enclosures that `interval` registers, in the order of `StandardProof`. -/
def registered : List Extension :=
  [elementaryExtension .exp, elementaryExtension .log, elementaryExtension .sin,
    elementaryExtension .cos, elementaryExtension .tan, elementaryExtension .asin,
    elementaryExtension .acos, elementaryExtension .atan, elementaryExtension .sinh,
    elementaryExtension .cosh, elementaryExtension .tanh, elementaryExtension .sqrt,
    asinhExtension, acoshExtension, atanhExtension, rpowExtension, logbExtension]

/-- The real functions of `registered`, by the same index. -/
noncomputable def registeredFunctions : List (List ℝ → ℝ) :=
  [RealFunction.apply (n := 1) Real.exp, RealFunction.apply (n := 1) Real.log,
    RealFunction.apply (n := 1) Real.sin, RealFunction.apply (n := 1) Real.cos,
    RealFunction.apply (n := 1) Real.tan, RealFunction.apply (n := 1) Real.arcsin,
    RealFunction.apply (n := 1) Real.arccos, RealFunction.apply (n := 1) Real.arctan,
    RealFunction.apply (n := 1) Real.sinh, RealFunction.apply (n := 1) Real.cosh,
    RealFunction.apply (n := 1) Real.tanh, RealFunction.apply (n := 1) Real.sqrt,
    RealFunction.apply (n := 1) Real.arsinh, RealFunction.apply (n := 1) Real.arcosh,
    RealFunction.apply (n := 1) Real.artanh, RealFunction.apply (n := 2) Real.rpow,
    RealFunction.apply (n := 2) Real.logb]

/-- The containment theorems of `StandardProof` make the two tables agree. -/
theorem registered_sound : ExtensionsSound registered registeredFunctions :=
  extensionsSound_nil |>.cons logb_extension_sound |>.cons rpow_extension_sound
    |>.cons artanh_extension_sound |>.cons arcosh_extension_sound |>.cons arsinh_extension_sound
    |>.cons sqrt_extension_sound |>.cons tanh_extension_sound |>.cons cosh_extension_sound
    |>.cons sinh_extension_sound |>.cons arctan_extension_sound |>.cons arccos_extension_sound
    |>.cons arcsin_extension_sound |>.cons tan_extension_sound |>.cons cos_extension_sound
    |>.cons sin_extension_sound |>.cons log_extension_sound |>.cons exp_extension_sound

/-- A sample input of each enclosure of `registered`, by the same index. -/
def samples : List (List (Interval ℚ)) :=
  [[point 1], [point 2], [point 1], [point 1], [point (1 / 2)], [point (1 / 2)], [point (1 / 2)],
    [point 1], [point 1], [point 1], [point 1], [point 2], [point 1], [point 2], [point (1 / 2)],
    [point 2, point (1 / 2)], [point 2, point 8]]

-- Each registered enclosure accepts its sample input at the default settings, so no theorem of
-- `registered_sound` holds only vacuously.
example : (registered.length == samples.length && (registered.zip samples).all fun (E, inputs) =>
    inputs.length == E.arity && (E.enclose? {} inputs).isSome) = true := by
  decide +kernel

-- `FloatLib.Tactic.Interval.Functions` registers each containment theorem for its function.
open Lean in
run_meta do
  let registrations := Tactic.intervalExtensionRegistry.getState (← getEnv)
  for (function, proof) in [(``Real.exp, ``exp_extension_sound),
      (``Real.log, ``log_extension_sound), (``Real.sin, ``sin_extension_sound),
      (``Real.cos, ``cos_extension_sound), (``Real.tan, ``tan_extension_sound),
      (``Real.arcsin, ``arcsin_extension_sound), (``Real.arccos, ``arccos_extension_sound),
      (``Real.arctan, ``arctan_extension_sound), (``Real.sinh, ``sinh_extension_sound),
      (``Real.cosh, ``cosh_extension_sound), (``Real.tanh, ``tanh_extension_sound),
      (``Real.sqrt, ``sqrt_extension_sound), (``Real.arsinh, ``arsinh_extension_sound),
      (``Real.arcosh, ``arcosh_extension_sound), (``Real.artanh, ``artanh_extension_sound),
      (``Real.rpow, ``rpow_extension_sound), (``Real.logb, ``logb_extension_sound)] do
    unless registrations.find? function == some proof do
      throwError "{function} is not registered with {proof}"

end FloatLibTests.Numerics.Standard
