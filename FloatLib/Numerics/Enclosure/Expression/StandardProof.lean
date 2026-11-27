/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Constants.Proof
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.ExtensionsProof
public import FloatLib.Numerics.Enclosure.Expression.Standard
public import FloatLib.Numerics.Enclosure.Interval.InverseHyperbolicProof
public import FloatLib.Numerics.Enclosure.Interval.PowersProof

/-!
# Containment for the registered enclosures and the standard calls

Each enclosure that the `interval` tactic registers contains the value of its function at every
input it accepts, `exp_extension_sound` to `logb_extension_sound`, and the twelve elementary ones
are `Backend.elementaryExtension_sound` at one operation each. The enclosures of `π` and `e`
contain `π` and `exp 1` (`Backend.piExtension_sound`, `Backend.eExtension_sound`), so the standard
calls are sound as a table (`Standard.extensions_sound`), and `Backend.withExtensions_sound` adds
them to any sound backend. None of this needs a tactic, so code that evaluates expressions with
`Standard.extensions` has these theorems without importing `interval`, and
`FloatLib.Tactic.Interval.Functions` registers them for `interval`.

The enclosure of `π` is narrower than `2 ^ (-precision)` (`Backend.piBounds_width_lt`), since each
degree of Machin's series divides the width by 25. A backend without calls of its own, such as
`Backend.rational`, is sound for every table of call functions once it is sound for one
(`Backend.Sound.of_noCalls`), so it also meets the contract with `Standard.functions`.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Each elementary enclosure, as a registered call, contains every accepted real input's image. -/
theorem Backend.elementaryExtension_sound (op : UnaryOp) :
    (Backend.elementaryExtension op).Sound op.eval :=
  Extension.unary_sound _ _ fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx

/-- The registered `exp` enclosure contains every accepted real input's image. -/
theorem exp_extension_sound : (Backend.elementaryExtension .exp).Sound Real.exp :=
  Backend.elementaryExtension_sound .exp

/-- The registered `log` enclosure contains every accepted real input's image. -/
theorem log_extension_sound : (Backend.elementaryExtension .log).Sound Real.log :=
  Backend.elementaryExtension_sound .log

/-- The registered `sin` enclosure contains every accepted real input's image. -/
theorem sin_extension_sound : (Backend.elementaryExtension .sin).Sound Real.sin :=
  Backend.elementaryExtension_sound .sin

/-- The registered `cos` enclosure contains every accepted real input's image. -/
theorem cos_extension_sound : (Backend.elementaryExtension .cos).Sound Real.cos :=
  Backend.elementaryExtension_sound .cos

/-- The registered `tan` enclosure contains every accepted real input's image. -/
theorem tan_extension_sound : (Backend.elementaryExtension .tan).Sound Real.tan :=
  Backend.elementaryExtension_sound .tan

/-- The registered `arcsin` enclosure contains every accepted real input's image. -/
theorem arcsin_extension_sound : (Backend.elementaryExtension .asin).Sound Real.arcsin :=
  Backend.elementaryExtension_sound .asin

/-- The registered `arccos` enclosure contains every accepted real input's image. -/
theorem arccos_extension_sound : (Backend.elementaryExtension .acos).Sound Real.arccos :=
  Backend.elementaryExtension_sound .acos

/-- The registered `arctan` enclosure contains every accepted real input's image. -/
theorem arctan_extension_sound : (Backend.elementaryExtension .atan).Sound Real.arctan :=
  Backend.elementaryExtension_sound .atan

/-- The registered `sinh` enclosure contains every accepted real input's image. -/
theorem sinh_extension_sound : (Backend.elementaryExtension .sinh).Sound Real.sinh :=
  Backend.elementaryExtension_sound .sinh

/-- The registered `cosh` enclosure contains every accepted real input's image. -/
theorem cosh_extension_sound : (Backend.elementaryExtension .cosh).Sound Real.cosh :=
  Backend.elementaryExtension_sound .cosh

/-- The registered `tanh` enclosure contains every accepted real input's image. -/
theorem tanh_extension_sound : (Backend.elementaryExtension .tanh).Sound Real.tanh :=
  Backend.elementaryExtension_sound .tanh

/-- The registered `sqrt` enclosure contains every accepted real input's image. -/
theorem sqrt_extension_sound : (Backend.elementaryExtension .sqrt).Sound Real.sqrt :=
  Backend.elementaryExtension_sound .sqrt

/-- The registered `arsinh` enclosure contains every accepted real input's image. -/
theorem arsinh_extension_sound : Backend.asinhExtension.Sound Real.arsinh :=
  Extension.unary_sound _ _ (fun _ _ _ _ h hx => containsReal_asinhBounds? h hx)

/-- The registered `arcosh` enclosure contains every accepted real input's image. -/
theorem arcosh_extension_sound : Backend.acoshExtension.Sound Real.arcosh :=
  Extension.unary_sound _ _ (fun _ _ _ _ h hx => containsReal_acoshBounds? h hx)

/-- The registered `artanh` enclosure contains every accepted real input's image. -/
theorem artanh_extension_sound : Backend.atanhExtension.Sound Real.artanh :=
  Extension.unary_sound _ _ (fun _ _ _ _ h hx => containsReal_atanhBounds? h hx)

/-- The registered `rpow` enclosure contains every accepted pair of real inputs. -/
theorem rpow_extension_sound : Backend.rpowExtension.Sound Real.rpow :=
  Extension.binary_sound _ _ (fun _ _ _ _ _ _ h hx hy => containsReal_rpowBounds? h hx hy)

/-- The registered `logb` enclosure contains every accepted pair of real inputs. -/
theorem logb_extension_sound : Backend.logbExtension.Sound Real.logb :=
  Extension.binary_sound _ _ (fun _ _ _ _ _ _ h hx hy => containsReal_logbBounds? h hx hy)

end FloatLib.Numerics.Interval

namespace FloatLib.Numerics.Interval.Backend

/-- `piBounds precision` contains `π`. -/
theorem containsReal_piBounds (precision : Nat) :
    (piBounds precision).ContainsReal some Real.pi := by
  have h := RationalInterval.contains_scaleNonnegative
    (Enclosure.contains_piQuarter (precision / 4 + 1)) (factor := 4) (by norm_num)
  rw [show ((4 : ℚ) : ℝ) * (Real.pi / 4) = Real.pi by push_cast; ring] at h
  exact (containsReal_some_iff _ _).mpr h

/-- The ends of `piBounds precision` are ordered, since `π` lies between them. -/
theorem piBounds_lo_le_hi (precision : Nat) :
    (piBounds precision).lo ≤ (piBounds precision).hi := by
  have h := (containsReal_some_iff _ _).mp (containsReal_piBounds precision)
  exact_mod_cast h.1.trans h.2

/--
`2 ^ precision < 3 * 25 ^ (precision / 4 + 1)`: Machin's series at degree `precision / 4 + 1` is
accurate to `precision` bits.
-/
private theorem two_pow_lt_three_mul_pow (precision : Nat) :
    2 ^ precision < 3 * 25 ^ (precision / 4 + 1) := by
  have hpos : 0 < 25 ^ (precision / 4) := by positivity
  calc 2 ^ precision ≤ 2 ^ (4 * (precision / 4) + 3) :=
        Nat.pow_le_pow_right (by decide) (by omega)
    _ = 16 ^ (precision / 4) * 8 := by rw [pow_add, pow_mul]; norm_num
    _ ≤ 25 ^ (precision / 4) * 8 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)
    _ < 3 * 25 ^ (precision / 4 + 1) := by rw [pow_succ]; omega

/-- The enclosure of `π` is narrower than `2 ^ (-precision)`. -/
theorem piBounds_width_lt (precision : Nat) :
    (piBounds precision).hi - (piBounds precision).lo < 1 / 2 ^ precision := by
  have hwidth := Enclosure.piQuarter_width_le (precision / 4 + 1)
  have hpow : (2 : ℚ) ^ precision < 3 * 25 ^ (precision / 4 + 1) := by
    exact_mod_cast two_pow_lt_three_mul_pow precision
  have hthird : 4 * (1 / (12 * 25 ^ (precision / 4 + 1)) : ℚ) < 1 / 2 ^ precision := by
    rw [show 4 * (1 / (12 * 25 ^ (precision / 4 + 1)) : ℚ) =
      1 / (3 * 25 ^ (precision / 4 + 1)) by ring]
    exact one_div_lt_one_div_of_lt (by positivity) hpow
  simp only [piBounds, RationalInterval.scaleNonnegative_def]
  linarith

/-- The registered enclosure of `π` contains `π` at every setting. -/
theorem piExtension_sound : piExtension.Sound Real.pi :=
  Extension.constant_sound _ _ fun _ _ h => Option.some.inj h ▸ containsReal_piBounds _

/-- `eBounds precision` contains `e = exp 1`. -/
theorem containsReal_eBounds (precision : Nat) :
    (eBounds precision).ContainsReal some (Real.exp 1) := by
  have h := Enclosure.contains_exp 1 (precision / 2 + 1)
  rw [Rat.cast_one] at h
  exact (containsReal_some_iff _ _).mpr h

/-- The registered enclosure of `e` contains `e = exp 1` at every setting. -/
theorem eExtension_sound : eExtension.Sound (Real.exp 1) :=
  Extension.constant_sound _ _ fun _ _ h => Option.some.inj h ▸ containsReal_eBounds _

/--
The real functions of the standard calls, by index: `π` is call `0`, the real power `Real.rpow`
is call `1`, and `e = exp 1` is call `2`, each read as a function of an argument list. Evaluation
of an expression with these calls takes `extensionValues Standard.functions` as its call table.
-/
noncomputable def Standard.functions : List (List ℝ → ℝ) :=
  [RealFunction.apply (n := 0) Real.pi, RealFunction.apply (n := 2) Real.rpow,
    RealFunction.apply (n := 0) (Real.exp 1)]

/--
Each standard call's enclosure contains the value of its real function at every input it
accepts.
-/
theorem Standard.extensions_sound : ExtensionsSound Standard.extensions Standard.functions :=
  ((extensionsSound_nil.cons eExtension_sound).cons rpow_extension_sound).cons piExtension_sound

/--
A backend whose calls all fail is sound for every table of call functions once it is sound for
one: no call succeeds, so the call contract holds whatever the table says.
-/
theorem Sound.of_noCalls {α : Type*} {B : Backend α} {functions functions' : Nat → List ℝ → ℝ}
    (hB : B.Sound functions) (hcall : ∀ index inputs, B.call? index inputs = none) :
    B.Sound functions' where
  const := hB.const
  unary := hB.unary
  binary := hB.binary
  ternary := hB.ternary
  call h := by simp [hcall] at h

end FloatLib.Numerics.Interval.Backend
