/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Interval.Registry
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Interval.InverseHyperbolicProof
public import FloatLib.Numerics.Enclosure.Interval.PowersProof

/-!
# Registered elementary functions

The standard elementary functions use the same enclosure registration as user-defined operations.
Their procedures and containment proofs reuse the existing endpoint-independent backend contracts.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- The registered `exp` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem exp_extension_sound : (Backend.elementaryExtension .exp).Sound Real.exp :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `log` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem log_extension_sound : (Backend.elementaryExtension .log).Sound Real.log :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `sin` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem sin_extension_sound : (Backend.elementaryExtension .sin).Sound Real.sin :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `cos` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem cos_extension_sound : (Backend.elementaryExtension .cos).Sound Real.cos :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `tan` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem tan_extension_sound : (Backend.elementaryExtension .tan).Sound Real.tan :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `arcsin` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem arcsin_extension_sound : (Backend.elementaryExtension .asin).Sound Real.arcsin :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `arccos` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem arccos_extension_sound : (Backend.elementaryExtension .acos).Sound Real.arccos :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `arctan` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem arctan_extension_sound : (Backend.elementaryExtension .atan).Sound Real.arctan :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `sinh` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem sinh_extension_sound : (Backend.elementaryExtension .sinh).Sound Real.sinh :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `cosh` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem cosh_extension_sound : (Backend.elementaryExtension .cosh).Sound Real.cosh :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `tanh` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem tanh_extension_sound : (Backend.elementaryExtension .tanh).Sound Real.tanh :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `sqrt` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem sqrt_extension_sound : (Backend.elementaryExtension .sqrt).Sound Real.sqrt :=
  Extension.unary_sound _ _ (fun config _ _ _ h hx =>
    Backend.containsReal_elementaryBounds? config h hx)

/-- The registered `arsinh` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem arsinh_extension_sound : Backend.asinhExtension.Sound Real.arsinh :=
  Extension.unary_sound _ _ (fun _ _ _ _ h hx => containsReal_asinhBounds? h hx)

/-- The registered `arcosh` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem arcosh_extension_sound : Backend.acoshExtension.Sound Real.arcosh :=
  Extension.unary_sound _ _ (fun _ _ _ _ h hx => containsReal_acoshBounds? h hx)

/-- The registered `artanh` enclosure contains every accepted real input's image. -/
@[interval_extension]
theorem artanh_extension_sound : Backend.atanhExtension.Sound Real.artanh :=
  Extension.unary_sound _ _ (fun _ _ _ _ h hx => containsReal_atanhBounds? h hx)

/-- The registered `rpow` enclosure contains every accepted pair of real inputs. -/
@[interval_extension]
theorem rpow_extension_sound : Backend.rpowExtension.Sound Real.rpow :=
  Extension.binary_sound _ _ (fun _ _ _ _ _ _ h hx hy => containsReal_rpowBounds? h hx hy)

/-- The registered `logb` enclosure contains every accepted pair of real inputs. -/
@[interval_extension]
theorem logb_extension_sound : Backend.logbExtension.Sound Real.logb :=
  Extension.binary_sound _ _ (fun _ _ _ _ _ _ h hx hy => containsReal_logbBounds? h hx hy)

end FloatLib.Numerics.Interval
