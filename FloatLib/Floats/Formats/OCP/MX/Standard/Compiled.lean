/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.ElementKernel
public import FloatLib.Tactic.CompilerOptimize

/-!
# Compiled MX element conversion

OCP MX v1.0, §§5.3 and 6.3: finite nearest-even element conversion with saturation.
The same proved bisection used by the kernel replaces the exhaustive candidate search
in compiled code. One wrapper covers all six profiles and every signed rational input.
The exceptional-input and FP8 overflow branches remain those of `Element.quantize`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics FloatLib.Floats.ExecFloat

/-- OCP MX v1.0, §5.3: the stored finite element selected by the existing bisection. -/
def Compiled.quantizeFinite (profile : Profile) (input : SignedRat) : Element profile :=
  let sp := (decide (input.value.num < 0)).toNat
  let neg := input.negative.toNat
  let ap := input.value.num.natAbs
  let q := input.value.den
  BitVec.ofNat profile.width <|
    if twosComplement profile then int8Nearest sp neg ap q else nearest profile sp neg ap q

/-- The compiled bisection equals the finite argmin specification for every profile and input. -/
theorem Compiled.quantizeFinite_eq (profile : Profile) (input : SignedRat) :
    Compiled.quantizeFinite profile input = Element.quantizeFinite profile input := by
  rw [quantizeFinite_eq_round]
  unfold Compiled.quantizeFinite roundCode
  cases h : twosComplement profile
  · simp only [Bool.false_eq_true, ↓reduceIte, nearestAll_eq profile h]
  · have hp : profile = .int8 := by cases profile <;> first | rfl | cases h
    subst profile
    simp only [↓reduceIte, nearestAll_int8]

/-- OCP MX v1.0, §5.3: certified compiled bisection, with the argmin as specification. -/
@[compiler_optimize direct]
def Compiled.finite (profile : Profile) : Backend.Certified (Element.quantizeFinite profile) :=
  .unary { name := "MX element bisection", kind := .generic, steadyCost := 1 }
    (Element.quantizeFinite profile) (Compiled.quantizeFinite profile)
    (Compiled.quantizeFinite_eq profile)

/-- Direct calls to finite conversion compile to the proved bisection after this import. -/
@[csimp] theorem quantizeFinite_eq_compiled : @quantizeFinite = @Compiled.quantizeFinite := by
  funext profile input
  exact (Compiled.quantizeFinite_eq profile input).symm

/-- OCP MX v1.0, §5.3: the shared exceptional dispatcher with compiled finite bisection. -/
def Compiled.quantize (profile : Profile) (value : NumericalValue SignedRat)
    (overflow : OverflowMode := .saturate) : Element profile :=
  quantizeWith profile (Compiled.quantizeFinite profile) value overflow

/-- Bisection preserves the complete converter, including exceptional inputs and overflow policy. -/
theorem Compiled.quantize_eq (profile : Profile) (value : NumericalValue SignedRat)
    (overflow : OverflowMode) :
    Compiled.quantize profile value overflow = Element.quantize profile value overflow := by
  unfold Compiled.quantize Element.quantize
  rw [← quantizeFinite_eq_compiled]

/-- OCP MX v1.0, §5.3: certified converter for both FP8 overflow policies and all inputs. -/
@[compiler_optimize direct]
def Compiled.conversion (profile : Profile) : Backend.Certified (@Element.quantize profile) :=
  .binary { name := "MX conversion bisection", kind := .generic, steadyCost := 1 }
    (@Element.quantize profile) (@Compiled.quantize profile) (Compiled.quantize_eq profile)

/-- Calls from codecs compiled after this import use the proved scalar dispatcher. -/
@[csimp] theorem quantize_eq_compiled : @quantize = @Compiled.quantize := by
  funext profile value overflow
  exact (Compiled.quantize_eq profile value overflow).symm

end FloatLib.Floats.Formats.OCP.MX.Standard.Element
