/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Candidates
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Multiplication.Proof
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Division.Proof
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Sqrt.Proof
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Fma.Proof

/-!
# Certified wide-limb candidates for the limb carrier

An explicit `StoragePlan.limbs` stores formats wider than 128 bits in limb arrays. Its arithmetic
candidates enter through this carrier and are proved equal to the configured reference operation
through `Model.WideLimb.toModel_add` and its siblings together with the codec laws. Division and
square root use arbitrary-precision integer quotients and roots after reading the stored fields;
the other kernels operate on the limbs themselves. A candidate is offered only when
`Model.WideLimb.Eligible` holds, a decidable test on the descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

variable (format : FloatFormat) (width_gt : 128 < format.bitWidth)

/-- Estimate for a direct limb-carrier entry, including any internal integer conversions. -/
def wideLimbEstimate (operation : Operation) : Candidate :=
  { Descriptor.Plan.wideLimbEstimate format operation with marshallingCost := 0 }

/-- Certified wide-limb addition on the limb carrier. -/
def wideLimbAdd (h : Model.WideLimb.Eligible format) :
    Certified (@Spec.add format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance) :=
  Certified.binary (wideLimbEstimate format .add) Spec.add
    (FloatLib.Floats.ExecFloat.applyBinary (Model.WideLimb.add format))
    fun left right => by
      apply FloatLib.Floats.ExecFloat.ext
      change Model.WideLimb.add format left.raw right.raw =
        Model.WideLimb.ofModel
          (Model.Spec.add (Model.WideLimb.toModel left.raw) (Model.WideLimb.toModel right.raw))
      rw [← Model.WideLimb.toModel_add h, Model.WideLimb.ofModel_toModel]

/-- Certified wide-limb subtraction on the limb carrier. -/
def wideLimbSub (h : Model.WideLimb.Eligible format) :
    Certified (@Spec.sub format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance) :=
  Certified.binary (wideLimbEstimate format .sub) Spec.sub
    (FloatLib.Floats.ExecFloat.applyBinary (Model.WideLimb.sub format))
    fun left right => by
      apply FloatLib.Floats.ExecFloat.ext
      change Model.WideLimb.sub format left.raw right.raw =
        Model.WideLimb.ofModel
          (Model.Spec.sub (Model.WideLimb.toModel left.raw) (Model.WideLimb.toModel right.raw))
      rw [← Model.WideLimb.toModel_sub h, Model.WideLimb.ofModel_toModel]

/-- Certified wide-limb multiplication on the limb carrier. -/
def wideLimbMul (h : Model.WideLimb.Eligible format) :
    Certified (@Spec.mul format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance) :=
  Certified.binary (wideLimbEstimate format .mul) Spec.mul
    (FloatLib.Floats.ExecFloat.applyBinary (Model.WideLimb.mul format))
    fun left right => by
      apply FloatLib.Floats.ExecFloat.ext
      change Model.WideLimb.mul format left.raw right.raw =
        Model.WideLimb.ofModel
          (Model.Spec.mul (Model.WideLimb.toModel left.raw) (Model.WideLimb.toModel right.raw))
      rw [← Model.WideLimb.toModel_mul h, Model.WideLimb.ofModel_toModel]

/-- Certified wide-limb division on the limb carrier. -/
def wideLimbDiv (h : Model.WideLimb.Eligible format) :
    Certified (@Spec.div format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance) :=
  Certified.binary (wideLimbEstimate format .div) Spec.div
    (FloatLib.Floats.ExecFloat.applyBinary (Model.WideLimb.div format))
    fun left right => by
      apply FloatLib.Floats.ExecFloat.ext
      change Model.WideLimb.div format left.raw right.raw =
        Model.WideLimb.ofModel
          (Model.Spec.div (Model.WideLimb.toModel left.raw) (Model.WideLimb.toModel right.raw))
      rw [← Model.WideLimb.toModel_div h, Model.WideLimb.ofModel_toModel]

/-- Certified wide-limb square root on the limb carrier. -/
def wideLimbSqrt (h : Model.WideLimb.Eligible format) :
    Certified (@Spec.sqrt format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance) :=
  Certified.unary (wideLimbEstimate format .sqrt) Spec.sqrt
    (FloatLib.Floats.ExecFloat.applyUnary (Model.WideLimb.sqrt format))
    fun value => by
      apply FloatLib.Floats.ExecFloat.ext
      change Model.WideLimb.sqrt format value.raw =
        Model.WideLimb.ofModel (Model.Spec.sqrt (Model.WideLimb.toModel value.raw))
      rw [← Model.WideLimb.toModel_sqrt h, Model.WideLimb.ofModel_toModel]

/-- Certified wide-limb fused multiply-add on the limb carrier. -/
def wideLimbFma (h : Model.WideLimb.Eligible format) :
    Certified (@Spec.fma format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance) :=
  Certified.ternary (wideLimbEstimate format .fma) Spec.fma
    (FloatLib.Floats.ExecFloat.applyTernary (Model.WideLimb.fma format))
    fun left right addend => by
      apply FloatLib.Floats.ExecFloat.ext
      change Model.WideLimb.fma format left.raw right.raw addend.raw =
        Model.WideLimb.ofModel
          (Model.Spec.fma (Model.WideLimb.toModel left.raw) (Model.WideLimb.toModel right.raw)
            (Model.WideLimb.toModel addend.raw))
      rw [← Model.WideLimb.toModel_fma h, Model.WideLimb.ofModel_toModel]

/-- Offer wide-limb addition exactly when the descriptor is eligible. -/
def wideLimbAdd? :
    Option (Certified (@Spec.add format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance)) :=
  if h : Model.WideLimb.Eligible format then some (wideLimbAdd format width_gt h) else none

/-- Offer wide-limb subtraction exactly when the descriptor is eligible. -/
def wideLimbSub? :
    Option (Certified (@Spec.sub format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance)) :=
  if h : Model.WideLimb.Eligible format then some (wideLimbSub format width_gt h) else none

/-- Offer wide-limb multiplication exactly when the descriptor is eligible. -/
def wideLimbMul? :
    Option (Certified (@Spec.mul format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance)) :=
  if h : Model.WideLimb.Eligible format then some (wideLimbMul format width_gt h) else none

/-- Offer wide-limb division exactly when the descriptor is eligible. -/
def wideLimbDiv? :
    Option (Certified (@Spec.div format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance)) :=
  if h : Model.WideLimb.Eligible format then some (wideLimbDiv format width_gt h) else none

/-- Offer wide-limb square root exactly when the descriptor is eligible. -/
def wideLimbSqrt? :
    Option (Certified (@Spec.sqrt format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance)) :=
  if h : Model.WideLimb.Eligible format then some (wideLimbSqrt format width_gt h) else none

/-- Offer wide-limb fused multiply-add exactly when the descriptor is eligible. -/
def wideLimbFma? :
    Option (Certified (@Spec.fma format (.limbs width_gt) (Code (.limbs width_gt)) inferInstance)) :=
  if h : Model.WideLimb.Eligible format then some (wideLimbFma format width_gt h) else none

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
