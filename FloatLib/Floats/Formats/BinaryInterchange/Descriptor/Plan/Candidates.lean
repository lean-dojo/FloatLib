/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Routes
public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Table
public import FloatLib.Floats.ExecFloat.Backends.Selection.Certified

/-!
# Certified execution candidates for arbitrary binary descriptors

Every binary `FloatFormat` has a proof-carrying candidate plan for addition, subtraction,
multiplication, division, square root, and fused multiply-add. The public `ExecFloat` dispatcher
makes the only selection:

* every format of at most eight encoded bits can use a lazily generated exhaustive table;
* each operation exposes at most one structural route, classified as fixed-format, native-word,
  or fixed-limb in exactly the same order as its executable dispatcher;
* every descriptor retains a proved width-generic baseline.

Every candidate is selected from descriptor data through the same structural predicates used by
runtime dispatch. Layout-specific kernels remain specialized, but no plan depends on descriptor
identity or a catalogued format name. A new IEEE, finite-only, FNUZ, or otherwise custom descriptor
receives table and structural candidates when eligible, together with the generic baseline.

Cost estimates live in `Descriptor.Plan.Estimates`; this module is responsible for candidate
availability and proof-carrying construction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-! ## Generic certified constructors -/

theorem toNatBits_lt_256_of_bitWidth_le
    {format : FloatFormat} (hwidth : format.bitWidth ≤ 8)
    (value : Model format) :
    value.toNatBits < 256 := by
  calc
    value.toNatBits < 2 ^ format.bitWidth :=
      Model.toNatBits_lt_two_pow value
    _ ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hwidth
    _ = 256 := by decide

/-! ## Descriptor-generic exhaustive tables -/

/-- Build a certified exhaustive binary table for a descriptor of at most eight bits. -/
def binaryTableCertified
    {format : FloatFormat}
    (operation : Operation)
    (modelSpec modelRun : Model format → Model format → Model format)
    (modelRun_eq_spec : ∀ left right, modelRun left right = modelSpec left right)
    (hwidth : format.bitWidth ≤ 8) :
    Certified
      (ModelCodec.liftBinary
        (F := Descriptor format) (plan := ()) modelSpec) :=
  let radix := 2 ^ format.bitWidth
  let table := Model.TinyTable.lazyBinaryTotal format radix modelRun
  let runModel := fun left right =>
    Model.TinyTable.runLazyBinaryTotal
      format radix modelRun table (by rfl) left right
      (Model.toNatBits_lt_two_pow left)
      (Model.toNatBits_lt_two_pow right)
  Certified.binary
    (tableEstimate format operation)
    (ModelCodec.liftBinary
      (F := Descriptor format) (plan := ()) modelSpec)
    (ModelCodec.liftBinary
      (F := Descriptor format) (plan := ()) runModel)
    fun left right => by
      apply FloatLib.Floats.ExecFloat.ext
      change runModel left.raw right.raw = modelSpec left.raw right.raw
      calc
        runModel left.raw right.raw = modelRun left.raw right.raw := by
          exact Model.TinyTable.runLazyBinaryTotal_eq
            format radix (by positivity) modelRun table (by rfl)
            left.raw right.raw
            (Model.toNatBits_lt_two_pow left.raw)
            (Model.toNatBits_lt_two_pow right.raw)
            (toNatBits_lt_256_of_bitWidth_le hwidth _)
        _ = modelSpec left.raw right.raw :=
          modelRun_eq_spec left.raw right.raw

/-- Build a certified exhaustive unary table for a descriptor of at most eight bits. -/
def unaryTableCertified
    {format : FloatFormat}
    (operation : Operation)
    (modelSpec modelRun : Model format → Model format)
    (modelRun_eq_spec : ∀ value, modelRun value = modelSpec value)
    (hwidth : format.bitWidth ≤ 8) :
    Certified
      (ModelCodec.liftUnary
        (F := Descriptor format) (plan := ()) modelSpec) :=
  let radix := 2 ^ format.bitWidth
  let table := Model.TinyTable.lazyUnaryTotal format radix modelRun
  let runModel := fun value =>
    Model.TinyTable.runLazyUnaryTotal
      format radix modelRun table (by rfl) value
      (Model.toNatBits_lt_two_pow value)
  Certified.unary
    (tableEstimate format operation)
    (ModelCodec.liftUnary
      (F := Descriptor format) (plan := ()) modelSpec)
    (ModelCodec.liftUnary
      (F := Descriptor format) (plan := ()) runModel)
    fun value => by
      apply FloatLib.Floats.ExecFloat.ext
      change runModel value.raw = modelSpec value.raw
      calc
        runModel value.raw = modelRun value.raw := by
          exact Model.TinyTable.runLazyUnaryTotal_eq
            format radix modelRun table (by rfl) value.raw
            (Model.toNatBits_lt_two_pow value.raw)
            (toNatBits_lt_256_of_bitWidth_le hwidth _)
        _ = modelSpec value.raw := modelRun_eq_spec value.raw

/-- Build a certified exhaustive ternary table for a descriptor of at most eight bits. -/
def ternaryTableCertified
    {format : FloatFormat}
    (operation : Operation)
    (modelSpec modelRun :
      Model format → Model format → Model format → Model format)
    (modelRun_eq_spec :
      ∀ left right addend,
        modelRun left right addend = modelSpec left right addend)
    (hwidth : format.bitWidth ≤ 8) :
    Certified
      (ModelCodec.liftTernary
        (F := Descriptor format) (plan := ()) modelSpec) :=
  let radix := 2 ^ format.bitWidth
  let table := Model.TinyTable.lazyTernaryTotal format radix modelRun
  let runModel := fun left right addend =>
    Model.TinyTable.runLazyTernaryTotal
      format radix modelRun table (by rfl) left right addend
      (Model.toNatBits_lt_two_pow left)
      (Model.toNatBits_lt_two_pow right)
      (Model.toNatBits_lt_two_pow addend)
  Certified.ternary
    (tableEstimate format operation)
    (ModelCodec.liftTernary
      (F := Descriptor format) (plan := ()) modelSpec)
    (ModelCodec.liftTernary
      (F := Descriptor format) (plan := ()) runModel)
    fun left right addend => by
      apply FloatLib.Floats.ExecFloat.ext
      change runModel left.raw right.raw addend.raw =
        modelSpec left.raw right.raw addend.raw
      calc
        runModel left.raw right.raw addend.raw =
            modelRun left.raw right.raw addend.raw := by
          exact Model.TinyTable.runLazyTernaryTotal_eq
            format radix (by positivity) modelRun table (by rfl)
            left.raw right.raw addend.raw
            (Model.toNatBits_lt_two_pow left.raw)
            (Model.toNatBits_lt_two_pow right.raw)
            (Model.toNatBits_lt_two_pow addend.raw)
            (toNatBits_lt_256_of_bitWidth_le hwidth _)
        _ = modelSpec left.raw right.raw addend.raw :=
          modelRun_eq_spec left.raw right.raw addend.raw

/-! ## Candidate availability -/

/-- Offer an exhaustive binary table exactly when the encoded width fits in one byte. -/
def tableBinary? {format : FloatFormat}
    (operation : Operation)
    (modelSpec modelRun : Model format → Model format → Model format)
    (modelRun_eq_spec : ∀ left right, modelRun left right = modelSpec left right) :
    Option
      (Certified
        (ModelCodec.liftBinary
          (F := Descriptor format) (plan := ()) modelSpec)) :=
  if hwidth : format.bitWidth ≤ 8 then
    some (binaryTableCertified operation modelSpec modelRun modelRun_eq_spec hwidth)
  else
    none

/-- Offer an exhaustive unary table exactly when the encoded width fits in one byte. -/
def tableUnary? {format : FloatFormat}
    (operation : Operation)
    (modelSpec modelRun : Model format → Model format)
    (modelRun_eq_spec : ∀ value, modelRun value = modelSpec value) :
    Option
      (Certified
        (ModelCodec.liftUnary
          (F := Descriptor format) (plan := ()) modelSpec)) :=
  if hwidth : format.bitWidth ≤ 8 then
    some (unaryTableCertified operation modelSpec modelRun modelRun_eq_spec hwidth)
  else
    none

/-- Offer an exhaustive ternary table exactly when the encoded width fits in one byte. -/
def tableTernary? {format : FloatFormat}
    (operation : Operation)
    (modelSpec modelRun :
      Model format → Model format → Model format → Model format)
    (modelRun_eq_spec :
      ∀ left right addend,
        modelRun left right addend = modelSpec left right addend) :
    Option
      (Certified
        (ModelCodec.liftTernary
          (F := Descriptor format) (plan := ()) modelSpec)) :=
  if hwidth : format.bitWidth ≤ 8 then
    some (ternaryTableCertified operation modelSpec modelRun modelRun_eq_spec hwidth)
  else
    none

/-! ## Complete per-operation plans -/

/-- Certified addition candidates derived from descriptor structure. -/
def addCandidates (format : FloatFormat) :
    CandidateSet (Certified (@Descriptor.Spec.add format)) where
  alternatives :=
    (show List (Certified (@Descriptor.Spec.add format)) from
      (tableBinary? .add Model.Spec.add Model.AddBackend.generic
        Model.AddBackend.generic_eq_spec).toList) ++
    (structuralRoute? format .add).toList.map (fun route =>
      Certified.binary (route.estimate format .add)
        Descriptor.Spec.add Descriptor.Backend.wordAdd
        Descriptor.Backend.wordAdd_eq_spec)
  baseline :=
    Certified.binary (genericEstimate format .add)
      Descriptor.Spec.add Descriptor.Backend.genericAdd
      Descriptor.Backend.genericAdd_eq_spec

/-- Certified subtraction candidates derived from descriptor structure. -/
def subCandidates (format : FloatFormat) :
    CandidateSet (Certified (@Descriptor.Spec.sub format)) where
  alternatives :=
    (show List (Certified (@Descriptor.Spec.sub format)) from
      (tableBinary? .sub Model.Spec.sub
        (fun left right => Model.AddBackend.generic left (Model.neg right))
        (fun left right => by
          simpa [Model.Spec.sub] using
            Model.AddBackend.generic_eq_spec left (Model.neg right))).toList) ++
    (structuralRoute? format .sub).toList.map (fun route =>
      Certified.binary (route.estimate format .sub)
        Descriptor.Spec.sub Descriptor.Backend.wordSub
        Descriptor.Backend.wordSub_eq_spec)
  baseline :=
    Certified.binary (genericEstimate format .sub)
      Descriptor.Spec.sub Descriptor.Backend.genericSub
      Descriptor.Backend.genericSub_eq_spec

/-- Certified multiplication candidates derived from descriptor structure. -/
def mulCandidates (format : FloatFormat) :
    CandidateSet (Certified (@Descriptor.Spec.mul format)) where
  alternatives :=
    (show List (Certified (@Descriptor.Spec.mul format)) from
      (tableBinary? .mul Model.Spec.mul Model.MulBackend.generic
        Model.MulBackend.generic_eq_spec).toList) ++
    (structuralRoute? format .mul).toList.map (fun route =>
      Certified.binary (route.estimate format .mul)
        Descriptor.Spec.mul Descriptor.Backend.wordMul
        Descriptor.Backend.wordMul_eq_spec)
  baseline :=
    Certified.binary (genericEstimate format .mul)
      Descriptor.Spec.mul Descriptor.Backend.genericMul
      Descriptor.Backend.genericMul_eq_spec

/-- Certified division candidates derived from descriptor structure. -/
def divCandidates (format : FloatFormat) :
    CandidateSet (Certified (@Descriptor.Spec.div format)) where
  alternatives :=
    (show List (Certified (@Descriptor.Spec.div format)) from
      (tableBinary? .div Model.Spec.div Model.DivBackend.generic
        Model.DivBackend.generic_eq_spec).toList) ++
    (structuralRoute? format .div).toList.map (fun route =>
      Certified.binary (route.estimate format .div)
        Descriptor.Spec.div Descriptor.Backend.wordDiv
        Descriptor.Backend.wordDiv_eq_spec)
  baseline :=
    Certified.binary (genericEstimate format .div)
      Descriptor.Spec.div Descriptor.Backend.genericDiv
      Descriptor.Backend.genericDiv_eq_spec

/-- Certified square-root candidates derived from descriptor structure. -/
def sqrtCandidates (format : FloatFormat) :
    CandidateSet (Certified (@Descriptor.Spec.sqrt format)) where
  alternatives :=
    (show List (Certified (@Descriptor.Spec.sqrt format)) from
      (tableUnary? .sqrt Model.Spec.sqrt Model.SqrtBackend.generic
        Model.SqrtBackend.generic_eq_spec).toList) ++
    (structuralRoute? format .sqrt).toList.map (fun route =>
      match route with
      | .fixedLimbs =>
          Certified.unary (route.estimate format .sqrt)
            Descriptor.Spec.sqrt Descriptor.Backend.fixedLimbSqrt
            Descriptor.Backend.fixedLimbSqrt_eq_spec
      | .fixedFormat | .nativeWord =>
          Certified.unary (route.estimate format .sqrt)
            Descriptor.Spec.sqrt Descriptor.Backend.wordSqrt
            Descriptor.Backend.wordSqrt_eq_spec)
  baseline :=
    Certified.unary (genericEstimate format .sqrt)
      Descriptor.Spec.sqrt Descriptor.Backend.genericSqrt
      Descriptor.Backend.genericSqrt_eq_spec

/-- Certified fused-multiply-add candidates derived from descriptor structure. -/
def fmaCandidates (format : FloatFormat) :
    CandidateSet (Certified (@Descriptor.Spec.fma format)) where
  alternatives :=
    (show List (Certified (@Descriptor.Spec.fma format)) from
      (tableTernary? .fma Model.Spec.fma Model.FmaBackend.generic
        Model.FmaBackend.generic_eq_spec).toList) ++
    (structuralRoute? format .fma).toList.map (fun route =>
      match route with
      | .fixedLimbs =>
          Certified.ternary (route.estimate format .fma)
            Descriptor.Spec.fma Descriptor.Backend.fixedLimbFma
            Descriptor.Backend.fixedLimbFma_eq_spec
      | .fixedFormat | .nativeWord =>
          Certified.ternary (route.estimate format .fma)
            Descriptor.Spec.fma Descriptor.Backend.wordFma
            Descriptor.Backend.wordFma_eq_spec)
  baseline :=
    Certified.ternary (genericEstimate format .fma)
      Descriptor.Spec.fma Descriptor.Backend.genericFma
      Descriptor.Backend.genericFma_eq_spec

end FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan
