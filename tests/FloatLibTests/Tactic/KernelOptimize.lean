/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.CompilerBackends
public meta import FloatLib.Tactic.KernelRules
public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.FixedPoint
public import FloatLib.Floats.Formats.OCP.FP8.E4M3
public import FloatLib.Tactic.FloatDecide
public import FloatLib.Tactic.ReplacementProof
public import FloatLib.Tactic.ReferencePaths

/-!
# Backend tags

`@[kernel_optimize]` and `@[compiler_optimize]` register an implementation together with its
proof. These tests check, for each tag,

* that a newly tagged implementation is used without any change to the family or the tactic:
  the cheapest kernel rule rewrites the goal of `float_decide`, and the planner selects a newly
  tagged compiled candidate that is cheaper than the baseline;
* that a candidate tagged for one format is not offered to another;
* that a format with a static form (binary32, a one-byte family) keeps it until a tagged
  candidate applies, and then runs the planner's choice, and that a candidate which declines a
  format can say so with a `NoAlternative` instance, which gives the format its static
  capability back;
* that a wrong or unproved implementation cannot be tagged, with the message that says why: a
  definition without a proof, a statement that is not an equation, an unfinished proof, a term
  that is not a certified implementation, and a candidate with an argument that the format
  does not determine.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Execution.BackendTags

universe u

open FloatLib.Floats
open FloatLib.Floats.ExecFloat

/-! ## Kernel rules -/

/-- A reference operation with no kernel implementation yet. -/
def reference (a b : Nat) : Nat := a + b

/-- A first implementation. -/
def first (a b : Nat) : Nat := b + a

/-- A second, cheaper implementation. -/
def second (a b : Nat) : Nat := Nat.add a b

/-- The first implementation, registered with its proof and a declared cost. -/
@[kernel_optimize (cost := 80)]
theorem reference_eq_first (a b : Nat) : reference a b = first a b :=
  Nat.add_comm a b

/-- With one rule, the rewrite uses it. -/
example : reference 2 3 = 5 := by
  simp only [kernel_optimize]
  guard_target = first 2 3 = 5
  rfl

/-- A cheaper implementation, tagged later. -/
@[kernel_optimize (cost := 50)]
theorem reference_eq_second (a b : Nat) : reference a b = second a b :=
  rfl

/-- The cheaper rule is now the one that rewrites, with no change to the first rule. -/
example : reference 2 3 = 5 := by
  simp only [kernel_optimize]
  guard_target = second 2 3 = 5
  rfl

/-- `float_decide` rewrites with the tagged rules and decides. -/
example : reference 2 3 = 5 := by
  float_decide

/-- A rule without a declared cost ranks after every rule with one. -/
@[kernel_optimize]
theorem reference_eq_first' (a b : Nat) : reference a b = first a b :=
  Nat.add_comm a b

example : reference 2 3 = 5 := by
  simp only [kernel_optimize]
  guard_target = second 2 3 = 5
  rfl

/--
info: FloatLibTests.Conformance.Execution.BackendTags.reference: reference_eq_second, 50 µs
FloatLibTests.Conformance.Execution.BackendTags.reference: reference_eq_first, 80 µs
FloatLibTests.Conformance.Execution.BackendTags.reference: reference_eq_first', no declared cost
-/
#guard_msgs in
#kernel_rules reference

/-- A selector that `float_decide` unfolds to reach the operation inside. -/
@[kernel_optimize unfold]
def selector (swap : Bool) (a b : Nat) : Nat :=
  if swap then reference b a else reference a b

example : selector true 2 3 = 5 := by
  float_decide

/-- A wrong implementation: it has no proof, so only the definition could be tagged. -/
def wrong (a b : Nat) : Nat := a * b

/--
error: `@[kernel_optimize]` cannot register `wrong`: it is a definition, not a proof. Tag the theorem that proves the implementation equal to the reference operation, which is what registers it. (A definition that only selects among operations can be unfolded by `float_decide` with `@[kernel_optimize unfold]`.)
-/
#guard_msgs in
attribute [kernel_optimize] wrong

/-!
A proof must be complete: the declaration and everything it uses may depend on `propext`,
`Classical.choice` and `Quot.sound` only. An unfinished proof depends on Lean's placeholder
axiom, and both tags refuse it through the shared check `Provenance.requireProved`. The repository's
source scan forbids a placeholder in a source file, so the check runs here on the placeholder
axiom itself, named by a string.
-/

/-- Run the proof check of the tag `tag` on the declaration `name`. -/
local elab "#check_proved " tag:str name:str : command =>
  Lean.Elab.Command.liftCoreM <|
    FloatLib.Numerics.Provenance.requireProved tag.getString.toName
      name.getString.toName

/--
error: `@[kernel_optimize]` cannot register `sorryAx`: its proof contains `sorry`. A backend is registered only with a complete proof that it equals the reference operation (no axiom beyond `propext`, `Classical.choice` and `Quot.sound`).
-/
#guard_msgs in
#check_proved "kernel_optimize" "sorryAx"

/-- A true statement that is not an equation between a reference and an implementation. -/
theorem reference_le (a b : Nat) : reference a b ≤ a + b :=
  Nat.le_refl _

/--
error: `@[kernel_optimize]` cannot register `reference_le`: its statement is not an equation `reference = implementation` (or an `↔`, or a conjunction of them).
-/
#guard_msgs in
attribute [kernel_optimize] reference_le

/-- The refused declarations left no rule behind. -/
example : reference 2 3 = 5 := by
  simp only [kernel_optimize]
  guard_target = second 2 3 = 5
  rfl

/-- Another reference operation, with an implementation stated the other way round. -/
def product (a b : Nat) : Nat := a * b

/-- A kernel implementation of `product`. -/
def productKernel (a b : Nat) : Nat := Nat.mul a b

/-- The equation as a kernel library states it: the implementation on the left. -/
@[kernel_optimize ← (cost := 3)]
theorem productKernel_eq (a b : Nat) : productKernel a b = product a b :=
  rfl

/-- The rule rewrites from right to left, with no mirrored theorem. -/
example : product 2 3 = 6 := by
  simp only [kernel_optimize]
  guard_target = productKernel 2 3 = 6
  rfl

/--
info: FloatLibTests.Conformance.Execution.BackendTags.product: productKernel_eq, 3 µs (←)
-/
#guard_msgs in
#kernel_rules product

/--
error: `@[kernel_optimize ←]` is for a theorem `implementation = reference`; `wrong` is a definition
-/
#guard_msgs in
attribute [kernel_optimize ←] wrong

/-- Erasing a rule removes it from the rewrite set and from the registry. -/
example : True := trivial
section Erased
attribute [-kernel_optimize] productKernel_eq

example : product 2 3 = 6 := by
  fail_if_success simp only [kernel_optimize]
  rfl

end Erased

/-! ## Compiled candidates -/

/-- A decimal fixed-point type with two fractional digits. -/
abbrev Cents := ExecFloat.FixedPoint FloatLib.Numerics.decimalRadix 2

/-- A binary fixed-point type with eight fractional digits. -/
abbrev Q8 := ExecFloat.FixedPoint FloatLib.Numerics.binaryRadix 8

/--
The steady cost of the addition candidate that the planner selects for a fixed-point type. It is
a macro, so that each use asks for the capability again and sees the candidates tagged so far: a
definition would keep the capability that instance search found where it was written.
-/
local macro "selectedAdd% " radix:term:max digits:term:max : term =>
  `((ExecFloat.Add.selectedCandidate (F := FixedPoint.Family $radix $digits)).steadyCost)

/-- Before any alternative is tagged, the family's baseline runs (steady cost 2). -/
example : selectedAdd% FloatLib.Numerics.decimalRadix 2 = 2 := by
  decide +kernel

/-- A second addition kernel: the operands in the other order. -/
def swappedAdd {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x y : ExecFloat.FixedPoint radix digits) : ExecFloat.FixedPoint radix digits :=
  FixedPoint.add y x

/-- The second kernel computes the reference addition. -/
theorem swappedAdd_eq {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x y : ExecFloat.FixedPoint radix digits) : swappedAdd x y = FixedPoint.add x y := by
  unfold swappedAdd FixedPoint.add Formats.FixedPoint.Code.add
  simp [Int.add_comm]

/-- An estimate with one cost. -/
def estimate (name : String) (steadyCost : Nat) : Backend.Candidate :=
  { name, kind := .custom "test kernel" 0, steadyCost }

/-- An expensive candidate for every fixed-point format: registered, not selected. -/
@[compiler_optimize]
def expensive {radix : FloatLib.Numerics.Radix} {digits : Nat} :
    Backend.Certified (FixedPoint.add (radix := radix) (fractionalDigits := digits)) :=
  Backend.Certified.binary (estimate "expensive" 1000) FixedPoint.add swappedAdd swappedAdd_eq

example : selectedAdd% FloatLib.Numerics.decimalRadix 2 = 2 := by
  decide +kernel

/-- A cheap candidate for the decimal formats only: it declines every other radix. -/
@[compiler_optimize]
def cheapDecimal {radix : FloatLib.Numerics.Radix} {digits : Nat} :
    Option (Backend.Certified (FixedPoint.add (radix := radix) (fractionalDigits := digits))) :=
  if radix.base = 10 then
    some (Backend.Certified.binary (estimate "cheap decimal" 1) FixedPoint.add swappedAdd
      swappedAdd_eq)
  else none

/-- The planner selects the new candidate where it applies, with no edit to the family. -/
example : selectedAdd% FloatLib.Numerics.decimalRadix 2 = 1 := by
  decide +kernel

/-- A format that the candidate declines keeps its baseline. -/
example : selectedAdd% FloatLib.Numerics.binaryRadix 8 = 2 := by
  decide +kernel

/--
The capability lists every tagged candidate that applies (in the order of their ranks), then the
baseline.
-/
example :
    let decimal := (ExecFloat.Add.candidates
      (F := FixedPoint.Family FloatLib.Numerics.decimalRadix 2)).toList.map
        (·.estimate.steadyCost)
    let binary := (ExecFloat.Add.candidates
      (F := FixedPoint.Family FloatLib.Numerics.binaryRadix 8)).toList.map
        (·.estimate.steadyCost)
    (decimal = [1000, 1, 2] ∨ decimal = [1, 1000, 2]) ∧ binary = [1000, 2] := by
  decide +kernel

/-! The registry of one specification: the family's baseline and the two candidates tagged here. -/

/--
info: FloatLib.Floats.ExecFloat.FixedPoint.add: FixedPoint.Plan.addCertified (baseline)
FloatLib.Floats.ExecFloat.FixedPoint.add: cheapDecimal (alternative)
FloatLib.Floats.ExecFloat.FixedPoint.add: expensive (alternative)
-/
#guard_msgs in
#compiler_backends FixedPoint.add

/-- Arithmetic still equals the reference, whichever candidate runs. -/
example (x y : Cents) : x + y = FixedPoint.add x y :=
  FloatLib.Floats.ExecFloat.Add.run_eq_spec x y

/-- A kernel that is not the reference addition. -/
def firstOperand {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x _y : ExecFloat.FixedPoint radix digits) : ExecFloat.FixedPoint radix digits :=
  x

/--
error: `@[compiler_optimize]` cannot register `firstOperand`: it is not a certified implementation. Its type must end in `Backend.Certified spec`, `Option (Backend.Certified spec)` or `List (Backend.Certified spec)`: the kernel together with its estimate and the proof `run = spec`, for example `Certified.binary estimate spec run run_eq_spec`. An implementation without that proof cannot be registered.
-/
#guard_msgs in
attribute [compiler_optimize] firstOperand

/--
error: `@[compiler_optimize]` cannot register `sorryAx`: its proof contains `sorry`. A backend is registered only with a complete proof that it equals the reference operation (no axiom beyond `propext`, `Classical.choice` and `Quot.sound`).
-/
#guard_msgs in
#check_proved "compiler_optimize" "sorryAx"

/-- A candidate with an argument that the format in use does not determine. -/
def needsProof {radix : FloatLib.Numerics.Radix} {digits : Nat} (_small : digits < 4) :
    Backend.Certified (FixedPoint.add (radix := radix) (fractionalDigits := digits)) :=
  expensive

/--
error: `@[compiler_optimize]` cannot register `needsProof`: its argument `_small` does not appear in the specification
  FixedPoint.add
so the format in use does not determine it. Decide eligibility inside the candidate and return `none` or `[]` for a format it does not support.
-/
#guard_msgs in
attribute [compiler_optimize] needsProof

/-- The refused candidates did not enter the selection. -/
example : selectedAdd% FloatLib.Numerics.decimalRadix 2 = 1 := by
  decide +kernel

/-! ## Formats with a static form -/

open FloatLib.Floats.Formats.BinaryInterchange in
/--
The kind of the multiplication candidate selected for a configured binary type. It is a macro
for the reason given at `selectedAdd%`.
-/
local macro "selectedMulKind% " family:term:max : term =>
  `((ExecFloat.Mul.selectedCandidate (F := $family)).kind)

/--
Binary32 has a static form: its capability names the fixed-format word kernel, and no tagged
candidate applies to it so far.
-/
example : selectedMulKind% (ExecFloat.Binary.Family 8 23) = .fixedFormat := by
  decide +kernel

open FloatLib.Floats.Formats.BinaryInterchange in
/--
A candidate for the multiplication of every configured binary format on a built-in carrier of
at most 32 bits, with a cost below every built-in kernel. It runs the reference operation.
-/
@[compiler_optimize]
def cheapNarrowMul (format : FloatFormat) (plan : Configured.StoragePlan format) :
    Option (Backend.Certified
      (@Configured.Spec.mul format plan (Configured.Code plan) inferInstance)) :=
  if format.bitWidth ≤ 32 then
    some (Backend.Certified.binary
      { name := "cheap narrow multiplication", kind := .custom "test kernel" 0, steadyCost := 1 }
      Configured.Spec.mul (fun left right => Configured.Spec.mul left right) fun _ _ => rfl)
  else none

/--
Binary32 now runs the tagged candidate: the static form steps aside for the planner's choice,
with no edit to the binary32 instances.
-/
example : selectedMulKind% (ExecFloat.Binary.Family 8 23) = .custom "test kernel" 0 := by
  decide +kernel

/-- So does a 16-bit format, whose capability was already policy-selected. -/
example : selectedMulKind% (ExecFloat.Binary.Family 5 10) = .custom "test kernel" 0 := by
  decide +kernel

/-- Binary64 is outside the candidate's formats: it keeps its fixed-format kernel. -/
example : selectedMulKind% (ExecFloat.Binary.Family 11 52) = .fixedFormat := by
  decide +kernel

open FloatLib.Floats.Formats.BinaryInterchange in
/-- Instance search cannot see that the candidate returns `none` for binary64, so the collection
for binary64 multiplication counts as open: its fixed-format kernel is selected, but through the
planner's dispatch. -/
example : Backend.Collected
    (Configured.Spec.mul : OperationSignature (ExecFloat.Binary.Family 11 52) .mul) .opened :=
  inferInstance

open FloatLib.Floats.Formats.BinaryInterchange in
/-- The candidate declines every binary64 carrier. Stated as an instance, instance search can
tell. -/
instance cheapNarrowMul_binary64
    (plan : Configured.StoragePlan (ExecFloat.Binary.descriptor 11 52)) :
    Backend.NoAlternative (cheapNarrowMul (ExecFloat.Binary.descriptor 11 52) plan).toList :=
  ⟨rfl⟩

open FloatLib.Floats.Formats.BinaryInterchange in
/-- With that instance the collection is closed, and binary64 multiplication is the family's
static capability itself again. -/
example : Backend.Collected
    (Configured.Spec.mul : OperationSignature (ExecFloat.Binary.Family 11 52) .mul) .closed :=
  inferInstance

open FloatLib.Floats.Formats.BinaryInterchange in
/-- Binary32, which the candidate serves, stays open. -/
example : Backend.Collected
    (Configured.Spec.mul : OperationSignature (ExecFloat.Binary.Family 8 23) .mul) .opened :=
  inferInstance

/-- Another operation of binary32 is untouched. -/
example :
    (ExecFloat.Add.selectedCandidate (F := ExecFloat.Binary.Family 8 23)).kind = .fixedFormat := by
  decide +kernel

/-- Binary32 multiplication still equals its reference, whichever candidate runs. -/
example (x y : ExecFloat (ExecFloat.Binary.Family 8 23)) :
    x * y = ExecFloat.Spec.mul x y :=
  ExecFloat.Mul.run_eq_spec x y

open FloatLib.Floats.Formats.BinaryInterchange in
/-- The one-byte family E4M3 selects its addition table under the balanced policy. -/
example :
    (ExecFloat.Add.selectedCandidate (F := E4M3.Family)).kind = .exhaustiveTable := by
  decide +kernel

open FloatLib.Floats.Formats.BinaryInterchange in
/-- A candidate for E4M3 addition only, cheaper than the table. -/
@[compiler_optimize]
def cheapE4M3FNAdd :
    Backend.Certified (StaticByte.Spec.add (F := E4M3.Family)) :=
  Backend.Certified.binary
    { name := "cheap E4M3 addition", kind := .custom "test kernel" 0, steadyCost := 1 }
    StaticByte.Spec.add (fun left right => StaticByte.Spec.add left right) fun _ _ => rfl

open FloatLib.Floats.Formats.BinaryInterchange in
/-- The byte family now runs the tagged candidate. -/
example :
    (ExecFloat.Add.selectedCandidate (F := E4M3.Family)).kind = .custom "test kernel" 0 := by
  decide +kernel

/-! ## Compiler replacements

A certificate proves `run = spec` for Lean definitions. Compiled code runs what the compiler puts
in their place, so `@[compiler_optimize]` refuses a candidate that reaches a replacement without
a registered proof (`Provenance.requireCompiled`).
-/

/-- Code that is not the reference addition. -/
def firstOperandCode {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x _y : ExecFloat.FixedPoint radix digits) : ExecFloat.FixedPoint radix digits :=
  x

/-- A kernel whose definition is the reference addition and whose compiled code is not. -/
@[implemented_by firstOperandCode]
def replacedAdd {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x y : ExecFloat.FixedPoint radix digits) : ExecFloat.FixedPoint radix digits :=
  FixedPoint.add x y

/-- A certificate with a complete proof about the definition of `replacedAdd`. -/
def replacedCandidate {radix : FloatLib.Numerics.Radix} {digits : Nat} :
    Backend.Certified (FixedPoint.add (radix := radix) (fractionalDigits := digits)) :=
  Backend.Certified.binary (estimate "replaced" 3000) FixedPoint.add replacedAdd fun _ _ => rfl

/--
error: `@[compiler_optimize]` cannot register `replacedCandidate`: its compiled code is not the code of its definitions, because `replacedAdd` is implemented by `firstOperandCode`. The proof `run = spec` is about the definitions. Register the proof that a replacement computes its definition with `@[replacement_proof]`, or use a `@[csimp]` equation.
-/
#guard_msgs in
attribute [compiler_optimize] replacedCandidate

/-- The replacement behind one more definition. -/
def viaReplacedAdd {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x y : ExecFloat.FixedPoint radix digits) : ExecFloat.FixedPoint radix digits :=
  replacedAdd x y

/-- A certificate that reaches the replacement through `viaReplacedAdd`. -/
def indirectCandidate {radix : FloatLib.Numerics.Radix} {digits : Nat} :
    Backend.Certified (FixedPoint.add (radix := radix) (fractionalDigits := digits)) :=
  Backend.Certified.binary (estimate "indirect" 3000) FixedPoint.add viaReplacedAdd
    fun _ _ => rfl

/--
error: `@[compiler_optimize]` cannot register `indirectCandidate`: its compiled code is not the code of its definitions, because `replacedAdd` is implemented by `firstOperandCode`. The proof `run = spec` is about the definitions. Register the proof that a replacement computes its definition with `@[replacement_proof]`, or use a `@[csimp]` equation.
-/
#guard_msgs in
attribute [compiler_optimize] indirectCandidate

/-- A kernel whose compiled code is `swappedAdd`, which does compute it. -/
@[implemented_by swappedAdd]
def provedAdd {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x y : ExecFloat.FixedPoint radix digits) : ExecFloat.FixedPoint radix digits :=
  FixedPoint.add x y

/-- A statement about some arguments only is not a replacement proof. -/
theorem swappedAdd_eq_provedAdd_self {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x : ExecFloat.FixedPoint radix digits) : swappedAdd x x = provedAdd x x :=
  swappedAdd_eq x x

/--
error: replacement proof `swappedAdd_eq_provedAdd_self` must equate `swappedAdd` and `provedAdd` on all universally quantified arguments, without additional hypotheses
-/
#guard_msgs in
attribute [replacement_proof] swappedAdd_eq_provedAdd_self

/-- The replacement computes its definition, for all arguments. -/
@[replacement_proof]
theorem swappedAdd_eq_provedAdd {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x y : ExecFloat.FixedPoint radix digits) : swappedAdd x y = provedAdd x y :=
  swappedAdd_eq x y

/-- With the registered proof the candidate is accepted. -/
@[compiler_optimize]
def provedCandidate {radix : FloatLib.Numerics.Radix} {digits : Nat} :
    Backend.Certified (FixedPoint.add (radix := radix) (fractionalDigits := digits)) :=
  Backend.Certified.binary (estimate "proved replacement" 3000) FixedPoint.add provedAdd
    fun _ _ => rfl

/-- The accepted candidate is collected, and the refused ones are not. -/
example :
    ((ExecFloat.Add.candidates
      (F := FixedPoint.Family FloatLib.Numerics.binaryRadix 8)).toList.map
        (·.estimate.steadyCost)).count 3000 = 1 := by
  decide +kernel

/-! ### Constructor indices that Lean generates

Since Lean 4.36 the constructor index `T.ctorIdx` of an inductive type with several constructors
is implemented by a generated read of the constructor tag, which derived equality tests call.
`requireCompiled` accepts exactly that pair (`Provenance.isGeneratedCtorIdx`), and refuses a
constructor index written by hand: one whose replacement is other code, and one whose replacement
is a tag read but whose definition is not the constructor index.
-/

/-- A type whose derived equality test compares constructor indices. -/
inductive Side where
  | left | right | both
  deriving DecidableEq

/-- Code that reaches the generated constructor index of `Side`. -/
def sameSide (first second : Side) : Bool :=
  decide (first = second)

#guard_msgs in
run_cmd Lean.Elab.Command.liftCoreM <|
  FloatLib.Numerics.Provenance.requireCompiled `compiler_optimize ``sameSide

set_option genCtorIdx false in
/-- A type for which Lean generates no constructor index. -/
inductive Choice where
  | first | second

/-- Code that is not a read of the constructor tag. -/
def Choice.ctorIdx._impl (_ : Choice) : Nat :=
  0

/-- A constructor index written by hand, with a replacement that is not Lean's tag read. -/
@[implemented_by Choice.ctorIdx._impl]
def Choice.ctorIdx : Choice → Nat
  | .first => 0
  | .second => 1

/-- Code that reaches the hand-written constructor index. -/
def choiceIndex (choice : Choice) : Nat :=
  choice.ctorIdx

/--
error: `@[compiler_optimize]` cannot register `choiceIndex`: its compiled code is not the code of its definitions, because `Choice.ctorIdx` is implemented by `Choice.ctorIdx._impl`. The proof `run = spec` is about the definitions. Register the proof that a replacement computes its definition with `@[replacement_proof]`, or use a `@[csimp]` equation.
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftCoreM <|
  FloatLib.Numerics.Provenance.requireCompiled `compiler_optimize ``choiceIndex

set_option genCtorIdx false in
/-- A second type for which Lean generates no constructor index. -/
inductive Flag where
  | off | on

/-- A read of the constructor tag, as Lean's own implementation is. -/
unsafe def Flag.ctorIdx._impl (flag : Flag) : Nat :=
  getObjTagNat flag

/-- A definition under the name of the constructor index that is not the constructor index. -/
@[implemented_by Flag.ctorIdx._impl]
def Flag.ctorIdx (_ : Flag) : Nat :=
  0

/-- Code that reaches the definition whose compiled code is the tag read. -/
def flagIndex (flag : Flag) : Nat :=
  flag.ctorIdx

/--
error: `@[compiler_optimize]` cannot register `flagIndex`: its compiled code is not the code of its definitions, because `Flag.ctorIdx` is implemented by `Flag.ctorIdx._impl`. The proof `run = spec` is about the definitions. Register the proof that a replacement computes its definition with `@[replacement_proof]`, or use a `@[csimp]` equation.
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftCoreM <|
  FloatLib.Numerics.Provenance.requireCompiled `compiler_optimize ``flagIndex

/-! ## Shared reference certificates -/

attribute [compiler_optimize reference] reference

/-- Reference registration preserves the operation and its generic certificate. -/
example :
    (compiled_reference% reference using estimate "reference" 1).run = reference :=
  (compiled_reference% reference using estimate "reference" 1).run_eq_spec

/-- Arguments can specialize a reference before it is certified. -/
example (n : Nat) :
    (compiled_reference% reference n using estimate "partial reference" 1).run = reference n :=
  (compiled_reference% reference n using estimate "partial reference" 1).run_eq_spec

/-- A reference can quantify over an arbitrary type universe. -/
def referenceIdentity {α : Type u} (value : α) : α := value

reference_paths referenceIdentity

/-- Universe-polymorphic dependent function types retain their identity certificate. -/
example : Backend.Certified (@referenceIdentity.{u}) :=
  compiled_reference% (@referenceIdentity.{u}) using estimate "polymorphic" 1

/-- error: the operation is not tagged `@[compiler_optimize reference]` -/
#guard_msgs in
example : Backend.Certified (@firstOperandCode) :=
  compiled_reference% (@firstOperandCode) using estimate "unregistered" 1

/--
error: `@[compiler_optimize]` cannot register `replacedAdd`: its compiled code is not the code of its definitions, because `replacedAdd` is implemented by `firstOperandCode`. The proof `run = spec` is about the definitions. Register the proof that a replacement computes its definition with `@[replacement_proof]`, or use a `@[csimp]` equation.
-/
#guard_msgs in
attribute [compiler_optimize reference] replacedAdd

/-- An executable reference cannot be a noncomputable choice. -/
noncomputable def chosenNat : Nat := Classical.choice (inferInstance : Nonempty Nat)

/-- error: `@[compiler_optimize reference]` requires a safe computable definition -/
#guard_msgs in
attribute [compiler_optimize reference] chosenNat

/-- error: `@[compiler_optimize reference]` requires a safe computable definition -/
#guard_msgs in
attribute [compiler_optimize reference] swappedAdd_eq_provedAdd

end FloatLibTests.Conformance.Execution.BackendTags
