/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.System

/-!
# Relational quantization specifications

Quantization is not, in general, a function from one scalar to one stored code. A result may
depend on a block scale, an exception policy, an entropy stream, a status accumulator, or a
format-specific tie rule. Some specifications intentionally permit several results before an
implementation fixes one.

`Spec Context Exact Result` is therefore the relation

```text
Context → Exact → Result → Prop
```

used to specify these choices. Deterministic reference functions and executable kernels are
ordinary functions proved to satisfy the relation.

This separation follows the distinction between representability and rounding used in generic
floating-point libraries.  In particular, Flocq defines format membership independently from
rounding operators; see S. Boldo and G. Melquiond, “Flocq: A Unified Library for Proving
Floating-Point Algorithms in Coq,” ARITH 2011, DOI 10.1109/ARITH.2011.40.
-/

@[expose] public section

namespace FloatLib.Numerics.Quantization

universe u v w x

/--
A context-indexed relation describing the permitted result of quantizing an exact input.

`Context`, `Exact`, and `Result` are deliberately arbitrary.  For example, `Context` may contain a
shared exponent or entropy state, while `Result` may be a code, a code/status pair, or an updated
entropy state together with a code.
-/
abbrev Spec (Context : Type u) (Exact : Type v) (Result : Type w) :=
  Context → Exact → Result → Prop

namespace Spec

variable {Context : Type u} {Exact : Type v} {Result : Type w}

/-- An implementation chooses a result permitted by the relational specification. -/
def Implements (spec : Spec Context Exact Result)
    (run : Context → Exact → Result) : Prop :=
  ∀ context input, spec context input (run context input)

/-- Every context and exact input has at least one permitted result. -/
def Total (spec : Spec Context Exact Result) : Prop :=
  ∀ context input, ∃ result, spec context input result

/-- The relation permits at most one result for each context and exact input. -/
def Deterministic (spec : Spec Context Exact Result) : Prop :=
  ∀ context input left right,
    spec context input left → spec context input right → left = right

/-- A reference function viewed as a singleton-valued relational specification. -/
def ofFunction (reference : Context → Exact → Result) : Spec Context Exact Result :=
  fun context input result => result = reference context input

/-- The reference function implements its singleton relational specification. -/
@[simp, grind .] theorem implements_ofFunction (reference : Context → Exact → Result) :
    (ofFunction reference).Implements reference := by
  intro _ _
  rfl

/-- A singleton relational specification is total. -/
theorem total_ofFunction (reference : Context → Exact → Result) :
    (ofFunction reference).Total := by
  intro context input
  exact ⟨reference context input, rfl⟩

/-- A singleton relational specification is deterministic. -/
theorem deterministic_ofFunction (reference : Context → Exact → Result) :
    (ofFunction reference).Deterministic := by
  intro context input left right hleft hright
  rw [hleft, hright]

/--
Map every permitted result through a pure post-processing function.

An output is permitted exactly when it is the image of a permitted source result. This is a
proposition about the output; it adds no runtime wrapper.
-/
def mapResult {MappedResult : Type x} (spec : Spec Context Exact Result)
    (f : Result → MappedResult) : Spec Context Exact MappedResult :=
  fun context input output =>
    ∃ result, spec context input result ∧ f result = output

/-- Post-processing a conforming implementation preserves conformance. -/
theorem implements_mapResult {MappedResult : Type x} (spec : Spec Context Exact Result)
    (f : Result → MappedResult) (run : Context → Exact → Result)
    (implements : spec.Implements run) :
    (spec.mapResult f).Implements (fun context input => f (run context input)) := by
  intro context input
  exact ⟨run context input, implements context input, rfl⟩

/-- Mapping the results of a total relation preserves totality. -/
theorem total_mapResult {MappedResult : Type x} (spec : Spec Context Exact Result)
    (f : Result → MappedResult) (total : spec.Total) :
    (spec.mapResult f).Total := by
  intro context input
  obtain ⟨result, permitted⟩ := total context input
  exact ⟨f result, result, permitted, rfl⟩

/-- Mapping the unique result of a deterministic relation remains deterministic. -/
theorem deterministic_mapResult {MappedResult : Type x} (spec : Spec Context Exact Result)
    (f : Result → MappedResult) (deterministic : spec.Deterministic) :
    (spec.mapResult f).Deterministic := by
  intro context input left right hleft hright
  obtain ⟨leftSource, leftPermitted, rfl⟩ := hleft
  obtain ⟨rightSource, rightPermitted, rfl⟩ := hright
  exact congrArg f (deterministic context input leftSource rightSource leftPermitted rightPermitted)

/--
Relational specification saying that a result code represents the scalar selected by `target`.

This is the bridge from context-dependent rounding to the common `NumericalSystem`
representability predicate.
-/
def represents (system : NumericalSystem) (target : Context → Exact → system.Scalar) :
    Spec Context Exact system.Code :=
  fun context input code => system.Represents code (target context input)

/-- A code-valued kernel implements `represents` exactly when every result represents its target. -/
theorem implements_represents_iff (system : NumericalSystem)
    (target : Context → Exact → system.Scalar)
    (run : Context → Exact → system.Code) :
    (represents system target).Implements run ↔
      ∀ context input, system.Represents (run context input) (target context input) :=
  Iff.rfl

end Spec

end FloatLib.Numerics.Quantization
