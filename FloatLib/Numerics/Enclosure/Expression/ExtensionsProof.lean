/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public import FloatLib.Numerics.Enclosure.Expression.Extensions

/-!
# Containment for registered operations

Parallel tables of executable enclosures and real functions are connected by containment proofs.
Only the executable table participates in the Boolean check. The semantic table and its proofs
enter the soundness theorem, preserving the same trust boundary as the built-in backend.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Interpret a registered operation index; unavailable entries have an unused default value. -/
noncomputable def extensionValues (functions : List (List ℝ → ℝ)) (index : Nat) : List ℝ → ℝ :=
  functions[index]?.getD (fun _ => 0)

/-- The enclosure and semantic tables agree at every available index. -/
def ExtensionsSound (extensions : List Extension) (functions : List (List ℝ → ℝ)) : Prop :=
  ∀ (index : Nat) (E : Extension), extensions[index]? = some E →
    ∀ (config : Backend.Config) (inputs : List (Interval ℚ)) (output : Interval ℚ)
      (values : List ℝ), E.enclose? config inputs = some output →
      inputs.length = E.arity → List.Forall₂ (fun I x => I.ContainsReal some x) inputs values →
      output.ContainsReal some (extensionValues functions index values)

/-- Empty extension tables have no successful calls. -/
theorem extensionsSound_nil : ExtensionsSound [] [] := by
  intro index E h
  simp at h

/-- Add one proved enclosure and its real function to matching extension tables. -/
theorem ExtensionsSound.cons {extensions functions} (h : ExtensionsSound extensions functions)
    {E : Extension} {f : RealFunction E.arity} (hf : E.Sound f) :
    ExtensionsSound (E :: extensions) (RealFunction.apply f :: functions) := by
  intro index F hF config inputs output values houtput hlength hinputs
  cases index with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hF
    subst F
    exact hf config inputs output values houtput hlength hinputs
  | succ index =>
    exact h index F (by simpa using hF) config inputs output values houtput hlength hinputs

private theorem decodedInputs_sound {α : Type*} {decode : α → Option ℚ}
    {inputs : List (Interval α)} {decoded : List (Interval ℚ)} {values : List ℝ}
    (h : inputs.mapM (fun I => I.decode? decode) = some decoded)
    (hx : List.Forall₂ (fun I x => I.ContainsReal decode x) inputs values) :
    decoded.length = inputs.length ∧
      List.Forall₂ (fun I x => I.ContainsReal some x) decoded values := by
  induction hx generalizing decoded with
  | nil =>
    simp at h
    subst decoded
    exact ⟨rfl, .nil⟩
  | @cons I x inputs values hi hx ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨J, hJ, rest, hrest, rfl⟩ := h
    obtain ⟨hlen, hvalues⟩ := ih hrest
    refine ⟨by simpa using hlen, .cons ?_ hvalues⟩
    simpa [ContainsReal, Contains] using (containsReal_iff_of_decode? hJ x).mp hi

/-- Registered proofs and outward rounding extend any sound endpoint backend. -/
theorem Backend.withExtensions_sound {α : Type*} {B : Backend α}
    {baseFunctions : Nat → List ℝ → ℝ} (hB : B.Sound baseFunctions)
    (config : Backend.Config) {extensions functions} (hE : ExtensionsSound extensions functions) :
    (B.withExtensions config extensions).Sound (extensionValues functions) where
  const := hB.const
  unary := hB.unary
  binary := hB.binary
  ternary := hB.ternary
  call := by
    intro index inputs output values h hx
    cases he : extensions[index]? with
    | none => simp [Backend.withExtensions, he] at h
    | some E =>
      by_cases hlen : inputs.length = E.arity
      · cases hd : inputs.mapM (fun I => I.decode? B.decode) with
        | none => simp [Backend.withExtensions, he, hlen, hd] at h
        | some decoded =>
          cases ho : E.enclose? config decoded with
          | none => simp [Backend.withExtensions, he, hlen, hd, ho] at h
          | some J =>
            obtain ⟨hlength, hvalues⟩ := decodedInputs_sound hd hx
            exact Backend.containsReal_encloseInterval? hB
              (by simpa [Backend.withExtensions, he, hlen, hd, ho] using h)
              (hE index E he config decoded J values ho (hlength.trans hlen) hvalues)
      · simp [Backend.withExtensions, he, hlen] at h

end FloatLib.Numerics.Interval
