/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.KernelRefl
public import FloatLib.Tactic.ScanLoop

/-!
# Specialized profile scans

The specialized forms are definitionally equal to the generic algorithms. The theorems
below connect these forms to the rounding specification for every supported profile.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard.Element

open FloatLib.Numerics FloatLib.Floats.ExecFloat.KernelPath

/--
The scan of all codes of a profile, with one flat step per profile: the form that Lean's kernel
evaluates. It is `scan` over the `2 ^ width` codes (`scanAll_eq`).
-/
noncomputable def scanAll (profile : Profile) (sp neg ap q : Nat) : Option Nat :=
  Profile.casesOn (motive := fun _ => Option Nat) profile
    (scan_loop% .e5m2 sp neg ap q 256) (scan_loop% .e4m3 sp neg ap q 256)
    (scan_loop% .e3m2 sp neg ap q 64) (scan_loop% .e2m3 sp neg ap q 64)
    (scan_loop% .e2m1 sp neg ap q 16) (scan_loop% .int8 sp neg ap q 256)

/-- The flat scan is the scan of all codes of the profile. -/
theorem scanAll_eq (profile : Profile) (sp neg ap q : Nat) :
    scanAll profile sp neg ap q = scan profile sp neg ap q (2 ^ profile.width) := by
  cases profile <;> exact kernel_refl%

/--
The code that nearest-even rounding selects for `input`, with its rounding key above its `width`
bits: the result of the scan of all codes for the numerator and the denominator of the input and
its sign bit, and zero if the profile had no finite code.
-/
noncomputable def scanCode (profile : Profile) (input : SignedRat) : Nat :=
  Option.casesOn (motive := fun _ => Nat)
    (scanAll profile (decide (input.value.num < 0)).toNat input.negative.toNat
      input.value.num.natAbs input.value.den)
    0 fun best => best

/--
Nearest-even element rounding on natural numbers, for every profile and every input: the word
that `quantizeFinite` selects is the low `width` bits of `scanCode`.
-/
theorem quantizeFinite_eq_scan (profile : Profile) (input : SignedRat) :
    quantizeFinite profile input = BitVec.ofNat profile.width (scanCode profile input) := by
  unfold scanCode
  rw [quantizeFinite_eq_argmin, scanAll_eq, scan_eq _ _ _ _ _ _ (Nat.le_refl _)]
  unfold finiteCodes
  generalize ((List.range (2 ^ profile.width)).filter (finiteCode profile)).argmin
    (codeKey profile (decide (input.value.num < 0)).toNat input.negative.toNat
      input.value.num.natAbs input.value.den) = result
  cases result with
  | none => rfl
  | some code =>
      change BitVec.ofNat profile.width code =
        BitVec.ofNat profile.width (packed profile _ _ _ _ code)
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      unfold packed
      rw [Nat.mul_add_mod_self_right]

/-! ## The scan is the least packed entry -/

/-- The result of the scan of the first `count` codes is the packed entry of a finite code below
`count` and is at most the packed entry of every such code; without a result, no code below
`count` is finite. -/
theorem scan_spec (profile : Profile) (sp neg ap q : Nat) : ∀ count,
    (∀ e, scan profile sp neg ap q count = some e →
      (∃ c, c < count ∧ finiteCode profile c = true ∧ e = packed profile sp neg ap q c) ∧
        ∀ c, c < count → finiteCode profile c = true → e ≤ packed profile sp neg ap q c) ∧
    (scan profile sp neg ap q count = none →
      ∀ c, c < count → finiteCode profile c = false)
  | 0 =>
      ⟨fun e h => absurd (show (none : Option Nat) = some e from h) (by simp),
        fun _ c hc => absurd hc (Nat.not_lt_zero c)⟩
  | count + 1 => by
      obtain ⟨ihsome, ihnone⟩ := scan_spec profile sp neg ap q count
      have hentry : Nat.add (Nat.shiftLeft (codeKey profile sp neg ap q count) profile.width)
          count = packed profile sp neg ap q count := by
        change codeKey profile sp neg ap q count <<< profile.width + count = _
        rw [Nat.shiftLeft_eq]; rfl
      change (∀ e, scanStep profile sp neg ap q count (scan profile sp neg ap q count) = some e →
        _) ∧
        (scanStep profile sp neg ap q count (scan profile sp neg ap q count) = none → _)
      unfold scanStep
      cases hfinite : finiteCode profile count
      · -- the code is not finite: the result stays
        dsimp only
        refine ⟨fun e he => ?_, fun hnone c hc => ?_⟩
        · obtain ⟨⟨c, hc, hfc, hec⟩, hmin⟩ := ihsome e he
          refine ⟨⟨c, Nat.lt_succ_of_lt hc, hfc, hec⟩, fun c hc hfc => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | rfl
          · exact hmin c hlt hfc
          · rw [hfinite] at hfc; cases hfc
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | rfl
          · exact ihnone hnone c hlt
          · exact hfinite
      · -- the code is finite
        dsimp only
        rw [hentry]
        cases hbest : scan profile sp neg ap q count with
        | none =>
            have hnone := ihnone hbest
            dsimp only
            refine ⟨fun e he => ?_, fun h => by cases h⟩
            have he' : packed profile sp neg ap q count = e := Option.some.inj he
            subst he'
            refine ⟨⟨count, Nat.lt_succ_self _, hfinite, rfl⟩, fun c hc hfc => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | rfl
            · rw [hnone c hlt] at hfc; cases hfc
            · exact Nat.le_refl _
        | some current =>
            obtain ⟨⟨c0, hc0, hfc0, hec0⟩, hmin⟩ := ihsome current hbest
            dsimp only
            refine ⟨fun e he => ?_, fun h => ?_⟩
            · cases hlt : Nat.blt (packed profile sp neg ap q count) current
              · -- the best stays
                rw [hlt] at he
                have he' : current = e := Option.some.inj he
                subst he'
                have hge : current ≤ packed profile sp neg ap q count := by
                  rcases Nat.lt_or_ge (packed profile sp neg ap q count) current with h | h
                  · have hblt : Nat.blt (packed profile sp neg ap q count) current = true := by
                      rw [Nat.blt_eq]; exact h
                    rw [hblt] at hlt; cases hlt
                  · exact h
                refine ⟨⟨c0, Nat.lt_succ_of_lt hc0, hfc0, hec0⟩, fun c hc hfc => ?_⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt' | rfl
                · exact hmin c hlt' hfc
                · exact hge
              · -- the new code is better
                rw [hlt] at he
                have he' : packed profile sp neg ap q count = e := Option.some.inj he
                subst he'
                have hless : packed profile sp neg ap q count < current := by
                  rw [← Nat.blt_eq]; exact hlt
                refine ⟨⟨count, Nat.lt_succ_self _, hfinite, rfl⟩, fun c hc hfc => ?_⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt' | rfl
                · exact Nat.le_trans (Nat.le_of_lt hless) (hmin c hlt' hfc)
                · exact Nat.le_refl _
            · cases hlt : Nat.blt (packed profile sp neg ap q count) current <;>
                rw [hlt] at h <;> cases h

/-- A packed entry of a finite code below `count` that is at most the packed entry of every such
code is the result of the scan. -/
theorem scan_eq_some (profile : Profile) (sp neg ap q count e : Nat)
    (hmem : ∃ c, c < count ∧ finiteCode profile c = true ∧ e = packed profile sp neg ap q c)
    (hmin : ∀ c, c < count → finiteCode profile c = true → e ≤ packed profile sp neg ap q c) :
    scan profile sp neg ap q count = some e := by
  obtain ⟨hsome, hnone⟩ := scan_spec profile sp neg ap q count
  obtain ⟨c, hc, hfc, hec⟩ := hmem
  cases hscan : scan profile sp neg ap q count with
  | none => rw [hnone hscan c hc] at hfc; cases hfc
  | some e' =>
      obtain ⟨⟨c', hc', hfc', hec'⟩, hmin'⟩ := hsome e' hscan
      have h1 : e' ≤ e := hec ▸ hmin' c hc hfc
      have h2 : e ≤ e' := hec' ▸ hmin c' hc' hfc'
      rw [Nat.le_antisymm h1 h2]

end FloatLib.Floats.Formats.OCP.MX.Standard.Element
