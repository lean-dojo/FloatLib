/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.CFixProof
public import FloatLib.Numerics.Kernel.Multiplicative
public import FloatLib.Numerics.Kernel.SeqProof

/-!
# The total over a split sums a completely multiplicative function

For a pair of functions `fr`, `fi` on the naturals that multiply like the parts of a complex
number, `fr (p * m) = fr p * fr m - fi p * fi m` and `fi (p * m) = fr p * fi m + fi p * fr m`,
that is `(1, 0)` at one, and a function `zp` whose value at every `p` contains `(fr p, fi p)`:

* `Split.total_contains`: `Split.total s zp rough c₁ plan` contains the sums of `fr` and `fi`
  over the integers of all pairs of the split;
* `Split.cover_Icc`: a list that passes `Split.cover lo ν` has each integer from `lo` to `ν`
  once;
* `Split.total_contains_Icc`: so the total over a split that passes `splitOk plan rough c₁ ν`
  contains `∑ n ∈ [1, ν], fr n` and `∑ n ∈ [1, ν], fi n`;
* `Cover.total_contains`: the same for a `Cover`, which carries the proof of `splitOk`;
* `Cover.find_spec`: `Cover.find ν` returns a cover for the bound `ν`.

All of it holds for every split, every bound and numbers of any ordered field.
`FloatLib.Tactic.Cover` gives covers (`cover% ν y` for
any bound).
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

namespace Split

/-- What a passed `cover` says about its list. -/
theorem cover_sound (lo ν : Nat) : ∀ (l : List Nat) (seen count : Nat),
    cover lo ν l seen count = true →
      l.Nodup ∧ (∀ n ∈ l, lo ≤ n ∧ n ≤ ν ∧ seen.testBit n = false) ∧ l.length = count
  | [], seen, count, h => by
    have hc : Nat.beq count 0 = true := h
    have hc' : count = 0 := Nat.eq_of_beq_eq_true hc
    simp [hc']
  | n :: l, seen, count, h => by
    have h' : Bool.and (Bool.and (Nat.ble lo n) (Nat.ble n ν))
        (Bool.and (Nat.beq (bit seen n) 0)
          (Bool.and (Nat.ble 1 count)
            (cover lo ν l (Nat.lor seen (Nat.shiftLeft 1 n)) (Nat.sub count 1)))) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h2, hν⟩, hbit, hcount, hrest⟩ := h'
    have h2' : lo ≤ n := Nat.le_of_ble_eq_true h2
    have hν' : n ≤ ν := Nat.le_of_ble_eq_true hν
    have hcount' : 1 ≤ count := Nat.le_of_ble_eq_true hcount
    have hseen : seen.testBit n = false := by
      have hb := Nat.eq_of_beq_eq_true hbit
      rw [bit_eq] at hb
      cases htb : seen.testBit n
      · rfl
      · rw [htb] at hb
        cases hb
    obtain ⟨hnodup, hall, hlen⟩ := cover_sound lo ν l _ _ hrest
    have hor : ∀ m : Nat, (Nat.lor seen (Nat.shiftLeft 1 n)).testBit m =
        (seen.testBit m || decide (n = m)) := by
      intro m
      change (seen ||| 1 <<< n).testBit m = _
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    refine ⟨?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨?_, hnodup⟩
      intro hmem
      have := (hall n hmem).2.2
      rw [hor] at this
      simp at this
    · intro m hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact ⟨h2', hν', hseen⟩
      · obtain ⟨hm2, hmν, hmbit⟩ := hall m hm
        rw [hor] at hmbit
        refine ⟨hm2, hmν, ?_⟩
        cases hs : seen.testBit m
        · rfl
        · rw [hs] at hmbit
          simp at hmbit
    · change l.length + 1 = count
      rw [hlen]
      change count - 1 + 1 = count
      omega

/-- A list that passes `cover lo ν` from the empty set, with the count `ν + 1 - lo`, has each
integer from `lo` to `ν` once. -/
theorem cover_Icc {lo ν : Nat} {l : List Nat}
    (h : cover lo ν l 0 (ν + 1 - lo) = true) : l.Nodup ∧ l.toFinset = Finset.Icc lo ν := by
  obtain ⟨hnodup, hall, hlen⟩ := cover_sound lo ν _ _ _ h
  refine ⟨hnodup, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    rw [List.mem_toFinset] at hn
    exact Finset.mem_Icc.2 ⟨(hall n hn).1, (hall n hn).2.1⟩
  · rw [List.toFinset_card_of_nodup hnodup, hlen, Nat.card_Icc]

variable {K : Type*} [Field K]

/-- The sums of a multiplicative pair over the multiples `n * r` of a list. -/
theorem sum_mul {fr fi : ℕ → K}
    (hmul : ∀ p m, fr (p * m) = fr p * fr m - fi p * fi m ∧
      fi (p * m) = fr p * fi m + fi p * fr m) (n : ℕ) :
    ∀ l : List (List Nat),
      ((l.map fun r => fr (n * List.prod r)).sum =
          fr n * (l.map fun r => fr (List.prod r)).sum - fi n * (l.map fun r => fi (List.prod
            r)).sum) ∧
        ((l.map fun r => fi (n * List.prod r)).sum =
          fr n * (l.map fun r => fi (List.prod r)).sum + fi n * (l.map fun r => fr (List.prod
            r)).sum)
  | _ => by
    constructor
    · simp_rw [(hmul n _).1, sub_eq_add_neg, ← neg_mul, List.sum_map_add,
        List.sum_map_mul_left]
    · simp_rw [(hmul n _).2, List.sum_map_add, List.sum_map_mul_left]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The value of a list of factors contains the pair at their product, for a pair `fr`, `fi` that
multiplies like the parts of a complex number and is `(1, 0)` at one. -/
theorem prodOf_contains {s : Nat} {zp : Nat → CFix} {fr fi : ℕ → K}
    (hmul : ∀ p m, fr (p * m) = fr p * fr m - fi p * fi m ∧
      fi (p * m) = fr p * fi m + fi p * fr m)
    (hone : fr 1 = 1 ∧ fi 1 = 0) (hzp : ∀ p, (zp p).Contains s (fr p) (fi p)) :
    ∀ l : List Nat, (prodOf s zp l).Contains s (fr (List.prod l)) (fi (List.prod l))
  | [] => by
    change (CFix.one s).Contains s (fr 1) (fi 1)
    rw [hone.1, hone.2]
    exact CFix.contains_one s
  | [q] => by
    change (strict q zp).Contains s (fr (q * 1)) (fi (q * 1))
    rw [strict_eq, Nat.mul_one]
    exact hzp q
  | q :: r :: rest => by
    change (CFix.mul s (strict q zp) (prodOf s zp (r :: rest))).Contains s
      (fr (q * List.prod (r :: rest))) (fi (q * List.prod (r :: rest)))
    rw [strict_eq, (hmul q _).1, (hmul q _).2]
    exact CFix.contains_mul (hzp q) (prodOf_contains hmul hone hzp (r :: rest))

/-- Entry `c` of the running sums contains what `S` contains plus the first `c` values. -/
theorem getD_cums_contains {s : Nat} {zp : Nat → CFix} {fr fi : ℕ → K}
    (hval : ∀ l : List Nat, (prodOf s zp l).Contains s (fr (List.prod l)) (fi (List.prod l))) :
    ∀ (rough : List (List Nat)) (S : CSum) (A B : K) (c : Nat), S.Contains s A B →
      (Seq.getD (cums s zp rough S) c CSum.bad).Contains s
        (A + ((rough.take c).map fun r => fr (List.prod r)).sum)
        (B + ((rough.take c).map fun r => fi (List.prod r)).sum)
  | [], S, A, B, c, hS => by
    cases c with
    | zero => simpa [cums, Seq.getD] using hS
    | succ c =>
      change (Seq.getD [S] (c + 1) CSum.bad).Contains s _ _
      change CSum.bad.Contains s _ _
      exact CSum.contains_bad s _ _
  | r :: rest, S, A, B, c, hS => by
    cases c with
    | zero => simpa [cums, Seq.getD] using hS
    | succ c =>
      change (Seq.getD (S :: cums s zp rest (CSum.push (prodOf s zp r) S)) (c + 1)
        CSum.bad).Contains s _ _
      change (Seq.getD (cums s zp rest (CSum.push (prodOf s zp r) S)) c CSum.bad).Contains s _ _
      have h := getD_cums_contains hval rest _ _ _ c (CSum.contains_push (hval r) hS)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      simpa only [add_comm, add_left_comm, add_assoc] using h

/-- The walk below a node, written out. -/
theorem walk_node (s : Nat) (zp : Nat → CFix) (cs : List CSum) (p c : Nat) (sub rest : Split)
    (zm : CFix) :
    walk s zp cs (node p c sub rest) zm =
      CSum.add (CSum.scale s (CFix.mul s (zp p) zm) (Seq.getD cs c CSum.bad))
        (CSum.add (walk s zp cs sub (CFix.mul s (zp p) zm)) (walk s zp cs rest zm)) := by
  change CSum.add (CSum.scale s (CFix.mul s (strict p zp) zm) (Seq.getD cs c CSum.bad))
    (CSum.add (walk s zp cs sub (CFix.mul s (strict p zp) zm)) (walk s zp cs rest zm)) = _
  rw [strict_eq]

/-- The walk below a node whose value contains `(fr m, fi m)` contains the sums of `fr` and `fi`
over the integers of the pairs below `m`, when entry `c` of `cs` contains the sums over the first
`c` members of `rough`. -/
theorem walk_contains {s : Nat} {zp : Nat → CFix} {fr fi : ℕ → K} {rough : List (List Nat)}
    {cs : List CSum}
    (hmul : ∀ p m, fr (p * m) = fr p * fr m - fi p * fi m ∧
      fi (p * m) = fr p * fi m + fi p * fr m)
    (hzp : ∀ p, (zp p).Contains s (fr p) (fi p))
    (hcs : ∀ c, (Seq.getD cs c CSum.bad).Contains s ((rough.take c).map fun r => fr (List.prod
      r)).sum
      ((rough.take c).map fun r => fi (List.prod r)).sum) :
    ∀ (plan : Split) (m : Nat) (zm : CFix), zm.Contains s (fr m) (fi m) →
      (walk s zp cs plan zm).Contains s ((pairs rough plan m).map fr).sum
        ((pairs rough plan m).map fi).sum
  | nil, _, _, _ => by
    change CSum.zero.Contains s (([] : List ℕ).map fr).sum (([] : List ℕ).map fi).sum
    simpa using CSum.contains_zero (K := K) s
  | node p c sub rest, m, zm, hzm => by
    rw [walk_node]
    have hz : (CFix.mul s (zp p) zm).Contains s (fr (p * m)) (fi (p * m)) := by
      rw [(hmul p m).1, (hmul p m).2]
      exact CFix.contains_mul (hzp p) hzm
    have hscale := CSum.contains_scale hz (hcs c)
    obtain ⟨e1, e2⟩ := sum_mul hmul (p * m) (rough.take c)
    rw [← e1, ← e2] at hscale
    have hsub := walk_contains hmul hzp hcs sub (p * m) _ hz
    have hrest := walk_contains hmul hzp hcs rest m zm hzm
    have hsum := CSum.contains_add hscale (CSum.contains_add hsub hrest)
    have hpairs : pairs rough (node p c sub rest) m =
        ((rough.take c).map fun r => p * m * List.prod r) ++
          (pairs rough sub (p * m) ++ pairs rough rest m) := rfl
    rw [hpairs]
    simpa [List.map_append, List.sum_append, Function.comp_def] using hsum

/-- The total over a split contains the sums of `fr` and `fi` over the integers of all pairs. -/
theorem total_contains {s : Nat} {zp : Nat → CFix} {fr fi : ℕ → K}
    (hmul : ∀ p m, fr (p * m) = fr p * fr m - fi p * fi m ∧
      fi (p * m) = fr p * fi m + fi p * fr m)
    (hone : fr 1 = 1 ∧ fi 1 = 0) (hzp : ∀ p, (zp p).Contains s (fr p) (fi p))
    (rough : List (List Nat)) (c₁ : Nat) (plan : Split) :
    (total s zp rough c₁ plan).Contains s ((allPairs rough c₁ plan).map fr).sum
      ((allPairs rough c₁ plan).map fi).sum := by
  have hval := prodOf_contains hmul hone hzp
  have hcs : ∀ c, (Seq.getD (cums s zp rough CSum.zero) c CSum.bad).Contains s
      ((rough.take c).map fun r => fr (List.prod r)).sum
      ((rough.take c).map fun r => fi (List.prod r)).sum := by
    intro c
    have h := getD_cums_contains hval rough CSum.zero 0 0 c (CSum.contains_zero s)
    simpa using h
  have hroot : (CFix.one s).Contains s (fr 1) (fi 1) := by
    rw [hone.1, hone.2]
    exact CFix.contains_one s
  have hwalk := walk_contains hmul hzp hcs plan 1 _ hroot
  have hsum := CSum.contains_add (hcs c₁) hwalk
  change (CSum.add (Seq.getD (cums s zp rough CSum.zero) c₁ CSum.bad)
    (walk s zp (cums s zp rough CSum.zero) plan (CFix.one s))).Contains s _ _
  simpa [allPairs, List.map_append, List.sum_append, Function.comp_def] using hsum

/-- The total over a split that passes `splitOk plan rough c₁ ν` contains the sums of `fr` and
`fi` over the integers from `1` to `ν`. -/
theorem total_contains_Icc {s : Nat} {zp : Nat → CFix} {fr fi : ℕ → K}
    (hmul : ∀ p m, fr (p * m) = fr p * fr m - fi p * fi m ∧
      fi (p * m) = fr p * fi m + fi p * fr m)
    (hone : fr 1 = 1 ∧ fi 1 = 0) (hzp : ∀ p, (zp p).Contains s (fr p) (fi p))
    {rough : List (List Nat)} {c₁ ν : Nat} {plan : Split}
    (hok : splitOk plan rough c₁ ν = true) :
    (total s zp rough c₁ plan).Contains s (∑ n ∈ Finset.Icc 1 ν, fr n)
      (∑ n ∈ Finset.Icc 1 ν, fi n) := by
  have h' : cover 1 ν (allPairs rough c₁ plan) 0 (ν + 1 - 1) = true := by
    rw [Nat.add_sub_cancel]
    exact hok
  obtain ⟨hnodup, hset⟩ := cover_Icc h'
  rw [← hset, List.sum_toFinset fr hnodup, List.sum_toFinset fi hnodup]
  exact total_contains hmul hone hzp rough c₁ plan

end Split

namespace Cover

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The total of a cover contains the sums of `fr` and `fi` over the integers from `1` to its
bound, for a pair `fr`, `fi` that multiplies like the parts of a complex number and is `(1, 0)`
at one, and values `zp p` that contain `(fr p, fi p)`. -/
theorem total_contains {s : Nat} {zp : Nat → CFix} {fr fi : ℕ → K}
    (hmul : ∀ p m, fr (p * m) = fr p * fr m - fi p * fi m ∧
      fi (p * m) = fr p * fi m + fi p * fr m)
    (hone : fr 1 = 1 ∧ fi 1 = 0) (hzp : ∀ p, (zp p).Contains s (fr p) (fi p)) (c : Cover) :
    (c.total s zp).Contains s (∑ n ∈ Finset.Icc 1 c.ν, fr n) (∑ n ∈ Finset.Icc 1 c.ν, fi n) :=
  Split.total_contains_Icc hmul hone hzp c.ok

/-- `find ν` returns a cover for the bound `ν`. -/
theorem find_spec {ν : ℕ} : ∀ {covers : List Cover} {c : Cover},
    find ν covers = some c → c.ν = ν
  | [], _, h => by cases h
  | d :: rest, c, h => by
    have h' : Bool.casesOn (motive := fun _ => Option Cover) (Nat.beq d.ν ν) (find ν rest)
        (some d) = some c := h
    cases hd : Nat.beq d.ν ν with
    | false =>
      rw [hd] at h'
      exact find_spec h'
    | true =>
      rw [hd] at h'
      cases h'
      exact Nat.eq_of_beq_eq_true hd

end Cover

end FloatLib.Numerics.Kernel
