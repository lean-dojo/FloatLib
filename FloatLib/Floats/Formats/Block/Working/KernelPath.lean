/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Working.Binary
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Flat
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Compare
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Div
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.Multiplication
public import FloatLib.Tactic.KernelOptimize

/-!
# The working quantizer on natural-number words

Lean's kernel computes natively on natural-number literals only. This module has the block
quantizer of `Block.Working.Binary` as functions of the encodings, built from the flat binary
operations of `BinaryInterchange.KernelPath.Flat`, for every working format, scale format and
element format:

* `clamp`, `blockMax`, `scale`, `reciprocal`, `element` and `elements` are `Working.clamp`,
  `Working.blockMax`, `Quantizer.scale`, `Quantizer.reciprocal`, `Quantizer.element` and the
  elements of `Quantizer.block` on words;
* `toNatBits_scale`, `toNatBits_reciprocal`, `toNatBits_element`, `block_fst` and `words_eq`
  are the kernel rules: the encoding of what the quantizer stores is the
  word that these functions compute, for every operand, NaNs and infinities included.
  `float_decide` rewrites with them.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block.Working.KernelPath

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.BinaryInterchange.Model

variable {W S E : FloatFormat}

/-- The flat comparison code of two words of the working format. -/
local notation "compareWords" => BinaryInterchange.KernelPath.Flat.compare

/-- The flat division of the working format. -/
local notation "divWords" => BinaryInterchange.KernelPath.Flat.div

/-- The flat cast between two formats. -/
local notation "castWords" => BinaryInterchange.KernelPath.Flat.cast

/-- `Working.clamp` on words: `low` when the comparison code of `x` with `low` is zero (less),
`high` when that of `high` with `x` is zero, and `x` otherwise. -/
noncomputable def clamp (W : FloatFormat) (low high x : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (compareWords W x low) 0)
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (compareWords W high x) 0) x high)
    low

/-- `Working.blockMax` on words. -/
noncomputable def blockMax (W : FloatFormat) (block : List Nat) : Nat :=
  List.foldl
    (fun best x =>
      (fun a => Bool.casesOn (motive := fun _ => Nat) (Nat.beq (compareWords W best a) 0) best a)
        (BinaryInterchange.KernelPath.abs W x))
    0 block

/-- `Quantizer.scale` on words. -/
noncomputable def scale (W S : FloatFormat) (target floor ceiling outer : Nat)
    (block : List Nat) : Nat :=
  castWords W S .nearest
    (clamp W floor ceiling (divWords W .nearest (divWords W .nearest (blockMax W block) target)
      outer))

/-- `Quantizer.reciprocal` on words. `one` is the word of the value one. -/
noncomputable def reciprocal (W S : FloatFormat) (one outer stored : Nat) : Nat :=
  divWords W .nearest (divWords W .nearest one outer) (castWords S W .nearest stored)

/-- `Quantizer.element` on words. -/
noncomputable def element (W E : FloatFormat) (target reciprocal x : Nat) : Nat :=
  castWords W E .nearest
    (clamp W (BinaryInterchange.KernelPath.Flat.neg W target) target
      (BinaryInterchange.KernelPath.Flat.mul W .nearest x reciprocal))

/-- The elements of `Quantizer.block` on words: the scale and the reciprocal are computed once
for the block. -/
noncomputable def elements (W S E : FloatFormat) (target floor ceiling one outer : Nat)
    (block : List Nat) : List Nat :=
  (fun r => List.map (element W E target r) block)
    (reciprocal W S one outer (scale W S target floor ceiling outer block))

/-- The flat comparison code decides `compare x y = some .lt`. -/
theorem compare_eq_zero_iff (x y : Model W) :
    Nat.beq (compareWords W x.toNatBits y.toNatBits) 0 = decide (compare x y = some .lt) := by
  have h := BinaryInterchange.KernelPath.compareCode_eq x y
  have hflat : compareWords W x.toNatBits y.toNatBits =
      BinaryInterchange.KernelPath.compareCode W x.toNatBits y.toNatBits := rfl
  rw [hflat, ← h]
  generalize BinaryInterchange.KernelPath.compareCode W x.toNatBits y.toNatBits = c
  unfold BinaryInterchange.KernelPath.decodeOrdering
  rcases c with _ | _ | _ | _ | c <;> rfl

/-- `clamp` computes the encoding of `Working.clamp`. -/
theorem clamp_eq (low high x : Model W) :
    clamp W low.toNatBits high.toNatBits x.toNatBits = (Working.clamp low high x).toNatBits := by
  unfold clamp Working.clamp
  rw [compare_eq_zero_iff, compare_eq_zero_iff]
  by_cases h1 : compare x low = some .lt
  · simp [h1]
  · by_cases h2 : compare high x = some .lt <;> simp [h1, h2]

/-- `blockMax` computes the encoding of `Working.blockMax`. -/
theorem blockMax_eq (block : List (Model W)) :
    blockMax W (block.map toNatBits) = (Working.blockMax block).toNatBits := by
  have hgen : ∀ (block : List (Model W)) (init : Model W),
      List.foldl
          (fun best x =>
            (fun a =>
              Bool.casesOn (motive := fun _ => Nat)
                (Nat.beq (compareWords W best a) 0) best a)
              (BinaryInterchange.KernelPath.abs W x))
          init.toNatBits (block.map toNatBits) =
        (block.foldl (fun best x => if compare best (abs x) = some .lt then abs x else best)
          init).toNatBits := by
    intro block
    induction block with
    | nil => intro init; rfl
    | cons x xs ih =>
      intro init
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
      congr 1
      dsimp only
      rw [BinaryInterchange.KernelPath.abs_eq_spec, compare_eq_zero_iff]
      by_cases h : compare init (abs x) = some .lt <;> simp [h]
  have hzero : (zero W false).toNatBits = 0 := by
    rw [show zero W false = posZero W by simp [zero]]
    exact BinaryInterchange.KernelPath.toNatBits_posZero W
  unfold blockMax Working.blockMax
  rw [← hgen, hzero]

/-- The encoding of the stored block scale is the word that `scale` computes. The declared
cost is that of a block of sixteen values. -/
@[kernel_optimize (cost := 3400)] theorem toNatBits_scale (Q : Quantizer W S E) (outer : Model W)
    (block : List (Model W)) :
    (Q.scale outer block).toNatBits =
      scale W S Q.target.toNatBits Q.floor.toNatBits Q.ceiling.toNatBits outer.toNatBits
        (block.map toNatBits) := by
  unfold scale Quantizer.scale Quantizer.scaled
  rw [blockMax_eq, BinaryInterchange.KernelPath.Flat.div_eq,
    BinaryInterchange.KernelPath.div_eq_spec, BinaryInterchange.KernelPath.div_eq_spec, clamp_eq,
    BinaryInterchange.KernelPath.Flat.cast_eq, BinaryInterchange.KernelPath.cast_eq_spec]

/-- The encoding of the reciprocal of the total scale is the word that `reciprocal` computes. -/
@[kernel_optimize (cost := 650)] theorem toNatBits_reciprocal (Q : Quantizer W S E)
    (outer : Model W) (stored : Model S) :
    (Q.reciprocal outer stored).toNatBits =
      reciprocal W S (posOne W).toNatBits outer.toNatBits stored.toNatBits := by
  unfold reciprocal Quantizer.reciprocal
  rw [BinaryInterchange.KernelPath.Flat.div_eq, BinaryInterchange.KernelPath.Flat.cast_eq,
    BinaryInterchange.KernelPath.cast_eq_spec, BinaryInterchange.KernelPath.div_eq_spec,
    BinaryInterchange.KernelPath.div_eq_spec]

/-- The encoding of a stored element is the word that `element` computes. -/
@[kernel_optimize (cost := 600)] theorem toNatBits_element (Q : Quantizer W S E)
    (r x : Model W) :
    (Q.element r x).toNatBits = element W E Q.target.toNatBits r.toNatBits x.toNatBits := by
  have hneg : BinaryInterchange.KernelPath.Flat.neg W Q.target.toNatBits =
      (neg Q.target).toNatBits := BinaryInterchange.KernelPath.neg_eq_spec Q.target
  unfold element Quantizer.element
  rw [hneg, BinaryInterchange.KernelPath.Flat.mul_eq,
    BinaryInterchange.KernelPath.mulFast_eq_spec, clamp_eq,
    BinaryInterchange.KernelPath.Flat.cast_eq, BinaryInterchange.KernelPath.cast_eq_spec]

/-- The scale of a quantized block is the stored block scale. -/
@[kernel_optimize] theorem block_fst (Q : Quantizer W S E) (outer : Model W)
    (values : List (Model W)) : (Q.block outer values).1 = Q.scale outer values :=
  rfl

/-- The words that a block stores are the word that `scale` computes and the words that
`elements` computes. The declared cost is that of a block of sixteen values. -/
@[kernel_optimize (cost := 8500)] theorem words_eq (Q : Quantizer W S E) (outer : Model W)
    (values : List (Model W)) :
    Q.words outer values =
      (scale W S Q.target.toNatBits Q.floor.toNatBits Q.ceiling.toNatBits outer.toNatBits
          (values.map toNatBits),
        elements W S E Q.target.toNatBits Q.floor.toNatBits Q.ceiling.toNatBits
          (posOne W).toNatBits outer.toNatBits (values.map toNatBits)) := by
  unfold elements Quantizer.words Quantizer.block
  rw [← toNatBits_scale, ← toNatBits_reciprocal Q]
  dsimp only
  rw [List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => toNatBits_element Q _ x

end FloatLib.Floats.Formats.Block.Working.KernelPath
