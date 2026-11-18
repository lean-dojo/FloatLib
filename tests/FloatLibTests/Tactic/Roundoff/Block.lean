/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Util.CollectAxioms
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
public import FloatLib.Floats.Formats.Block.Roundoff
public import FloatLib.Floats.Formats.Block.Stored
public import FloatLib.Tactic.Roundoff

/-!
# Block-scaled kernels bounded by `roundoff`

`roundoff` derives each statement below from the program alone.

* Block quantization: one element of any format whose element rounding has a registered budget,
  for every level structure, with NVFP4 and the fixed-point combine format as named instances. A
  budget may also be a hypothesis of the program, and an element format with no budget is
  rejected.
* Matrix products and dot products of block-quantized tensors, read at pair indices.
* Ordered accumulation in an accumulator format, and a narrow accumulator promoted to a wide one.
  The blocked dot product with rounded fused multiply-adds is that promotion, accumulation
  commutes with a scale of the format, and two orders differ by at most twice the bound.
* An NVFP4-weight, NVFP4-activation dot product accumulated in binary32.
* Kernels on stored words: FP8 products accumulated in a 14-bit accumulator and promoted to
  binary32, and the same partial sums scaled by the power-of-two block scales of OCP MX.
* An NVFP4 dot product on stored words in the order of NVIDIA's matrix product (the partial dot
  product of each block of 16, times the two block scales, accumulated in binary32), for any
  number of blocks, with the quantization of both operands as hypotheses. The hypotheses are
  discharged for words that hold the quantized elements of two NVFP4 tensors, FloatLib's cast
  from binary32 produces such words, and the codes of the stored NVFP4 format under any policy
  meet the hypotheses with no premise.

The checks are of the generated statements. They cover these programs, with tensor sizes as
written, and the first three statements hold for every level structure of the stated shape.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffBlock

open FloatLib.Floats FloatLib.Floats.Formats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics FloatLib.Floats.Formats.Block

/-! ## Block quantization -/

/-- One element under any scale levels: the relative error of E2M1, and its absolute error and
saturation threshold times the magnitude of the total scale. There is no premise. -/
roundoff mixed theorem element :=
  fun (levels : List (Level (Fin 4 × Fin 4) Unit ℝ)) (x : Fin 4 × Fin 4 → ℝ)
    (i : Fin 4 × Fin 4) =>
    (Format.mk (fun _ => Rounding.saturating .e2m1) levels).reconstruct x i

example (levels : List (Level (Fin 4 × Fin 4) Unit ℝ)) (x : Fin 4 × Fin 4 → ℝ)
    (i : Fin 4 × Fin 4) :=
  show MixedError _ (x i) (Model.unitRoundoffAt FloatFormat.e2m1)
    (|(Format.mk (fun _ => Rounding.saturating .e2m1) levels).scale x i| *
        Model.underflowErrorAt FloatFormat.e2m1 +
      max 0 (|x i| - |(Format.mk (fun _ => Rounding.saturating .e2m1) levels).scale x i| *
        Model.toReal (Model.posMaxFinite FloatFormat.e2m1))) from element levels x i

/-- NVFP4 on a tile, with the tensor scale and blocks of 16 along the rows. -/
roundoff mixed theorem nvfp4_element :=
  fun (x : Fin 16 × Fin 16 → ℝ) (i : Fin 16 × Fin 16) =>
    (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct x i

example (x : Fin 16 × Fin 16 → ℝ) (i : Fin 16 × Fin 16) :=
  show MixedError _ (x i) (Model.unitRoundoffAt FloatFormat.e2m1)
    (|(nvfp4 (tiles 0 0) (tiles 1 16)).scale x i| * Model.underflowErrorAt FloatFormat.e2m1 +
      max 0 (|x i| - |(nvfp4 (tiles 0 0) (tiles 1 16)).scale x i| *
        Model.toReal (Model.posMaxFinite FloatFormat.e2m1))) from nvfp4_element x i

/-- S2F6 in blocks of 32 with a power-of-two scale: fixed point has no relative error. -/
roundoff mixed theorem combine_element :=
  fun (x : Fin 4 × Fin 64 → ℝ) (i : Fin 4 × Fin 64) =>
    (combine 2 6 32 (Rounding.pow2Ceil (-127) 127) (127 / 64)).reconstruct x i

example (x : Fin 4 × Fin 64 → ℝ) (i : Fin 4 × Fin 64) :=
  show MixedError _ (x i) 0 _ from combine_element x i

/-- A budget supplied as a hypothesis covers an element format that has no registered one. -/
roundoff mixed theorem supplied_budget :=
  fun (F : Format (Fin 4) Unit ℝ) (u η M : ℝ)
    (_ : ∀ i, Rounding.HasBudget (F.element i) u η M) (x : Fin 4 → ℝ) (i : Fin 4) =>
    F.reconstruct x i

example (F : Format (Fin 4) Unit ℝ) (u η M : ℝ)
    (h : ∀ i, Rounding.HasBudget (F.element i) u η M) (x : Fin 4 → ℝ) (i : Fin 4) :=
  show MixedError _ (x i) u (|F.scale x i| * η + max 0 (|x i| - |F.scale x i| * M)) from
    supplied_budget F u η M h x i

/-- An element format without a budget is rejected: the rule does not apply, and the analysis
does not look inside the quantizer. -/
elab "#roundoff_rejects " program:term : command => do
  let command ← `(command| roundoff mixed theorem rejected := $program)
  let messages := (← get).messages
  Lean.Elab.Command.elabCommand command
  let failed := (← get).messages.hasErrors
  modify fun state => { state with messages }
  unless failed do
    throwError "roundoff accepted a program it should reject"

#roundoff_rejects
  fun (E : Rounding ℝ) (levels : List (Level (Fin 4) Unit ℝ)) (x : Fin 4 → ℝ) (i : Fin 4) =>
    (Format.mk (fun _ => E) levels).reconstruct x i

/-! ## Products of block-quantized tensors -/

/-- One entry of the product of an NVFP4 weight matrix, in blocks along its rows, and an NVFP4
activation matrix, in blocks along its columns. The reference is the exact entry. -/
roundoff mixed theorem matmul_entry :=
  fun (W : Fin 4 × Fin 32 → ℝ) (X : Fin 32 × Fin 8 → ℝ) (r : Fin 4) (c : Fin 8) =>
    ∑ j, (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct W (r, j) *
      (nvfp4 (tiles 0 0) (tiles 16 1)).reconstruct X (j, c)

example (W : Fin 4 × Fin 32 → ℝ) (X : Fin 32 × Fin 8 → ℝ) (r : Fin 4) (c : Fin 8) :=
  show MixedError _
    ((List.finRange 32).foldl (fun reference j => reference + W (r, j) * X (j, c)) 0) _ _ from
    matmul_entry W X r c

/-! ## Accumulation -/

/-- Ordered accumulation of given terms in binary32. -/
roundoff mixed theorem accumulated :=
  fun (terms : List ℝ) => accumulate (Rounding.grid .binary32) terms

example (terms : List ℝ) :=
  show MixedError _ (terms.foldl (fun reference term => reference + term) 0) 0
    (((1 + Model.unitRoundoffAt FloatFormat.binary32) ^ terms.length - 1) *
        (terms.map abs).sum +
      terms.length * (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ terms.length *
        Model.underflowErrorAt FloatFormat.binary32) from accumulated terms

/-- A 14-bit accumulator with the exponent range of binary32, the precision DeepSeek-V3 reports
for FP8 matrix products on its hardware. -/
def accumulator14 : FloatFormat where
  expWidth := 8
  fracWidth := 13
  exponentBias := 127
  encoding := .ieee
  exponentBias_pos := by decide
  exponentBias_le_maxFinite := by decide

/-- Chunks accumulated in the 14-bit format and promoted to binary32. -/
roundoff mixed theorem promoted :=
  fun (chunks : List (List ℝ)) =>
    accumulateChunked (Rounding.grid accumulator14) (Rounding.grid .binary32) chunks

example (chunks : List (List ℝ)) :=
  show MixedError _ _ 0
    (((1 + Model.unitRoundoffAt FloatFormat.binary32) ^ chunks.length *
          (1 + Model.unitRoundoffAt accumulator14) ^ chunkBound chunks - 1) *
        (chunks.map fun chunk => (chunk.map abs).sum).sum +
      chunks.length * (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ chunks.length *
        (chunkBound chunks * (1 + Model.unitRoundoffAt accumulator14) ^ chunkBound chunks *
            Model.underflowErrorAt accumulator14 +
          Model.underflowErrorAt FloatFormat.binary32)) from promoted chunks

/-- The blocked dot product with fused multiply-adds in the 14-bit accumulator and block
partials added in binary32, in blocks of 128 terms, is that promotion: the same bound, against
the exact dot product, for every length. -/
example (a b : ℕ → ℝ) (n : ℕ) :
    |BlockedDot.kernelEntry (fun x y z => (Rounding.grid accumulator14).round (x * y + z))
          (fun x y => (Rounding.grid .binary32).round (x + y)) 0 a b 128 n (some 0) -
        ∑ k ∈ Finset.range n, a k * b k| ≤
      ((1 + Model.unitRoundoffAt FloatFormat.binary32) ^ BlockedDot.blockCount 128 n *
            (1 + Model.unitRoundoffAt accumulator14) ^ 128 - 1) *
          ∑ k ∈ Finset.range n, |a k * b k| +
        BlockedDot.blockCount 128 n *
            (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ BlockedDot.blockCount 128 n *
          (((128 : ℕ) : ℝ) * (1 + Model.unitRoundoffAt accumulator14) ^ 128 *
              Model.underflowErrorAt accumulator14 +
            Model.underflowErrorAt FloatFormat.binary32) :=
  abs_kernelEntry_sub_le (N := Rounding.grid accumulator14) (W := Rounding.grid .binary32)
    (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le
    (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le
    (Model.abs_roundAt_sub_le_unitRoundoffAt _) (Model.abs_roundAt_sub_le_unitRoundoffAt _)
    a b (by decide) n

/-- Accumulating terms scaled by a block scale of eight in binary32 scaled by eight is the
accumulation in binary32, scaled. -/
example (terms : List ℝ) :
    accumulate ((Rounding.grid .binary32).scaled 8) (terms.map (· * 8)) =
      accumulate (Rounding.grid .binary32) terms * 8 :=
  accumulate_scaled _ (by norm_num) terms

/-- Accumulating in binary32 from the last term to the first changes the result by at most twice
the accumulation bound. -/
example (terms : List ℝ) :
    |accumulate (Rounding.grid .binary32) terms -
        accumulate (Rounding.grid .binary32) terms.reverse| ≤
      2 * (((1 + Model.unitRoundoffAt FloatFormat.binary32) ^ terms.length - 1) *
          (terms.map abs).sum +
        terms.length * (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ terms.length *
          Model.underflowErrorAt FloatFormat.binary32) :=
  abs_accumulate_sub_accumulate_le_of_perm (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le (Model.abs_roundAt_sub_le_unitRoundoffAt _)
    (List.reverse_perm terms).symm

/-- A dot product of an NVFP4 weight row and an NVFP4 activation row, accumulated in binary32.
The reference is the exact dot product of the inputs, so the bound has the quantization error of
both operands and the accumulation error. -/
roundoff mixed theorem linear :=
  fun (w x : Fin 2 × Fin 32 → ℝ) (r : Fin 2) =>
    accumulate (Rounding.grid .binary32)
      ((List.finRange 32).map fun j => (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct w (r, j) *
        (nvfp4 (tiles 0 0) (tiles 1 16)).reconstruct x (r, j))

example (w x : Fin 2 × Fin 32 → ℝ) (r : Fin 2) :=
  show MixedError _
    ((List.finRange 32).foldl (fun reference j => reference + w (r, j) * x (r, j)) 0) _ _ from
    linear w x r

/-! ## Kernels on stored words -/

/-- FP8 products accumulated in the 14-bit accumulator and promoted to binary32 once per chunk.
The products and the promotion are exact, and each addition rounds once. -/
roundoff mixed theorem promoted_dot :=
  fun (chunks : List (List (Model FloatFormat.e4m3 × Model FloatFormat.e4m3))) =>
    Model.toReal (chunks.foldl (fun wide chunk => Model.add wide
      (Model.cast accumulator14 FloatFormat.binary32 (chunk.foldl (fun narrow pair =>
        Model.add narrow (Model.mul (Model.cast _ accumulator14 pair.1)
          (Model.cast _ accumulator14 pair.2))) (Model.zero _ false))))
      (Model.zero _ false))

/-- An OCP MX dot product on stored words: the partial dot product of each block in the 14-bit
accumulator, promoted to binary32, multiplied by the two power-of-two block scales and added. -/
roundoff mixed theorem mx_block_dot :=
  fun (blocks : List ((ℤ × ℤ) × List (Model FloatFormat.e4m3 × Model FloatFormat.e4m3))) =>
    Model.toReal (blocks.foldl (fun wide block => Model.add wide
      (Model.scale (Model.cast accumulator14 FloatFormat.binary32 (block.2.foldl
        (fun narrow pair => Model.add narrow (Model.mul (Model.cast _ accumulator14 pair.1)
          (Model.cast _ accumulator14 pair.2))) (Model.zero _ false)))
        (block.1.1 + block.1.2)))
      (Model.zero _ false))

example (blocks : List ((ℤ × ℤ) × List (Model FloatFormat.e4m3 × Model FloatFormat.e4m3))) :=
  show _ → MixedError _
    (blocks.foldl (fun reference block => reference +
      block.2.foldl (fun reference pair => reference + pair.1.toReal * pair.2.toReal) 0 *
        (2 : ℝ) ^ ((block.1.1 + block.1.2 : ℤ) : ℝ)) 0) _ _ from mx_block_dot blocks

/-- An NVFP4 dot product on stored words, in the order of NVIDIA's matrix product
(arXiv:2509.25149, appendix B.3): the partial dot product of the E2M1 elements of each block of
16, multiplied by the product of the two E4M3 block scales, and the results added, all in
binary32. `hw` and `hx` state how the stored elements approximate exact scaled inputs `w`, `x`.
The reference is `∑ b, (∑ j, w (b, j) * x (b, j)) * (sw b * sx b)`. -/
roundoff mixed theorem nvfp4_block_dot :=
  fun (m : ℕ) (ew ex : Fin m × Fin 16 → Model FloatFormat.e2m1)
    (sw sx : Fin m → Model FloatFormat.e4m3) (uw ux : ℝ) (w x aw ax : Fin m × Fin 16 → ℝ)
    (hw : ∀ i, MixedError (Model.toReal (ew i)) (w i) uw (aw i))
    (hx : ∀ i, MixedError (Model.toReal (ex i)) (x i) ux (ax i)) =>
    Model.toReal ((List.finRange m).foldl (fun wide b => Model.add wide
      (Model.mul
        ((List.finRange 16).foldl (fun part j => Model.add part
          (Model.mul (Model.cast _ FloatFormat.binary32 (ew (b, j)))
            (Model.cast _ FloatFormat.binary32 (ex (b, j))))) (Model.zero _ false))
        (Model.mul (Model.cast _ FloatFormat.binary32 (sw b))
          (Model.cast _ FloatFormat.binary32 (sx b)))))
      (Model.zero _ false))

/-- Words that hold the quantized elements of two NVFP4 tensors meet the hypotheses with E2M1's
budget (`Format.quantize_mixedError`), so the reference is the same sum over the exact scaled
inputs of the two tensors. For every number of blocks and all data. -/
example (m : ℕ) (w x : Fin m × Fin 16 → ℝ) (ew ex : Fin m × Fin 16 → Model FloatFormat.e2m1)
    (sw sx : Fin m → Model FloatFormat.e4m3)
    (hew : ∀ i, Model.toReal (ew i) = (nvfp4 (tiles 0 0) (tiles 1 16)).quantize w i)
    (hex : ∀ i, Model.toReal (ex i) = (nvfp4 (tiles 0 0) (tiles 1 16)).quantize x i) :=
  show _ → MixedError _
    ((List.finRange m).foldl (fun reference b => reference +
      (List.finRange 16).foldl (fun reference j => reference +
        (nvfp4 (tiles 0 0) (tiles 1 16)).normalized w (b, j) *
          (nvfp4 (tiles 0 0) (tiles 1 16)).normalized x (b, j)) 0 *
        ((sw b).toReal * (sx b).toReal)) 0) _ _ from
    nvfp4_block_dot m ew ex sw sx _ _ _ _ _ _
      (fun i => hew i ▸ Format.quantize_mixedError (nvfp4 (tiles 0 0) (tiles 1 16)) w i)
      (fun i => hex i ▸ Format.quantize_mixedError (nvfp4 (tiles 0 0) (tiles 1 16)) x i)

/-- FloatLib's cast produces such words: converting a finite binary32 value that holds the exact
scaled input stores the quantized element of the block format. -/
example (m : ℕ) (w : Fin m × Fin 16 → ℝ) (i : Fin m × Fin 16) (v : Model FloatFormat.binary32)
    (hv : Model.isFinite v = true)
    (hq : Model.isFinite (Model.cast _ FloatFormat.e2m1 v) = true)
    (hscaled : Model.toReal v = (nvfp4 (tiles 0 0) (tiles 1 16)).normalized w i) :
    Model.toReal (Model.cast _ FloatFormat.e2m1 v) =
      (nvfp4 (tiles 0 0) (tiles 1 16)).quantize w i := by
  rw [Rounding.toReal_cast_eq_ofFormat v hv hq, hscaled]
  rfl

/-- The same kernel on the codes of FloatLib's stored NVFP4 format. For two rational tensors
quantized by the executable quantizer under any two policies, the element words are the binary
words of the stored codes, and they meet the hypotheses with E2M1's budget
(`Profile.encode_mixedError`), so there is no hypothesis left on the elements. The reference is
the same sum over the exact inputs divided by their stored total scales. For every number of
blocks, all data and every policy. -/
example (m : ℕ) (xw xx : Fin m × Fin 16 → SignedRat)
    (pw px : Policy (Fin m × Fin 16) (ℕ × ℕ)) (sw sx : Fin m → Model FloatFormat.e4m3) :=
  nvfp4_block_dot m
    (fun i => Model.ofNatBits
      (((nvfp4Stored (tiles 0 0) (tiles 1 16)).quantize pw xw).elements i).toNat)
    (fun i => Model.ofNatBits
      (((nvfp4Stored (tiles 0 0) (tiles 1 16)).quantize px xx).elements i).toNat)
    sw sx _ _ _ _ _ _
    (fun _ => OCP.MX.Standard.Profile.encode_mixedError .e2m1 rfl _)
    (fun _ => OCP.MX.Standard.Profile.encode_mixedError .e2m1 rfl _)

-- The generated statements and the rules behind them depend on the three standard axioms only.
run_cmd do
  for name in [``Format.reconstruct_mixedError, ``accumulate_mixedError,
      ``accumulateChunked_mixedError, ``element, ``nvfp4_element, ``combine_element,
      ``supplied_budget, ``matmul_entry, ``accumulated, ``promoted, ``linear, ``promoted_dot,
      ``mx_block_dot, ``nvfp4_block_dot, ``Format.quantize_mixedError,
      ``OCP.MX.Standard.Profile.encode_mixedError,
      ``OCP.MX.Standard.Profile.toReal_ofNatBits] do
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unexpected axiom {dependency}"

end FloatLibTests.Conformance.BinaryInterchange.RoundoffBlock
