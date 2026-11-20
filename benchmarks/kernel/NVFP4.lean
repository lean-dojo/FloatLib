/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

import FloatLib.Floats.Formats.Block
import FloatLib.Floats.Formats.Block.Configured
import FloatLib.Floats.Formats.Block.Stored
import FloatLib.Floats.Formats.Block.CodedDot
import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath
import FloatLib.Tactic.KernelCost
import FloatLib.Tactic.KernelEval

/-!
NVIDIA, arXiv:2509.25149v2, Appendix B.1–B.3: kernel observations under exact arithmetic.
Quantization includes its input construction. The dot and decode inputs are literal stored
codes, so those timings exclude quantization. These differ from the native corpus harness.

The rows `NVFP4_WORKING` time `Block.nvfp4Working`, the quantizer on binary32 encodings in the
order of torchao's `nvfp4_quantize`: one element, the scale of a block of 16, and all 17 words of
the block (their sum is observed, so that the kernel computes each one).
-/

open FloatLib.Numerics FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange

private def format : Block.CodedFormat (Fin 16) Unit :=
  Block.nvfp4Stored (fun _ => ()) (fun _ => ())

private def policy : Block.Policy (Fin 16) Unit :=
  Block.nvfp4Supplied (fun _ => ()) (fun _ => 1)

private def inputs (i : Fin 16) : SignedRat :=
  SignedRat.ofRat (mkRat ((i.val : Int) - 8) 7)

private def tensor : Block.Tensor format where
  scales := ((fun _ => Model.ofNatBits 0x3f800000), (fun _ => BitVec.ofNat 8 56), ())
  elements _ := BitVec.ofNat 4 2

#print "NVFP4_KERNEL quantize-element n=16"
#kernel_cost rewritten (((format.quantize policy inputs).elements 2).toNat)
#print "NVFP4_KERNEL quantize-scales n=16"
#kernel_cost rewritten (((format.quantize policy inputs).scales.2.1 ()).toNat)
#print "NVFP4_KERNEL decode-element n=16"
#kernel_cost rewritten (Block.finiteValue (tensor.decode 2)).num.natAbs
#print "NVFP4_KERNEL Dot n=16"
#kernel_cost rewritten (OCP.MX.Dot .binary32 tensor tensor (List.finRange 16)).toNatBits
#print "NVFP4_KERNEL DotGeneral n=16"
#kernel_cost rewritten
  (OCP.MX.DotGeneral .binary32 tensor tensor [List.finRange 16]).toNatBits

private def word (bits : Nat) : Model FloatFormat.binary32 :=
  Model.ofNatBits bits

private def ramp : List (Model FloatFormat.binary32) :=
  [0x3F800000, 0x40000000, 0x40400000, 0x40800000, 0x40A00000, 0x40C00000, 0x40E00000,
    0x41000000, 0xBF800000, 0xC0000000, 0xC0400000, 0xC0800000, 0xC0A00000, 0xC0C00000,
    0xC0E00000, 0xC1000000].map word

#print "NVFP4_WORKING element n=1"
#kernel_cost (Block.nvfp4Working.element (word 0x3E800000) (word 0x40400000)).toNatBits
#print "NVFP4_WORKING scale n=16"
#kernel_cost (Block.nvfp4Working.scale (word 0x3F800000) ramp).toNatBits
#print "NVFP4_WORKING block n=16"
#kernel_cost
  (Block.nvfp4Working.words (word 0x3F800000) ramp).2.foldl Nat.add
    (Block.nvfp4Working.words (word 0x3F800000) ramp).1
