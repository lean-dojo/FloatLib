/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath
import FloatLib.Floats.Formats.Block.CodedDot
import FloatLib.Tactic.KernelCost
import FloatLib.Tactic.KernelEval

/-!
OCP MX v1.0, §§5.3 and 6.1–6.3. Tagged kernel timings include construction of the
displayed exact input. These are kernel observations, not compiled throughput measurements.
-/

open FloatLib.Numerics FloatLib.Floats.Formats
open OCP.MX.Standard

#print "MX_KERNEL e5m2 finite"
#kernel_cost rewritten (Element.quantizeFinite .e5m2 (SignedRat.ofRat (7 / 3))).toNat
#print "MX_KERNEL e4m3 finite"
#kernel_cost rewritten (Element.quantizeFinite .e4m3 (SignedRat.ofRat (7 / 3))).toNat
#print "MX_KERNEL e3m2 finite"
#kernel_cost rewritten (Element.quantizeFinite .e3m2 (SignedRat.ofRat (7 / 3))).toNat
#print "MX_KERNEL e2m3 finite"
#kernel_cost rewritten (Element.quantizeFinite .e2m3 (SignedRat.ofRat (7 / 3))).toNat
#print "MX_KERNEL e2m1 finite"
#kernel_cost rewritten (Element.quantizeFinite .e2m1 (SignedRat.ofRat (7 / 3))).toNat
#print "MX_KERNEL int8 finite"
#kernel_cost rewritten (Element.quantizeFinite .int8 (SignedRat.ofRat (7 / 3))).toNat

private def inputs : Fin 32 → SignedRat :=
  fun i => SignedRat.ofRat (((i.val : Rat) + 1) * 7 / 3)

#print "MX_KERNEL e4m3 block32 element"
#kernel_cost rewritten (((format (fun _ : Fin 32 => ()) .e4m3).quantize
  (policy (fun _ : Fin 32 => ()) .e4m3) inputs).elements 2).toNat
