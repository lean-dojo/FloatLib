/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import FloatLib
import FloatLib.Tactic.KernelCost
import FloatLib.Tactic.KernelEval

/-!
# Kernel time of one operation in the formats that are not binary interchange formats

Each `#kernel_cost` line prints the median kernel time of one evaluation of the term as written
and after the rewrite of `float_decide` with the rules tagged `@[kernel_optimize]`. The operands
are built from stored codes, so that the time is the operation and not the rounding of a
literal. `benchmarks/suite/run.sh families` turns the output into a table. A label line
precedes each measurement.
-/

open FloatLib.Floats FloatLib.Numerics FloatLib.Floats.ExecFloat FloatLib.Floats.Formats

/-- Binary fixed point with eight fractional bits. -/
abbrev Q8 := ExecFloat.FixedPoint binaryRadix 8
/-- Powers of ten with a sign. -/
abbrev L10 := ExecFloat.Logarithmic decimalRadix
/-- The P3109 report's Binary8p4se. -/
abbrev B8P4 := ExecFloat.P3109 .binary8p4se

#print "KCOST fixed-point(2,8) add"
#kernel_cost (ExecFloat.FixedPoint.coefficient ((ExecFloat.FixedPoint.ofCoefficient 12345 : Q8) + ExecFloat.FixedPoint.ofCoefficient (-777))).toNat
#print "KCOST fixed-point(2,8) sub"
#kernel_cost (ExecFloat.FixedPoint.coefficient ((ExecFloat.FixedPoint.ofCoefficient 12345 : Q8) - ExecFloat.FixedPoint.ofCoefficient (-777))).toNat
#print "KCOST logarithmic(10) mul"
#kernel_cost decide (ExecFloat.Logarithmic.toCode ((.ofExponent 2 : L10) * .ofExponent (-1) (negative := true)) = .value true 1)

#print "KCOST p3109-binary8p4se add"
#kernel_cost ((ExecFloat.P3109.ofNatBits 68 : B8P4) + ExecFloat.P3109.ofNatBits 70).toNatBits
#print "KCOST p3109-binary8p4se mul"
#kernel_cost ((ExecFloat.P3109.ofNatBits 68 : B8P4) * ExecFloat.P3109.ofNatBits 70).toNatBits
#print "KCOST p3109-binary8p4se div"
#kernel_cost ((ExecFloat.P3109.ofNatBits 68 : B8P4) / ExecFloat.P3109.ofNatBits 70).toNatBits

#print "KCOST posit8 add"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C : Posit8) + ExecFloat.Posit.ofNatBits 0x52)
#print "KCOST posit8 mul"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C : Posit8) * ExecFloat.Posit.ofNatBits 0x52)
#print "KCOST posit8 div"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C : Posit8) / ExecFloat.Posit.ofNatBits 0x52)
#print "KCOST posit16 add"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C00 : Posit16) + ExecFloat.Posit.ofNatBits 0x5200)
#print "KCOST posit16 mul"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C00 : Posit16) * ExecFloat.Posit.ofNatBits 0x5200)
#print "KCOST posit32 add"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C000000 : Posit32) + ExecFloat.Posit.ofNatBits 0x52000000)
#print "KCOST posit32 mul"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C000000 : Posit32) * ExecFloat.Posit.ofNatBits 0x52000000)
#print "KCOST posit32 div"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C000000 : Posit32) / ExecFloat.Posit.ofNatBits 0x52000000)
#print "KCOST posit64 add"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C00000000000000 : Posit64) + ExecFloat.Posit.ofNatBits 0x5200000000000000)
#print "KCOST posit64 mul"
#kernel_cost ExecFloat.Posit.toNatBits ((ExecFloat.Posit.ofNatBits 0x4C00000000000000 : Posit64) * ExecFloat.Posit.ofNatBits 0x5200000000000000)

/-- Three in posit16. -/
abbrev positThree : Posit16 := ExecFloat.Posit.ofNatBits 0x4C00
/-- Five in posit16. -/
abbrev positFive : Posit16 := ExecFloat.Posit.ofNatBits 0x5200

#print "KCOST posit16 quire 3 + 3 * 5, rounded"
#kernel_cost ExecFloat.Posit.toNatBits (ExecFloat.Posit.Quire.qToP (ExecFloat.Posit.Quire.qMulAdd (ExecFloat.Posit.Quire.pToQ positThree) positThree positFive) : Posit16)

#print "KCOST posit32 literal 0.1"
#kernel_cost ExecFloat.Posit.toNatBits (0.1 : Posit32)
#print "KCOST posit16 literals 1.5 + 2.25"
#kernel_cost ExecFloat.Posit.toNatBits ((1.5 : Posit16) + 2.25)

open DecimalInterchange in
#print "KCOST decimal32 add"
open DecimalInterchange in
#kernel_cost decide ((Arithmetic.add .decimal32 .nearest (.finite false 12345 (-2)) (.finite false 67 0)).1 = .finite false 19045 (-2))
open DecimalInterchange in
#print "KCOST decimal64 add"
open DecimalInterchange in
#kernel_cost decide ((Arithmetic.add .decimal64 .nearest (.finite false 12345 (-2)) (.finite false 67 0)).1 = .finite false 19045 (-2))
open DecimalInterchange in
#print "KCOST decimal64 mul"
open DecimalInterchange in
#kernel_cost decide ((Arithmetic.mul .decimal64 .nearest (.finite false 12345 (-2)) (.finite false 67 0)).1 = .finite false 827115 (-2))
open DecimalInterchange in
#print "KCOST decimal64 add-rounded"
open DecimalInterchange in
#kernel_cost decide ((Arithmetic.add .decimal64 .nearest (.finite false 1234567890123456 (-2)) (.finite false 6700000000000007 5)).1 = .finite false 0 0)
open DecimalInterchange in
#print "KCOST decimal128 add"
open DecimalInterchange in
#kernel_cost decide ((Arithmetic.add .decimal128 .nearest (.finite false 12345 (-2)) (.finite false 67 0)).1 = .finite false 19045 (-2))

open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-e2m1 quantize"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost (Element.quantize .e2m1 (.finite (SignedRat.ofRat (7/3))) .saturate).toNat
open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-e2m3 quantize"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost (Element.quantize .e2m3 (.finite (SignedRat.ofRat (7/3))) .saturate).toNat
open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-e4m3 quantize"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost (Element.quantize .e4m3 (.finite (SignedRat.ofRat (7/3))) .saturate).toNat
open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-e5m2 quantize"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost (Element.quantize .e5m2 (.finite (SignedRat.ofRat (7/3))) .saturate).toNat
open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-int8 quantize"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost (Element.quantize .int8 (.finite (SignedRat.ofRat (7/3))) .saturate).toNat

/-- Four inputs that share one block. -/
def blockInputs : Fin 4 → SignedRat := fun i => SignedRat.ofRat (((i.val : Rat) + 1) * 7 / 3)

open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-e4m3 block of 4, one element"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost (((format (fun _ : Fin 4 => ()) .e4m3).quantize (policy (fun _ : Fin 4 => ()) .e4m3) blockInputs).elements 2).toNat

/-- Thirty-two inputs that share one block. -/
def wideBlockInputs : Fin 32 → SignedRat := fun i => SignedRat.ofRat (((i.val : Rat) + 1) * 7 / 3)

open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-e4m3 block of 32, one element"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost (((format (fun _ : Fin 32 => ()) .e4m3).quantize (policy (fun _ : Fin 32 => ()) .e4m3) wideBlockInputs).elements 2).toNat

open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-e4m3 dequantize (value of a word, compared with 9/4)"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost decide (Block.finiteValue (Element.decode (profile := .e4m3) (BitVec.ofNat 8 65)) = 9 / 4)

open FloatLib.Floats.Formats.OCP.MX Standard in
#print "KCOST mx-e4m3 block of 4, scale (compared with 1/32)"
open FloatLib.Floats.Formats.OCP.MX Standard in
#kernel_cost decide ((((format (fun _ : Fin 4 => ()) .e4m3).toFormat (policy (fun _ : Fin 4 => ()) .e4m3)).scale (fun j => (blockInputs j).value) 2) = 1 / 32)
