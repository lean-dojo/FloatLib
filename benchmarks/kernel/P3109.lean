/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

import FloatLib.Floats.Formats.P3109.KernelPath.Rules
import FloatLib.Tactic.KernelCost

/-!
P3109 operations in Lean's kernel.

Each row is one public operation of P3109 Interim Report v4.1 (unapproved draft), §§4.10 to
4.13 and 4.16, on fixed encodings: of Binary8p4se, and of the signed extended format of sixteen
bits with precision eight. `#kernel_cost` prints the time of the term as it is written and the
time after the rules tagged `@[kernel_optimize]`, which evaluate the flat operations of
`P3109.KernelPath.Flat` on the encodings.
-/

open FloatLib.Floats FloatLib.Floats.ExecFloat FloatLib.Floats.Formats.P3109

/-- The report's Binary8p4se. -/
abbrev B8 := ExecFloat.P3109 .binary8p4se
/-- A signed extended format of sixteen bits with precision eight. -/
abbrev B16 := ExecFloat.P3109 (Formats.P3109.Format.signed 16 8 .extended)

/-- An operand of Binary8p4se. -/
def a : B8 := ExecFloat.P3109.ofNatBits 68
/-- An operand of Binary8p4se. -/
def b : B8 := ExecFloat.P3109.ofNatBits 70
/-- An operand of Binary8p4se. -/
def c : B8 := ExecFloat.P3109.ofNatBits 60
/-- An operand of the sixteen-bit format. -/
def u : B16 := ExecFloat.P3109.ofNatBits 0x4155
/-- An operand of the sixteen-bit format. -/
def v : B16 := ExecFloat.P3109.ofNatBits 0x3eaa
/-- An operand of the sixteen-bit format. -/
def w : B16 := ExecFloat.P3109.ofNatBits 0x3c33

#print "P3109 Add binary8p4se"
#kernel_cost (ExecFloat.P3109.Add a b).toNatBits
#print "P3109 Multiply binary8p4se"
#kernel_cost (ExecFloat.P3109.Multiply a b).toNatBits
#print "P3109 Divide binary8p4se"
#kernel_cost (ExecFloat.P3109.Divide a b).toNatBits
#print "P3109 FMA binary8p4se"
#kernel_cost (ExecFloat.P3109.FMA a b c).toNatBits
#print "P3109 FAA binary8p4se"
#kernel_cost (ExecFloat.P3109.FAA a b c).toNatBits
#print "P3109 Recip binary8p4se"
#kernel_cost (ExecFloat.P3109.Recip a).toNatBits
#print "P3109 CopySign binary8p4se"
#kernel_cost (ExecFloat.P3109.CopySign a b).toNatBits
#print "P3109 Sqrt binary8p4se"
#kernel_cost (ExecFloat.P3109.Sqrt a).toNatBits
#print "P3109 Sqrt binary8p4se stochasticC"
#kernel_cost (ExecFloat.P3109.Sqrt a .binary8p4se (.stochasticC (.ofNat 3 5))).toNatBits
#print "P3109 RSqrt binary8p4se"
#kernel_cost (ExecFloat.P3109.RSqrt a).toNatBits
#print "P3109 Hypot binary8p4se"
#kernel_cost (ExecFloat.P3109.Hypot a b).toNatBits
#print "P3109 Minimum binary8p4se"
#kernel_cost (ExecFloat.P3109.Minimum a b).toNatBits
#print "P3109 MaximumMagnitudeNumber binary8p4se"
#kernel_cost (ExecFloat.P3109.MaximumMagnitudeNumber a b).toNatBits
#print "P3109 MinimumFinite binary8p4se"
#kernel_cost (ExecFloat.P3109.MinimumFinite a b).toNatBits
#print "P3109 Clamp binary8p4se"
#kernel_cost (ExecFloat.P3109.Clamp a c b).toNatBits
#print "P3109 CompareLess binary8p4se"
#kernel_cost ExecFloat.P3109.CompareLess a b
#print "P3109 CompareEqual binary8p4se"
#kernel_cost ExecFloat.P3109.CompareEqual a b
#print "P3109 CompareGreaterEqual binary8p4se"
#kernel_cost ExecFloat.P3109.CompareGreaterEqual a b
#print "P3109 compare binary8p4se"
#kernel_cost ExecFloat.P3109.compare a b
#print "P3109 IsNaN binary8p4se"
#kernel_cost ExecFloat.P3109.IsNaN a
#print "P3109 IsFinite binary8p4se"
#kernel_cost ExecFloat.P3109.IsFinite a
#print "P3109 IsOne binary8p4se"
#kernel_cost ExecFloat.P3109.IsOne a
#print "P3109 IsNormal binary8p4se"
#kernel_cost ExecFloat.P3109.IsNormal a
#print "P3109 NextGreaterThan binary8p4se"
#kernel_cost (ExecFloat.P3109.NextGreaterThan a).toNatBits

#print "P3109 Add 16p8"
#kernel_cost (ExecFloat.P3109.Add u v).toNatBits
#print "P3109 FAA 16p8"
#kernel_cost (ExecFloat.P3109.FAA u v w).toNatBits
#print "P3109 Recip 16p8"
#kernel_cost (ExecFloat.P3109.Recip u).toNatBits
#print "P3109 Sqrt 16p8"
#kernel_cost (ExecFloat.P3109.Sqrt u).toNatBits
#print "P3109 RSqrt 16p8"
#kernel_cost (ExecFloat.P3109.RSqrt u).toNatBits
#print "P3109 Hypot 16p8"
#kernel_cost (ExecFloat.P3109.Hypot u v).toNatBits
#print "P3109 MaximumMagnitudeNumber 16p8"
#kernel_cost (ExecFloat.P3109.MaximumMagnitudeNumber u v).toNatBits
#print "P3109 Clamp 16p8"
#kernel_cost (ExecFloat.P3109.Clamp u w v).toNatBits
#print "P3109 CompareLess 16p8"
#kernel_cost ExecFloat.P3109.CompareLess u v
#print "P3109 IsOne 16p8"
#kernel_cost ExecFloat.P3109.IsOne u

#print "P3109 Mixed.Convert binary32 to binary8p4se"
#kernel_cost (Arithmetic.Mixed.Convert (Arithmetic.Destination.p3109 .binary8p4se)
  (Formats.BinaryInterchange.Model.ofNatBits 0x3FD9999A :
    Formats.BinaryInterchange.Model .binary32)).toNatBits
#print "P3109 Mixed.Convert binary64 to 16p8, rounded up, saturated"
#kernel_cost (Arithmetic.Mixed.Convert
  (Arithmetic.Destination.p3109 (Formats.P3109.Format.signed 16 8 .extended))
  (Formats.BinaryInterchange.Model.ofNatBits 0xBEF81E03F705857B :
    Formats.BinaryInterchange.Model .binary64) .up .finite).toNatBits

/-- `1.7` in binary32. -/
def single : Formats.BinaryInterchange.Model .binary32 :=
  Formats.BinaryInterchange.Model.ofNatBits 0x3FD9999A
/-- `-2.3e-5` in binary64. -/
def double : Formats.BinaryInterchange.Model .binary64 :=
  Formats.BinaryInterchange.Model.ofNatBits 0xBEF81E03F705857B

#print "P3109 Mixed.Add binary32 + binary8p4se"
#kernel_cost (Arithmetic.Mixed.Add (Arithmetic.Destination.p3109 .binary8p4se) single a).toNatBits
#print "P3109 Mixed.Multiply binary8p4se * rational"
#kernel_cost (Arithmetic.Mixed.Multiply (Arithmetic.Destination.p3109 .binary8p4se) a
  (3 / 4 : Rat)).toNatBits
#print "P3109 Mixed.Divide binary8p4se / binary32"
#kernel_cost (Arithmetic.Mixed.Divide (Arithmetic.Destination.p3109 .binary8p4se) a
  single).toNatBits
#print "P3109 Mixed.FMA binary32 * binary8p4se + binary64"
#kernel_cost (Arithmetic.Mixed.FMA (Arithmetic.Destination.p3109 .binary8p4se) single a
  double).toNatBits
#print "P3109 Mixed.FAA binary32 + binary8p4se + binary64"
#kernel_cost (Arithmetic.Mixed.FAA (Arithmetic.Destination.p3109 .binary8p4se) single a
  double).toNatBits
