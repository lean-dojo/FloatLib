/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Proof.Certificate
public import FloatLib.Floats.Formats.FiniteOnly
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Instances
public import FloatLib.Floats.Formats.OCP
public import FloatLib.Floats.Formats.Posit

/-!
# Complete backend-certificate audit

This module asks Lean to construct the six-operation `FullArithmeticCertificate` at every public
binary execution boundary:

* arbitrary descriptor-backed binary formats;
* every static-byte OCP and FNUZ family; and
* representative Posit Standard widths spanning byte, native-word, fixed-pair, and
  arbitrary-precision carriers.

A certificate is more than a test result. Its fields are the `run = spec` equations that the
operation typeclasses require, so a missing backend refinement stops this module from compiling.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Execution.Certificates

open FloatLib.Floats
open FloatLib.Floats.ExecFloat.Proof
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.OCP.MX

universe u

/-- Every arbitrary binary descriptor has all six certified selected backends. -/
theorem descriptor
    (format : FloatFormat) :
    FullArithmeticCertificate (Descriptor format) :=
  fullArithmeticCertificate (Descriptor format)

/-- Every registered static-byte family has all six certified selected backends. -/
theorem staticByte
    (F : Type u) [StaticByte.Family F] :
    FullArithmeticCertificate F :=
  fullArithmeticCertificate F

/-
Concrete witnesses make accidental loss of any public family registration a compile error. The
generic `staticByte` theorem proves the mathematics; these declarations audit the exported names.
-/

theorem ocpE4M3FN : FullArithmeticCertificate E4M3FN.Family :=
  fullArithmeticCertificate E4M3FN.Family

theorem ocpE5M2 : FullArithmeticCertificate E5M2.Family :=
  fullArithmeticCertificate E5M2.Family

theorem ocpE2M1 : FullArithmeticCertificate E2M1.Family :=
  fullArithmeticCertificate E2M1.Family

theorem ocpE2M3 : FullArithmeticCertificate E2M3.Family :=
  fullArithmeticCertificate E2M3.Family

theorem ocpE3M2 : FullArithmeticCertificate E3M2.Family :=
  fullArithmeticCertificate E3M2.Family

theorem onnxe4m3fnuz : FullArithmeticCertificate E4M3FNUZ.Family :=
  fullArithmeticCertificate E4M3FNUZ.Family

theorem onnxe5m2fnuz : FullArithmeticCertificate E5M2FNUZ.Family :=
  fullArithmeticCertificate E5M2FNUZ.Family

/-!
These concrete posit witnesses cover both sides of every storage boundary. The generic format
proof lives with the posit conformance theory. These declarations check that public type-directed
instance synthesis reaches a complete selected-backend certificate without a separately
registered family for any width.
-/

theorem posit2 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 2) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 2)

theorem posit8 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 8) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 8)

theorem posit9 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 9) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 9)

theorem posit16 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 16) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 16)

theorem posit17 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 17) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 17)

theorem posit32 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 32) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 32)

theorem posit33 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 33) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 33)

theorem posit64 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 64) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 64)

theorem posit65 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 65) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 65)

theorem posit128 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 128) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 128)

theorem posit129 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 129) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 129)

theorem posit256 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 256) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 256)

theorem posit4096 :
    FullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 4096) :=
  fullArithmeticCertificate (FloatLib.Floats.ExecFloat.Posit.Family 4096)

end FloatLibTests.Conformance.Execution.Certificates
