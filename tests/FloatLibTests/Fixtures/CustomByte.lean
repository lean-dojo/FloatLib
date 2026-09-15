/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Declaration
public import FloatLib.Floats.ExecFloat.Core.Operations

/-!
# Custom byte format used by planner checks

`TestByte` is a deliberately small user-defined format with several independently named,
certified addition kernels. Their cost estimates expose cold-start, steady-state, and memory
selection behavior without tying planner tests or code-generation probes to a built-in format.
-/

@[expose] public section

namespace FloatLibTests.Fixtures.CustomByte

open FloatLib.Numerics

float_format TestByte where
  Code := UInt8
  Scalar := UInt8
  denote := fun code => .finite code

/-- Reference addition for the custom direct-byte format. -/
def addSpec
    (left _right : FloatLib.Floats.ExecFloat TestByte) :
    FloatLib.Floats.ExecFloat TestByte :=
  left

/-- Independently named fast kernel used to exercise custom-format planning. -/
@[inline] def addFast
    (left _right : FloatLib.Floats.ExecFloat TestByte) :
    FloatLib.Floats.ExecFloat TestByte :=
  left

/--
The candidate portfolio deliberately exposes a cold-versus-warm crossover and an inadmissible
resident-memory choice. Every candidate executes the same proved function; only its engineering
estimate differs.
-/
instance [FloatLib.Floats.ExecFloat.Backend.PolicyFor TestByte] :
    FloatLib.Floats.ExecFloat.Add TestByte where
  spec := addSpec
  candidates := {
    alternatives := [
      FloatLib.Floats.ExecFloat.Backend.Certified.binary
        { name := "custom TestByte oversized table"
          kind := .custom "custom oversized table" 0
          steadyCost := 0
          residentBytes := 32 * 1024 * 1024 }
        addSpec addFast (fun _ _ => rfl),
      FloatLib.Floats.ExecFloat.Backend.Certified.binary
        { name := "custom TestByte lazy specialization"
          kind := .custom "custom lazy specialization" 1
          steadyCost := 1
          setupCost := 1000000 }
        addSpec addFast (fun _ _ => rfl),
      FloatLib.Floats.ExecFloat.Backend.Certified.binary
        { name := "custom TestByte projection kernel"
          kind := .custom "custom projection kernel" 2
          steadyCost := 10 }
        addSpec addFast (fun _ _ => rfl)
    ]
    baseline := FloatLib.Floats.ExecFloat.Backend.Certified.binary
      { name := "custom TestByte exact baseline"
        kind := .generic
        steadyCost := 100 }
      addSpec addSpec (fun _ _ => rfl)
  }

end FloatLibTests.Fixtures.CustomByte
