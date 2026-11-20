/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.IEEE754
public import FloatLib.Tactic.Roundoff
meta import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Runtime

/-!
# `#roundoff_check`: is a generated bound useful?

`#roundoff_check` evaluates the bound and the reference of a generated theorem at given or sampled
inputs and warns when the bound is at least the magnitude of the reference, where the theorem
does not fix the sign of the result. These checks read its reports: for a subtraction that
cancels and its rewritten form, for sampled inputs of a loop, for a native program, for a
reference with a logarithm that is enclosed rather than exact, for a program in a directed
rounding attribute, and for a statement whose conclusion it cannot read.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffCheck

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

section Configured

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- `1 / (1 + s) - 1`, which cancels for small `s`. -/
def cancelling (s : Value) : Value := 1 / (1 + s) - 1

/-- The mixed theorem of the cancelling form. -/
roundoff mixed theorem cancelling_mixedError :=
  fun (s : Value) (hformat : format.isIEEE = true) (hs : 0 ≤ ExecFloat.Binary.toReal s) =>
    ExecFloat.Binary.toReal (cancelling s)

/-- The same value as `-(s / (1 + s))`, with no cancellation. -/
def stable (s : Value) : Value := -(s / (1 + s))

/-- The mixed theorem of the stable form. -/
roundoff mixed theorem stable_mixedError :=
  fun (s : Value) (hformat : format.isIEEE = true) (hs : 0 ≤ ExecFloat.Binary.toReal s) =>
    ExecFloat.Binary.toReal (stable s)

/-- A dot product. -/
def dot {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j * y j) 0

/-- The mixed theorem of the dot product. -/
roundoff mixed theorem dot_mixedError :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

/-- The closed forward theorem of the dot product. -/
roundoff closed theorem dot_closed :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

end Configured

-- At `s = 2⁻²⁴` in binary32 the sum `1 + s` rounds to one and the computed value is zero: the
-- bound exceeds the reference, and the command warns.
/--
warning: evaluated at 1 input
  computed value  0
  reference       -5.9604641e-8 (exact)
  error           5.960e-8
  bound           1.192e-7 (bound / error = 2.00)
  premises        3 hold, 0 do not, 0 not evaluated
  The bound is at least the magnitude 5.960e-8 of the reference: there the theorem does not fix
  the sign of the result. The computation cancels, or the bound is not relative to its result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check cancelling_mixedError (5.9604645e-8 : Binary32)

-- The stable form at the same input.
/--
info: evaluated at 1 input
  computed value  -5.9604645e-8
  reference       -5.9604641e-8 (exact)
  error           3.553e-15
  bound           7.105e-15 (bound / error = 2.00)
  premises        3 hold, 0 do not, 0 not evaluated
  bound / |reference| = 1.19e-7: the bound fixes the sign of the result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check stable_mixedError (5.9604645e-8 : Binary32)

-- Away from the cancellation the bound of the first form fixes the sign.
/--
info: evaluated at 1 input
  computed value  -3.3333331e-1
  reference       -3.3333333e-1 (exact)
  error           1.987e-8
  bound           9.934e-8 (bound / error = 5.00)
  premises        3 hold, 0 do not, 0 not evaluated
  bound / |reference| = 2.98e-7: the bound fixes the sign of the result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check cancelling_mixedError (0.5 : Binary32)

-- Inputs that are not given are sampled; the report is at the worst sampled input.
/--
info: evaluated at 20 inputs; the largest bound over magnitude is at
  n := 4
  x := [8594374e-5, 6049893e-9, 2566372e-8, 8692913e-10]
  y := [-4367066e-9, -7328469e-6, -4131792e-10, 8187806e-4]
  computed value  2.9208982e-1
  reference       2.9208979e-1 (exact)
  error           2.797e-8
  bound           1.572e-7 (bound / error = 5.62)
  premises        1 hold, 0 do not, 1 not evaluated
  bound / |reference| = 5.38e-7: the bound fixes the sign of the result at every input.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check dot_mixedError

/--
info: evaluated at 5 inputs; the largest bound over magnitude is at
  n := 3
  x := [-2066493e-8, -2558406e-7, -2852539e-10]
  y := [-8615838e-4, -2768442e-10, 9538451e-7]
  computed value  1.7804367e1
  reference       1.7804368e1 (exact)
  error           9.130e-7
  bound           4.245e-6 (bound / error = 4.65)
  premises        2 hold, 0 do not, 0 not evaluated
  bound / |reference| = 2.38e-7: the bound fixes the sign of the result at every input.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check (samples := 5) (size := 3) dot_closed

-- The command compiles the program once for its sampled inputs and runs it at each of them. The
-- compiled program is not left in the environment.
run_meta do
  let left : Nat := (← Lean.getEnv).constants.map₂.foldl (init := 0) fun count name _ =>
    if name.components.any (·.toString.startsWith "_roundoffCheck") then count + 1 else count
  unless left == 0 do throwError "{left} compiled programs are left in the environment"

-- Given inputs at another format.
/--
info: evaluated at 1 input
  computed value  -1.2000000e1
  reference       -1.2000000e1 (exact)
  error           0
  bound           4.663e-15
  premises        1 hold, 0 do not, 1 not evaluated
  bound / |reference| = 3.89e-16: the bound fixes the sign of the result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check dot_mixedError (n := 2) (![1.5, -2.25] : Fin 2 → Binary64) ![4, 8]

/-- A native program. -/
def nativeAxpy (a x y : Float32) : Float32 := a * x + y

/-- The mixed theorem of the native program. -/
roundoff mixed theorem nativeAxpy_mixedError :=
  fun (a x y : Float32) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.ofFloat32 (nativeAxpy a x y) : Binary32)

-- `3 * 5 - 15` is exactly zero, which no bound with a nonzero budget separates from zero.
/--
warning: evaluated at 1 input
  computed value  0
  reference       0 (exact)
  error           0
  bound           8.941e-7
  premises        1 hold, 0 do not, 0 not evaluated
  The bound is at least the magnitude 0 of the reference: there the theorem does not fix the sign
  of the result. The computation cancels, or the bound is not relative to its result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check nativeAxpy_mixedError (Float32.ofNat 3) (Float32.ofNat 5) (-(Float32.ofNat 15))

/-- A term of a relative entropy: logarithms of nearby values cancel. -/
def logRatio (p q : Binary32) : Binary32 :=
  p * (ExecFloat.Binary.CorrectlyRounded.log p - ExecFloat.Binary.CorrectlyRounded.log q)

/-- The mixed theorem of the term. -/
roundoff mixed theorem logRatio_mixedError :=
  fun (p q : Binary32) (hp : 0 < ExecFloat.Binary.toReal p) (hq : 0 < ExecFloat.Binary.toReal q) =>
    ExecFloat.Binary.toReal (logRatio p q)

-- The reference has logarithms, so it is enclosed, not exact.
/--
warning: evaluated at 1 input
  computed value  -2.9802322e-8
  reference       -2.9802321e-8 (enclosed)
  error           1.776e-15
  bound           4.131e-8 (bound / error = 2.33e7)
  premises        3 hold, 0 do not, 0 not evaluated
  The bound is at least the magnitude 2.980e-8 of the reference: there the theorem does not fix
  the sign of the result. The computation cancels, or the bound is not relative to its result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check logRatio_mixedError (0.25 : Binary32) (0.25000003 : Binary32)

/--
info: evaluated at 1 input
  computed value  -2.7465308e-1
  reference       -2.7465307e-1 (enclosed)
  error           4.959e-9
  bound           5.769e-8 (bound / error = 1.16e1)
  premises        3 hold, 0 do not, 0 not evaluated
  bound / |reference| = 2.10e-7: the bound fixes the sign of the result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check logRatio_mixedError (0.25 : Binary32) (0.75 : Binary32)

section Directed

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- The lower endpoint of `x * y + z`: both operations round toward negative infinity. -/
def lowerAffine (x y z : Value) : Value :=
  ExecFloat.Binary.add (ExecFloat.Binary.mul x y (mode := .down)) z (mode := .down)

/-- The mixed theorem of the lower endpoint. -/
roundoff mixed theorem lowerAffine_mixedError :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (lowerAffine x y z)

end Directed

-- A program in a directed attribute: the computed endpoint is below the reference, and the
-- bound uses the unit roundoff of the attribute, twice that of the format.
/--
info: evaluated at 1 input
  computed value  7.2999996e-1
  reference       7.2999999e-1 (exact)
  error           3.025e-8
  bound           9.060e-8 (bound / error = 3.00)
  premises        2 hold, 0 do not, 0 not evaluated
  bound / |reference| = 1.24e-7: the bound fixes the sign of the result.
  This is a report at the inputs above, not a proof.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check lowerAffine_mixedError (0.1 : Binary32) (0.3 : Binary32) (0.7 : Binary32)

/-- A theorem that is not a roundoff bound. -/
theorem notABound (x : ℝ) : x = x := rfl

/--
error: roundoff_check: `notABound` states no bound. The command reads a conclusion `|value -
reference| ≤ bound` or `MixedError value reference relative absolute`, as `roundoff theorem`,
`roundoff mixed theorem` and `roundoff closed theorem` generate.
-/
#guard_msgs (whitespace := lax) in
#roundoff_check notABound

end FloatLibTests.Conformance.BinaryInterchange.RoundoffCheck
