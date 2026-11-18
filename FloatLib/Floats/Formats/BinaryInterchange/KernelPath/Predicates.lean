/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Predicates.Runtime

/-!
# The comparison predicates of IEEE 754-2019 on encodings

The 22 comparisons of IEEE 754-2019 §5.11 are `Model.compareQuiet` and `Model.compareSignaling`
at a predicate. The truth value of a predicate depends only on the relation of the operands,
which `Flat.compare` computes on the two encodings as a code (`0` less, `1` equal, `2` greater,
`3` unordered), and the `invalid` flag only on whether an operand is a NaN or a signaling NaN.

* `acceptsCode predicate code` is the truth value of a predicate at a comparison code, and
  `acceptsCode_eq` proves it equal to `Predicate.accepts` at the relation the code stands for.
* `signalingCode fmt a` is one when the word `a` is a signaling NaN (`signalingCode_eq`).
* `Value.compareQuiet_eq_lift` and `Value.compareSignaling_eq_lift` state the two families on
  the decoded operands as a truth value and a flag computed on the encodings. They hold for
  every family with a natural-number view, so for every format descriptor, every predicate and
  all operands, NaNs included.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The truth value of a comparison predicate of IEEE 754-2019 §5.11 at a comparison code: `0`
less, `1` equal, `2` greater, and unordered for every other code.
-/
def acceptsCode : IEEEComparison.Predicate → Nat → Bool
  | .equal, code => Nat.beq code 1
  | .notEqual, code => !Nat.beq code 1
  | .greater, code => Nat.beq code 2
  | .greaterEqual, code => Nat.ble 1 code && Nat.ble code 2
  | .less, code => Nat.beq code 0
  | .lessEqual, code => Nat.ble code 1
  | .unordered, code => Nat.ble 3 code
  | .ordered, code => Nat.ble code 2
  | .lessUnordered, code => Nat.beq code 0 || Nat.ble 3 code
  | .notGreater, code => !Nat.beq code 2
  | .notLess, code => !Nat.beq code 0
  | .greaterUnordered, code => Nat.ble 2 code

/-- `acceptsCode` is `Predicate.accepts` at the relation that the code stands for. -/
theorem acceptsCode_eq (predicate : IEEEComparison.Predicate) (code : Nat) :
    acceptsCode predicate code = predicate.accepts (decodeOrdering code) := by
  cases predicate <;> rcases code with _ | _ | _ | code <;> rfl

/-- One when the word `a` is a signaling NaN (`signalingCode_eq`). -/
def signalingCode (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.mul (nanCode fmt a) (signalingFlag fmt a)

/-- `signalingCode` is one exactly on the signaling NaNs. -/
theorem signalingCode_eq {fmt : FloatFormat} (x : Model fmt) :
    Nat.beq (signalingCode fmt x.toNatBits) 1 = Model.isSignaling x := by
  unfold signalingCode nanCode
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.mul_eq, sign_toNatBits, magnitude_toNatBits,
    nanFlag_eq, nanFlag_mul_signalingFlag]
  cases Model.isSignaling x <;> rfl

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- The comparison code of two encodings stands for the comparison of the decoded values. -/
theorem decodeOrdering_compare (x y : FloatLib.Floats.ExecFloat F) :
    decodeOrdering (Flat.compare format (toNat x) (toNat y)) =
      Model.compare (view.toModel x.raw) (view.toModel y.raw) := by
  rw [toNat_eq, toNat_eq]
  exact compareCode_eq _ _

/--
A quiet comparison of IEEE 754-2019 §5.11 on the decoded values: the predicate at the
comparison code of the encodings, with `invalid` exactly when an encoding is a signaling NaN.
-/
theorem compareQuiet_eq_lift (predicate : IEEEComparison.Predicate)
    (x y : FloatLib.Floats.ExecFloat F) :
    Model.compareQuiet predicate (view.toModel x.raw) (view.toModel y.raw) =
      { value := acceptsCode predicate (Flat.compare format (toNat x) (toNat y))
        status :=
          { invalid := Nat.beq (signalingCode format (toNat x)) 1 ||
              Nat.beq (signalingCode format (toNat y)) 1 } } := by
  unfold Model.compareQuiet
  rw [acceptsCode_eq, decodeOrdering_compare, toNat_eq, toNat_eq, signalingCode_eq,
    signalingCode_eq]

/--
A signaling comparison of IEEE 754-2019 §5.11 on the decoded values: the predicate at the
comparison code of the encodings, with `invalid` exactly when an encoding is a NaN.
-/
theorem compareSignaling_eq_lift (predicate : IEEEComparison.Predicate)
    (x y : FloatLib.Floats.ExecFloat F) :
    Model.compareSignaling predicate (view.toModel x.raw) (view.toModel y.raw) =
      { value := acceptsCode predicate (Flat.compare format (toNat x) (toNat y))
        status :=
          { invalid := Nat.beq (nanCode format (toNat x)) 1 ||
              Nat.beq (nanCode format (toNat y)) 1 } } := by
  unfold Model.compareSignaling
  rw [acceptsCode_eq, decodeOrdering_compare, toNat_eq, toNat_eq, nanCode_eq, nanCode_eq]

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
