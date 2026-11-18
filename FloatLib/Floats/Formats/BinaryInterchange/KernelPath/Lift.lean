/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
public import FloatLib.Tactic.KernelOptimize
public import FloatLib.Tactic.KernelProj

/-!
# Lifting operations on encodings to stored values

A `NatView F format` instance says that the family `F` stores encodings of `format`: it reads the
natural-number encoding out of a stored code and stores one back, next to the family's own
conversions to and from `Model format`, with the three laws that tie them together.

`unary`, `binary` and `ternary` lift an operation on encodings to `ExecFloat F` values. They use
primitive projections and constructors only, so that Lean's kernel pays a few steps for each
operand and none for the result. `unary_eq`, `binary_eq` and `ternary_eq` state that the lifted
operation is the model operation carried through the family's conversions (`NatView.liftUnary`,
`liftBinary`, `liftTernary`), which is how every binary family defines its reference operations.

A computation can also stay on encodings from end to end: `toNat_unary`, `toNat_binary` and
`toNat_ternary` say that the encoding of a lifted result is the operation applied to the
encodings of the operands, `eq_iff_toNat_eq` turns an equation between stored values into one
between encodings, and `toNat_natRec` runs a loop over stored values as a loop over encodings.
With these rules Lean's kernel never builds a stored value in the middle of a computation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.KernelPath

universe u

/--
A natural-number view of the stored codes of the family `F`, whose values are encodings of
`format`.
-/
class NatView (F : Type u) [EncodedFormat F] (format : outParam FloatFormat) where
  /-- The natural-number encoding stored in a code. -/
  toNat : FormatCode F → Nat
  /-- The code that stores an encoding below `2 ^ format.bitWidth`. -/
  ofNat : (n : Nat) → n < 2 ^ format.bitWidth → FormatCode F
  /-- The family's decoding of a code into the proof model. -/
  toModel : FormatCode F → Model format
  /-- The family's packing of a proof-model value. -/
  ofModel : Model format → FormatCode F
  /-- `toNat` reads the encoding of the decoded value. -/
  toNat_eq : ∀ code, toNat code = (toModel code).toNatBits
  /-- `toNat` reads back what `ofNat` stores. -/
  toNat_ofNat : ∀ (n : Nat) (hn : n < 2 ^ format.bitWidth), toNat (ofNat n hn) = n
  /-- Packing a decoded code returns the code. -/
  ofModel_toModel : ∀ code, ofModel (toModel code) = code

namespace NatView

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- `ofNat` stores a model value, given that value's encoding. -/
theorem ofNat_eq_ofModel {n : Nat} (hn : n < 2 ^ format.bitWidth) {value : Model format}
    (hvalue : n = value.toNatBits) : view.ofNat n hn = view.ofModel value := by
  have hmodel : view.toModel (view.ofNat n hn) = value := by
    rw [← Model.ofNatBits_toNatBits (view.toModel _), ← view.toNat_eq, view.toNat_ofNat, hvalue,
      Model.ofNatBits_toNatBits]
  rw [← hmodel, view.ofModel_toModel]

/-- A unary model operation carried through the family's conversions. -/
def liftUnary (spec : Model format → Model format) (x : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw (view.ofModel (spec (view.toModel x.raw)))

/-- A binary model operation carried through the family's conversions. -/
def liftBinary (spec : Model format → Model format → Model format)
    (x y : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw (view.ofModel (spec (view.toModel x.raw) (view.toModel y.raw)))

/-- A ternary model operation carried through the family's conversions. -/
def liftTernary (spec : Model format → Model format → Model format → Model format)
    (x y z : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw
    (view.ofModel (spec (view.toModel x.raw) (view.toModel y.raw) (view.toModel z.raw)))

/-- Lifting two model operations that agree on every operand gives the same operation. -/
theorem liftUnary_congr {f g : Model format → Model format} (h : ∀ x, f x = g x)
    (x : FloatLib.Floats.ExecFloat F) : liftUnary (view := view) f x = liftUnary g x := by
  simp only [liftUnary, h]

/-- Lifting two model operations that agree on all operands gives the same operation. -/
theorem liftBinary_congr {f g : Model format → Model format → Model format}
    (h : ∀ x y, f x y = g x y) (x y : FloatLib.Floats.ExecFloat F) :
    liftBinary (view := view) f x y = liftBinary g x y := by
  simp only [liftBinary, h]

/-- Lifting two model operations that agree on all operands gives the same operation. -/
theorem liftTernary_congr {f g : Model format → Model format → Model format → Model format}
    (h : ∀ x y z, f x y z = g x y z) (x y z : FloatLib.Floats.ExecFloat F) :
    liftTernary (view := view) f x y z = liftTernary g x y z := by
  simp only [liftTernary, h]

end NatView

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- The natural-number encoding of a stored value, read with primitive projections. -/
def toNat (x : FloatLib.Floats.ExecFloat F) : Nat :=
  (kernel_proj% view 0) (kernel_proj% x 0)

/-- The stored value whose encoding is `n` reduced to the format width. -/
def ofNat (n : Nat) : FloatLib.Floats.ExecFloat F :=
  ⟨(kernel_proj% view 1) (Nat.mod n (Nat.pow 2 format.bitWidth))
      (Nat.mod_lt n (Nat.pow_pos (by decide))), .intro⟩

/-- `toNat` reads the encoding of the model value that the family decodes. -/
theorem toNat_eq (x : FloatLib.Floats.ExecFloat F) :
    toNat x = (view.toModel x.raw).toNatBits :=
  view.toNat_eq x.raw

/-- `ofNat` stores the model value with the given encoding. -/
theorem ofNat_eq (n : Nat) :
    (ofNat n : FloatLib.Floats.ExecFloat F) =
      FloatLib.Floats.ExecFloat.ofRaw (view.ofModel (Model.ofNatBits n)) := by
  apply FloatLib.Floats.ExecFloat.ext
  refine NatView.ofNat_eq_ofModel _ ?_
  change n % 2 ^ format.bitWidth = (BitVec.ofNat format.bitWidth n).toNat
  rw [BitVec.toNat_ofNat]

/-- `toNat` reads back the encoding that `ofNat` stores, reduced to the format width. -/
theorem toNat_ofNat (n : Nat) :
    toNat (ofNat n : FloatLib.Floats.ExecFloat F) = n % 2 ^ format.bitWidth :=
  view.toNat_ofNat _ _

/-- Storing the encoding of a value returns the value. -/
theorem ofNat_toNat (x : FloatLib.Floats.ExecFloat F) : ofNat (toNat x) = x := by
  rw [ofNat_eq, toNat_eq, Model.ofNatBits_toNatBits]
  exact FloatLib.Floats.ExecFloat.ext (view.ofModel_toModel x.raw)

/-- A unary operation that computes the encodings of a model operation stays in range. -/
theorem unary_lt {op : Nat → Nat} {spec : Model format → Model format}
    (h : ∀ x, op x.toNatBits = (spec x).toNatBits) (x : FloatLib.Floats.ExecFloat F) :
    op ((kernel_proj% view 0) (kernel_proj% x 0)) < 2 ^ format.bitWidth := by
  change op (view.toNat x.raw) < _
  rw [view.toNat_eq, h]
  exact Model.toNatBits_lt_two_pow _

/-- A binary operation that computes the encodings of a model operation stays in range. -/
theorem binary_lt {op : Nat → Nat → Nat} {spec : Model format → Model format → Model format}
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) :
    op ((kernel_proj% view 0) (kernel_proj% x 0)) ((kernel_proj% view 0) (kernel_proj% y 0)) <
      2 ^ format.bitWidth := by
  change op (view.toNat x.raw) (view.toNat y.raw) < _
  rw [view.toNat_eq, view.toNat_eq, h]
  exact Model.toNatBits_lt_two_pow _

/-- A ternary operation that computes the encodings of a model operation stays in range. -/
theorem ternary_lt {op : Nat → Nat → Nat → Nat}
    {spec : Model format → Model format → Model format → Model format}
    (h : ∀ x y z, op x.toNatBits y.toNatBits z.toNatBits = (spec x y z).toNatBits)
    (x y z : FloatLib.Floats.ExecFloat F) :
    op ((kernel_proj% view 0) (kernel_proj% x 0)) ((kernel_proj% view 0) (kernel_proj% y 0))
        ((kernel_proj% view 0) (kernel_proj% z 0)) < 2 ^ format.bitWidth := by
  change op (view.toNat x.raw) (view.toNat y.raw) (view.toNat z.raw) < _
  rw [view.toNat_eq, view.toNat_eq, view.toNat_eq, h]
  exact Model.toNatBits_lt_two_pow _

/--
Lift a unary operation on encodings to stored values. `h` says that `op` computes the encodings of
the model operation `spec`, which keeps the result in range.
-/
def unary (op : Nat → Nat) (spec : Model format → Model format)
    (h : ∀ x, op x.toNatBits = (spec x).toNatBits) (x : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  ⟨(kernel_proj% view 1) (op ((kernel_proj% view 0) (kernel_proj% x 0))) (unary_lt h x), .intro⟩

/--
Lift a binary operation on encodings to stored values. `h` says that `op` computes the encodings
of the model operation `spec`, which keeps the result in range.
-/
def binary (op : Nat → Nat → Nat) (spec : Model format → Model format → Model format)
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  ⟨(kernel_proj% view 1)
      (op ((kernel_proj% view 0) (kernel_proj% x 0)) ((kernel_proj% view 0) (kernel_proj% y 0)))
      (binary_lt h x y), .intro⟩

/--
Lift a ternary operation on encodings to stored values. `h` says that `op` computes the encodings
of the model operation `spec`, which keeps the result in range.
-/
def ternary (op : Nat → Nat → Nat → Nat)
    (spec : Model format → Model format → Model format → Model format)
    (h : ∀ x y z, op x.toNatBits y.toNatBits z.toNatBits = (spec x y z).toNatBits)
    (x y z : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  ⟨(kernel_proj% view 1)
      (op ((kernel_proj% view 0) (kernel_proj% x 0)) ((kernel_proj% view 0) (kernel_proj% y 0))
        ((kernel_proj% view 0) (kernel_proj% z 0)))
      (ternary_lt h x y z), .intro⟩

/--
The stored value whose encoding is `op`, the encoding of the model value `spec`: a constant
lifted like an operation, with no reduction of `op` to the format width.
-/
def nullary (op : Nat) (spec : Model format) (h : op = spec.toNatBits) :
    FloatLib.Floats.ExecFloat F :=
  ⟨(kernel_proj% view 1) op (h ▸ Model.toNatBits_lt_two_pow spec), .intro⟩

/-- A lifted encoding is the model value carried through the family's packing. -/
theorem nullary_eq (op : Nat) (spec : Model format) (h : op = spec.toNatBits) :
    nullary (F := F) op spec h = FloatLib.Floats.ExecFloat.ofRaw (view.ofModel spec) := by
  apply FloatLib.Floats.ExecFloat.ext
  exact NatView.ofNat_eq_ofModel _ h

/-- A lifted unary operation is the model operation carried through the family's conversions. -/
theorem unary_eq (op : Nat → Nat) (spec : Model format → Model format)
    (h : ∀ x, op x.toNatBits = (spec x).toNatBits) (x : FloatLib.Floats.ExecFloat F) :
    unary op spec h x = NatView.liftUnary spec x := by
  apply FloatLib.Floats.ExecFloat.ext
  have hop : op (view.toNat x.raw) = (spec (view.toModel x.raw)).toNatBits := by
    rw [view.toNat_eq, h]
  exact NatView.ofNat_eq_ofModel _ hop

/-- A lifted binary operation is the model operation carried through the family's conversions. -/
theorem binary_eq (op : Nat → Nat → Nat) (spec : Model format → Model format → Model format)
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) :
    binary op spec h x y = NatView.liftBinary spec x y := by
  apply FloatLib.Floats.ExecFloat.ext
  have hop : op (view.toNat x.raw) (view.toNat y.raw) =
      (spec (view.toModel x.raw) (view.toModel y.raw)).toNatBits := by
    rw [view.toNat_eq, view.toNat_eq, h]
  exact NatView.ofNat_eq_ofModel _ hop

/-- A lifted ternary operation is the model operation carried through the family's conversions. -/
theorem ternary_eq (op : Nat → Nat → Nat → Nat)
    (spec : Model format → Model format → Model format → Model format)
    (h : ∀ x y z, op x.toNatBits y.toNatBits z.toNatBits = (spec x y z).toNatBits)
    (x y z : FloatLib.Floats.ExecFloat F) :
    ternary op spec h x y z = NatView.liftTernary spec x y z := by
  apply FloatLib.Floats.ExecFloat.ext
  have hop : op (view.toNat x.raw) (view.toNat y.raw) (view.toNat z.raw) =
      (spec (view.toModel x.raw) (view.toModel y.raw) (view.toModel z.raw)).toNatBits := by
    rw [view.toNat_eq, view.toNat_eq, view.toNat_eq, h]
  exact NatView.ofNat_eq_ofModel _ hop

/-! ## Staying on encodings -/

/-- The encoding of a lifted encoding is that encoding. -/
theorem toNat_nullary (op : Nat) (spec : Model format) (h : op = spec.toNatBits) :
    toNat (nullary (F := F) op spec h) = op :=
  view.toNat_ofNat _ _

/-- The encoding of a lifted unary result is the operation on the encoding of the operand. -/
theorem toNat_unary (op : Nat → Nat) (spec : Model format → Model format)
    (h : ∀ x, op x.toNatBits = (spec x).toNatBits) (x : FloatLib.Floats.ExecFloat F) :
    toNat (unary op spec h x) = op (toNat x) :=
  view.toNat_ofNat _ _

/-- The encoding of a lifted binary result is the operation on the encodings of the operands. -/
theorem toNat_binary (op : Nat → Nat → Nat) (spec : Model format → Model format → Model format)
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) :
    toNat (binary op spec h x y) = op (toNat x) (toNat y) :=
  view.toNat_ofNat _ _

/-- The encoding of a lifted ternary result is the operation on the encodings of the operands. -/
theorem toNat_ternary (op : Nat → Nat → Nat → Nat)
    (spec : Model format → Model format → Model format → Model format)
    (h : ∀ x y z, op x.toNatBits y.toNatBits z.toNatBits = (spec x y z).toNatBits)
    (x y z : FloatLib.Floats.ExecFloat F) :
    toNat (ternary op spec h x y z) = op (toNat x) (toNat y) (toNat z) :=
  view.toNat_ofNat _ _

/-- Two stored values are equal exactly when their encodings are. -/
@[kernel_optimize] theorem eq_iff_toNat_eq (x y : FloatLib.Floats.ExecFloat F) :
    x = y ↔ toNat x = toNat y := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← ofNat_toNat x, ← ofNat_toNat y, h]

/-- The encoding of a stored value is below `2 ^ format.bitWidth`. -/
theorem toNat_lt (x : FloatLib.Floats.ExecFloat F) : toNat x < 2 ^ format.bitWidth := by
  rw [toNat_eq]
  exact Model.toNatBits_lt_two_pow _

/-- Reading back a stored encoding, in the form the kernel computes: `Nat.mod` and `Nat.pow`. -/
@[kernel_optimize] theorem toNat_ofNat_kernel (n : Nat) :
    toNat (ofNat n : FloatLib.Floats.ExecFloat F) = Nat.mod n (Nat.pow 2 format.bitWidth) :=
  toNat_ofNat n

/--
The encoding of the result of a loop over stored values is the same loop over encodings: the
state is the encoding of the accumulator, and each step reads it back with `ofNat`.
-/
@[kernel_optimize] theorem toNat_natRec (init : FloatLib.Floats.ExecFloat F)
    (step : Nat → FloatLib.Floats.ExecFloat F → FloatLib.Floats.ExecFloat F) (n : Nat) :
    toNat (Nat.rec (motive := fun _ => FloatLib.Floats.ExecFloat F) init step n) =
      Nat.rec (motive := fun _ => Nat) (toNat init)
        (fun index state => toNat (step index (ofNat state))) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change toNat (step k (Nat.rec (motive := fun _ => FloatLib.Floats.ExecFloat F) init step k)) =
        toNat (step k (ofNat (Nat.rec (motive := fun _ => Nat) (toNat init)
          (fun index state => toNat (step index (ofNat state))) k)))
      rw [← ih, ofNat_toNat]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
