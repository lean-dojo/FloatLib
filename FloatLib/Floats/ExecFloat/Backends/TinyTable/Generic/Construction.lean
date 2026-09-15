/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Core

/-!
# Exhaustive byte-table construction

The `Tabulation` constructors share the row-major generation and lookup equations for arbitrary
radices. The `Encoding` adapters supply exact model operations and byte-range guarantees. Tables
are stored in Lean runtime `Thunk` cells, so construction is lazy and memoized while the warm path
performs no model evaluation.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Backend.TinyTable

universe u

variable {Model : Type u}

namespace Tabulation

/-- Generate a row-major binary table; the coordinate bounds erase at runtime. -/
@[inline] abbrev binary (radix : Nat) (entry : Fin radix → Fin radix → UInt8) : ByteArray :=
  ByteArray.ofFn fun index : Fin (radix * radix) =>
    have hradix : 0 < radix := Nat.pos_of_ne_zero fun h => by
      simpa [h] using index.isLt
    entry
      ⟨index.val / radix, Nat.div_lt_iff_lt_mul hradix |>.2 (by
        simpa only [Nat.mul_comm] using index.isLt)⟩
      ⟨index.val % radix, Nat.mod_lt _ hradix⟩

/-- Generate a row-major ternary table with the final coordinate varying fastest. -/
@[inline] abbrev ternary (radix : Nat)
    (entry : Fin radix → Fin radix → Fin radix → UInt8) : ByteArray :=
  ByteArray.ofFn fun index : Fin (radix * radix * radix) =>
    have hradix : 0 < radix := Nat.pos_of_ne_zero fun h => by
      simpa [h] using index.isLt
    let pair := index.val / radix
    have hpair : pair < radix * radix :=
      Nat.div_lt_iff_lt_mul hradix |>.2 (by
        simpa only [Nat.mul_assoc] using index.isLt)
    entry
      ⟨pair / radix, Nat.div_lt_iff_lt_mul hradix |>.2 (by
        simpa only [Nat.mul_comm] using hpair)⟩
      ⟨pair % radix, Nat.mod_lt _ hradix⟩
      ⟨index.val % radix, Nat.mod_lt _ hradix⟩

/-- Reading a binary table at a row-major index recovers the generating entry. -/
theorem getElem_binary (radix : Nat) (entry : Fin radix → Fin radix → UInt8)
    (left right : Fin radix) (hindex : left.val * radix + right.val < (binary radix entry).size) :
    (binary radix entry)[left.val * radix + right.val]'hindex = entry left right := by
  have hradix : 0 < radix := Nat.zero_lt_of_lt right.isLt
  rw [ByteArray.getElem_ofFn]
  have hdiv : (left.val * radix + right.val) / radix = left.val := by
    rw [Nat.mul_comm left.val radix, Nat.mul_add_div hradix,
      Nat.div_eq_of_lt right.isLt, Nat.add_zero]
  have hmod : (left.val * radix + right.val) % radix = right.val := by
    rw [Nat.mul_comm left.val radix, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt right.isLt]
  simp only [hdiv, hmod]

/-- Reading a ternary table at a row-major index recovers all three generating coordinates. -/
theorem getElem_ternary (radix : Nat) (entry : Fin radix → Fin radix → Fin radix → UInt8)
    (left right addend : Fin radix)
    (hindex : (left.val * radix + right.val) * radix + addend.val <
      (ternary radix entry).size) :
    (ternary radix entry)[(left.val * radix + right.val) * radix + addend.val]'hindex =
      entry left right addend := by
  have hradix : 0 < radix := Nat.zero_lt_of_lt addend.isLt
  rw [ByteArray.getElem_ofFn]
  have houterDiv :
      ((left.val * radix + right.val) * radix + addend.val) / radix =
        left.val * radix + right.val := by
    rw [Nat.mul_comm (left.val * radix + right.val) radix, Nat.mul_add_div hradix,
      Nat.div_eq_of_lt addend.isLt, Nat.add_zero]
  have houterMod :
      ((left.val * radix + right.val) * radix + addend.val) % radix = addend.val := by
    rw [Nat.mul_comm (left.val * radix + right.val) radix,
      Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt addend.isLt]
  have hinnerDiv : (left.val * radix + right.val) / radix = left.val := by
    rw [Nat.mul_comm left.val radix, Nat.mul_add_div hradix,
      Nat.div_eq_of_lt right.isLt, Nat.add_zero]
  have hinnerMod : (left.val * radix + right.val) % radix = right.val := by
    rw [Nat.mul_comm left.val radix, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt right.isLt]
  simp only [houterDiv, houterMod, hinnerDiv, hinnerMod]

end Tabulation

/-- Build the row-major byte table of a total binary model operation. -/
def binaryTotal (encoding : Encoding Model) (op : Model → Model → Model) : ByteArray :=
  Tabulation.binary encoding.radix fun left right =>
    UInt8.ofNat (encoding.encode (op (encoding.decode left) (encoding.decode right))).val

/-- Build the dense byte table of a total unary model operation. -/
def unaryTotal (encoding : Encoding Model) (op : Model → Model) : ByteArray :=
  ByteArray.ofFn fun index : Fin encoding.radix =>
    UInt8.ofNat (encoding.encode (op (encoding.decode index))).val

/-- Build the row-major byte table of a total ternary model operation. -/
def ternaryTotal
    (encoding : Encoding Model) (op : Model → Model → Model → Model) : ByteArray :=
  Tabulation.ternary encoding.radix fun left right addend =>
    UInt8.ofNat <|
      (encoding.encode <|
        op (encoding.decode left) (encoding.decode right) (encoding.decode addend)).val

/-- Delay and memoize a total binary table. -/
def lazyBinaryTotal
    (encoding : Encoding Model) (op : Model → Model → Model) : Thunk ByteArray :=
  Thunk.mk fun _ => binaryTotal encoding op

/-- Delay and memoize a total unary table. -/
def lazyUnaryTotal
    (encoding : Encoding Model) (op : Model → Model) : Thunk ByteArray :=
  Thunk.mk fun _ => unaryTotal encoding op

/-- Delay and memoize a total ternary table. -/
def lazyTernaryTotal
    (encoding : Encoding Model) (op : Model → Model → Model → Model) : Thunk ByteArray :=
  Thunk.mk fun _ => ternaryTotal encoding op

/-- Forcing a lazy binary table yields the corresponding exhaustive table. -/
@[simp] theorem lazyBinaryTotal_get
    (encoding : Encoding Model) (op : Model → Model → Model) :
    (lazyBinaryTotal encoding op).get = binaryTotal encoding op := by
  rfl

/-- Forcing a lazy unary table yields the corresponding exhaustive table. -/
@[simp] theorem lazyUnaryTotal_get
    (encoding : Encoding Model) (op : Model → Model) :
    (lazyUnaryTotal encoding op).get = unaryTotal encoding op := by
  rfl

/-- Forcing a lazy ternary table yields the corresponding exhaustive table. -/
@[simp] theorem lazyTernaryTotal_get
    (encoding : Encoding Model) (op : Model → Model → Model → Model) :
    (lazyTernaryTotal encoding op).get = ternaryTotal encoding op := by
  rfl

end FloatLib.Floats.ExecFloat.Backend.TinyTable
