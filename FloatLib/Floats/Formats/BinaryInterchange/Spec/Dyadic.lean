/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.AddDyadic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof

/-!
# Reference arithmetic with exact dyadic intermediates

Addition, subtraction, multiplication, and fused multiply-add are all specified the same way.
Decode finite operands exactly, compute the dyadic intermediate, and round once to nearest with
ties to even. Exceptional operands follow the descriptor's NaN, infinity, overflow, and zero
policy. In particular, FMA does not round its product before adding the third operand.

These definitions are the stable proof targets for the dispatched arithmetic kernels. Quotients
use the rational specification in `Spec.Division`, and roots use `Spec.SquareRoot`. Other rounding
directions and exception-status results belong to the operation APIs.

The specifications also execute when a backend declines an operand. So the rounding refinement
must be imported before they are defined, because it replaces the logical rounder's repeated
one-bit shifts with bulk integer rounding in their compiled code. Compiled addition and FMA
(`Internal.add`, `Internal.fma`) add with `addDyadicForRounding`, so operands far apart in
exponent build no integer as wide as their gap.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Spec

/-! ## Addition and subtraction -/

/-- Exact dyadic addition followed by nearest-even rounding in the destination descriptor. -/
@[inline] def add {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy => roundDyadic fmt (addDyadic dx dy)
  | _, _ =>
      match chooseNaN2 x y with
      | some nan => nan
      | none =>
          if isInf x then
            if isInf y then
              if signBit x == signBit y then x else invalidResult fmt
            else
              x
          else if isInf y then
            y
          else
            invalidResult fmt

/--
`add` as compiled code runs it. Finite operands far apart in exponent are added with
`addDyadicForRounding`, which builds no aligned integer as wide as their exponent gap and rounds
like the exact sum (`roundDyadic_addDyadicForRounding`).
-/
@[inline] def Internal.add {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy => roundDyadic fmt (addDyadicForRounding (fmt.fracWidth + 3) dx dy)
  | _, _ => Spec.add x y

/-- Compiled addition rounds the bounded sum, which rounds like the exact one. -/
@[csimp] theorem add_eq_internal : @add = @Internal.add := by
  funext fmt x y
  unfold Internal.add
  split
  · rename_i dx dy hx hy
    simp only [add, hx, hy, roundDyadic_addDyadicForRounding]
  · rfl

/--
Subtraction as addition of the negated right operand.

`neg` toggles the stored sign bit of every word in a signed-zero format, so a NaN propagated from
`y` comes back with its sign bit flipped relative to `y`. IEEE 754-2019 Section 6.3 leaves the
sign of a NaN result unspecified, so this sign choice is allowed, but callers comparing NaN words
bit for bit should not expect `sub x y` to return `y`'s NaN unchanged. In the
finite-unsigned-zero encoding `neg` leaves the NaN word unchanged, so no flip occurs there. The
dispatched `Model.sub` and its backends are proved equal to this definition, so every format
shares the convention.
-/
@[inline] def sub {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  add x (neg y)

/-! ## Multiplication -/

/-- Exact dyadic multiplication followed by nearest-even rounding in the destination descriptor. -/
@[inline] def mul {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dx.significand == 0 || dy.significand == 0 then
        zero fmt sign
      else
        roundDyadic fmt
          { negative := sign
            significand := dx.significand * dy.significand
            exponent := dx.exponent + dy.exponent }
  | _, _ =>
      match chooseNaN2 x y with
      | some nan => nan
      | none =>
          if isInf x then
            if isZero y then invalidResult fmt
            else nativeOverflow fmt (signBit x != signBit y)
          else if isInf y then
            if isZero x then invalidResult fmt
            else nativeOverflow fmt (signBit x != signBit y)
          else
            invalidResult fmt

/-! ## Fused multiply-add -/

/-- Exact `(x * y) + z` followed by one nearest-even destination rounding. -/
@[inline] def fma {fmt : FloatFormat} (x y z : Model fmt) : Model fmt :=
  match chooseNaN3 x y z with
  | some nan => nan
  | none =>
      if isInf x || isInf y then
        if isZero x || isZero y then
          invalidResult fmt
        else
          let prodSign := Bool.xor (signBit x) (signBit y)
          let prodInf := nativeOverflow fmt prodSign
          if isInf z then
            if signBit z != prodSign then invalidResult fmt else prodInf
          else
            prodInf
      else if isInf z then
        z
      else
        match toDyadic? x, toDyadic? y, toDyadic? z with
        | some dx, some dy, some dz =>
            let product : Numerics.Dyadic :=
              { negative := Bool.xor dx.negative dy.negative
                significand := dx.significand * dy.significand
                exponent := dx.exponent + dy.exponent }
            roundDyadic fmt (addDyadic product dz)
        | _, _, _ => invalidResult fmt

/--
`fma` as compiled code runs it: the product and the addend are added with `addDyadicForRounding`,
so an addend far from the product in exponent builds no correspondingly wide integer.
-/
@[inline] def Internal.fma {fmt : FloatFormat} (x y z : Model fmt) : Model fmt :=
  match chooseNaN3 x y z with
  | some nan => nan
  | none =>
      if isInf x || isInf y then
        if isZero x || isZero y then
          invalidResult fmt
        else
          let prodSign := Bool.xor (signBit x) (signBit y)
          let prodInf := nativeOverflow fmt prodSign
          if isInf z then
            if signBit z != prodSign then invalidResult fmt else prodInf
          else
            prodInf
      else if isInf z then
        z
      else
        match toDyadic? x, toDyadic? y, toDyadic? z with
        | some dx, some dy, some dz =>
            let product : Numerics.Dyadic :=
              { negative := Bool.xor dx.negative dy.negative
                significand := dx.significand * dy.significand
                exponent := dx.exponent + dy.exponent }
            roundDyadic fmt (addDyadicForRounding (fmt.fracWidth + 3) product dz)
        | _, _, _ => invalidResult fmt

/-- Compiled FMA rounds the bounded sum of the product and the addend. -/
@[csimp] theorem fma_eq_internal : @fma = @Internal.fma := by
  funext fmt x y z
  simp only [fma, Internal.fma, roundDyadic_addDyadicForRounding]

end FloatLib.Floats.Formats.BinaryInterchange.Model.Spec
