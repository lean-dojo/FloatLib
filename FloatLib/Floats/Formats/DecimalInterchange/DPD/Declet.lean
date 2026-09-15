/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

/-!
# Densely packed decimal declets

The eight cases below are Cowlishaw's DPD encoding table, also specified by
IEEE 754-2019 §3.5.2(c)(1). Three decimal digits occupy ten bits. Decoding accepts
all 1024 bit patterns; the 24 redundant patterns select the same digits as their
canonical encodings.

Source: https://speleotrove.com/decimal/DPDecimal.html, encoding and decoding tables.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.DPD

/-- Encode three decimal digits. The input contract is `n < 1000`. -/
def encodeDeclet (n : Nat) : Nat :=
  let a := n / 100
  let b := n / 10 % 10
  let c := n % 10
  let low := a % 2 * 128 + b % 2 * 16 + c % 2
  let x := a % 8 / 2
  let y := b % 8 / 2
  let z := c % 8 / 2
  low + if a < 8 then
    if b < 8 then
      if c < 8 then x * 256 + y * 32 + z * 2
      else x * 256 + y * 32 + 8
    else
      if c < 8 then x * 256 + z * 32 + 10
      else x * 256 + 78
  else
    if b < 8 then
      if c < 8 then z * 256 + y * 32 + 12
      else y * 256 + 46
    else
      if c < 8 then z * 256 + 14
      else 110

/-- Decode a ten-bit declet, including its redundant encodings. -/
def decodeDeclet (n : Nat) : Nat :=
  let r := n / 128 % 2
  let u := n / 16 % 2
  let y := n % 2
  let pq := n / 256 % 4
  let st := n / 32 % 4
  if n / 8 % 2 = 0 then
    (2 * pq + r) * 100 + (2 * st + u) * 10 + n % 8
  else if n / 2 % 4 = 0 then
    (2 * pq + r) * 100 + (2 * st + u) * 10 + 8 + y
  else if n / 2 % 4 = 1 then
    (2 * pq + r) * 100 + (8 + u) * 10 + 2 * st + y
  else if n / 2 % 4 = 2 then
    (8 + r) * 100 + (2 * st + u) * 10 + 2 * pq + y
  else if st = 2 then
    (2 * pq + r) * 100 + (8 + u) * 10 + 8 + y
  else if st = 1 then
    (8 + r) * 100 + (2 * pq + u) * 10 + 8 + y
  else if st = 0 then
    (8 + r) * 100 + (8 + u) * 10 + 2 * pq + y
  else
    (8 + r) * 100 + (8 + u) * 10 + 8 + y

end FloatLib.Floats.Formats.DecimalInterchange.DPD
