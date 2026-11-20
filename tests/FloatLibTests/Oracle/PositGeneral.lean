/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.Posit.KernelPath.Core
import FloatLibTests.Oracle.Parsing

/-!
# Posit operations with any number of exponent bits, for external comparison

`oracle posit-general P ES` reads one request per line from standard input and writes the
encoding that the kernel operation of `Posit.KernelPath.Core` returns in the format with `P`
payload bits and `ES` exponent bits, as a decimal number. A request is an operation name and its
operands in hexadecimal:

* `add A B`, `sub A B`, `mul A B`, `div A B`, `fma A B C` (the encoding of `A * B + C`),
  `sqrt A`, `neg A`, `abs A`, `next A`, `prior A`;
* `lt A B` and `le A B`, which write one for true and zero for false;
* `cast Q ES' A`, the conversion of `A` to the format with `Q` payload bits and `ES'` exponent
  bits;
* `tosigned W A` and `tounsigned W A`, the words of the conversions to a signed and to an
  unsigned integer of `W` bits.

`tests/oracles/posit_general.py` compares the output with SoftPosit's 8-bit posits, which have
no exponent bit, and its 16-bit posits, which have one.
-/

namespace FloatLibTests.Oracle.PositGeneral

open FloatLib.Floats.Formats.Posit
open FloatLibTests.Oracle.Parsing

/-- The result of one request in the format with `p` payload bits and `es` exponent bits. -/
def apply (p es : Nat) (operation : String) (operands : List Nat) : Option Nat :=
  match operation, operands with
  | "add", [a, b] => some (KernelPath.add p es a b)
  | "sub", [a, b] => some (KernelPath.sub p es a b)
  | "mul", [a, b] => some (KernelPath.mul p es a b)
  | "div", [a, b] => some (KernelPath.div p es a b)
  | "fma", [a, b, c] => some (KernelPath.fma p es a b c)
  | "sqrt", [a] => some (KernelPath.sqrt p es a)
  | "neg", [a] => some (KernelPath.neg p a)
  | "abs", [a] => some (KernelPath.abs p a)
  | "next", [a] => some (KernelPath.next p a)
  | "prior", [a] => some (KernelPath.prior p a)
  | "lt", [a, b] => some (if KernelPath.lt p a b then 1 else 0)
  | "le", [a, b] => some (if KernelPath.le p a b then 1 else 0)
  | "cast", [q, es', a] => some (KernelPath.cast p es q es' a)
  | "tosigned", [w, a] => some (KernelPath.toSigned p es w a)
  | "tounsigned", [w, a] => some (KernelPath.toUnsigned p es w a)
  | _, _ => none

/-- Answer the requests of standard input, one per line. -/
partial def answer (p es : Nat) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop (failures : UInt32) : IO UInt32 := do
    let line ← stdin.getLine
    if line.isEmpty then
      return failures
    match fields line with
    | operation :: rest =>
        match rest.mapM parseHex? >>= apply p es operation with
        | some result =>
            stdout.putStrLn (toString result)
            loop failures
        | none =>
            stdout.putStrLn "error"
            loop (failures + 1)
    | [] => loop failures
  loop 0

/-- Dispatch `oracle posit-general P ES`. -/
public def run (arguments : List String) : IO UInt32 := do
  match arguments.map String.toNat? with
  | [some p, some es] => answer p es
  | _ =>
      IO.eprintln "usage: oracle posit-general PAYLOAD_BITS EXPONENT_BITS"
      return 2

end FloatLibTests.Oracle.PositGeneral
