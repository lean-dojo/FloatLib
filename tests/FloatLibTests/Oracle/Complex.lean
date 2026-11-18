/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Algebraic
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Tangent
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Inverse
import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Power

/-!
# Complex elementary function vectors for an external MPC oracle

`oracle complex` reads one request per line from standard input and writes one result per line.
A request is `NAME EXPWIDTH FRACWIDTH MODE RE IM`: the function, the IEEE format by its exponent
and fraction widths, the rounding direction by its constructor name, and the two parts of the
argument as decimal storage words. The answer is the two storage words of the result, or `error`
followed by a reason. The request `pow EXPWIDTH FRACWIDTH MODE RE IM WRE WIM` takes the base and
the exponent, and its answer ends with `1` for a certified result and `0` otherwise.

`tests/oracles/complex_mpc.py` drives it and compares every answer with GNU MPC through gmpy2,
rounding MPC's high-precision parts to the format itself. `tests/oracles/complex_cmath.py`
compares the special values in binary64 with CPython's `cmath`.
-/

open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibTests.Oracle.Complex

/-- The unary complex functions by their C23 §7.3 names without the leading `c`. -/
def unary? (name : String) (fmt : FloatFormat) :
    Option (ExecComplex fmt → Model.IEEERoundingMode → ExecComplex fmt) :=
  match name with
  | "sqrt" => some fun z mode => ExecComplex.sqrt z mode
  | "rsqrt" => some fun z mode => ExecComplex.rsqrt z mode
  | "log" => some fun z mode => ExecComplex.log z mode
  | "log1p" => some fun z mode => ExecComplex.log1p z mode
  | "atanh" => some fun z mode => ExecComplex.atanh z mode
  | "atan" => some fun z mode => ExecComplex.atan z mode
  | "exp" => some fun z mode => ExecComplex.exp z mode
  | "expm1" => some fun z mode => ExecComplex.expm1 z mode
  | "sinh" => some fun z mode => ExecComplex.sinh z mode
  | "cosh" => some fun z mode => ExecComplex.cosh z mode
  | "sin" => some fun z mode => ExecComplex.sin z mode
  | "cos" => some fun z mode => ExecComplex.cos z mode
  | "tanh" => some fun z mode => ExecComplex.tanh z mode
  | "tan" => some fun z mode => ExecComplex.tan z mode
  | "asinh" => some fun z mode => ExecComplex.asinh z mode
  | "asin" => some fun z mode => ExecComplex.asin z mode
  | "acosh" => some fun z mode => ExecComplex.acosh z mode
  | "acos" => some fun z mode => ExecComplex.acos z mode
  | _ => none

def mode? (name : String) : Option Model.IEEERoundingMode :=
  Model.IEEERoundingMode.all.find? fun mode => toString mode == name

def format? (expWidth fracWidth : Nat) : Option FloatFormat :=
  if hexp : 2 ≤ expWidth then
    if hfrac : 0 < fracWidth then some (FloatFormat.ieee expWidth fracWidth hexp hfrac) else none
  else none

/-- Answer one request line. -/
def answer (line : String) : String :=
  match line.splitOn " " with
  | [name, expWidth, fracWidth, mode, re, im] =>
      match expWidth.toNat?, fracWidth.toNat?, mode? mode, re.toNat?, im.toNat? with
      | some expWidth, some fracWidth, some mode, some re, some im =>
          match format? expWidth fracWidth with
          | some fmt =>
              match unary? name fmt with
              | some function =>
                  let result := function ⟨Model.ofNatBits re, Model.ofNatBits im⟩ mode
                  s!"{Model.toNatBits result.re} {Model.toNatBits result.im}"
              | none => s!"error unknown function {name}"
          | none => "error unsupported format"
      | _, _, _, _, _ => "error malformed request"
  | ["pow", expWidth, fracWidth, mode, re, im, exponentRe, exponentIm] =>
      match expWidth.toNat?, fracWidth.toNat?, mode? mode, re.toNat?, im.toNat?,
        exponentRe.toNat?, exponentIm.toNat? with
      | some expWidth, some fracWidth, some mode, some re, some im, some exponentRe,
          some exponentIm =>
          match format? expWidth fracWidth with
          | some fmt =>
              let result := ExecComplex.powChecked (fmt := fmt)
                ⟨Model.ofNatBits re, Model.ofNatBits im⟩
                ⟨Model.ofNatBits exponentRe, Model.ofNatBits exponentIm⟩ mode
              s!"{Model.toNatBits result.1.re} {Model.toNatBits result.1.im} {
                if result.2 then 1 else 0}"
          | none => "error unsupported format"
      | _, _, _, _, _, _, _ => "error malformed request"
  | _ => "error malformed request"

/-- Answer requests from standard input until it ends. -/
public def run : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (answer line.trimAscii.copy)
  stdout.flush

end FloatLibTests.Oracle.Complex
