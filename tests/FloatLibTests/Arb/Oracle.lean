/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Lean.Data.Json
public import FloatLibTests.External.Process
import Lean

/-!
# Arb oracle (python-flint) integration

This module wraps the optional Python/Arb process:

- `run` handles one unary interval query;
- `runExpr` handles the whitelisted expression language; and
- `runMLP` handles the small feedforward-network request format.

The Lean side validates the response shape and reconstructs exact rational bounds from Arb's
`mid_rad_10exp` integers. It does not prove that Arb computed those bounds correctly; callers must
treat the process result as external evidence unless a Lean theorem checks a derived certificate.
-/

@[expose] public section

namespace Rat

/-- Render a rational in a form accepted by Arb, such as `-3/2` or `5`. -/
def toArbString (q : Rat) : String :=
  if q.den = 1 then
    toString q.num
  else
    s!"{q.num}/{q.den}"

end Rat

namespace FloatLibTests.Arb

open Lean

/-!
## Unary interval queries

Unary mode sends one function name and one input interval to Arb. It is the most direct interface
when a proof or example needs a certified enclosure for `exp`, `log`, `tanh`, or a related scalar
function.

For more general evaluation (expression ASTs / small MLPs), use the request API further below.
-/

/--
Unary interval query sent to the Python Arb oracle.

Endpoints remain decimal strings until Arb parses them, avoiding an intermediate host-float
rounding step.
-/
structure Query where
  /-- Unary function name (e.g. `"tanh"`, `"exp"`, `"log"`). -/
  func : String
  /-- Lower endpoint of the input interval, as a decimal string. -/
  lo : String
  /-- Upper endpoint of the input interval, as a decimal string. -/
  hi : String
  /-- Working precision (in bits) used inside Arb. -/
  precBits : Nat := 200
  /-- Number of decimal digits used in printed endpoints. -/
  digits : Nat := 50
  deriving Repr, Inhabited

/--
Exact integer encoding of the rational interval
`[(mid - rad) * 10^exp, (mid + rad) * 10^exp]`.

The Python process emits the three integers as strings so JSON number limits cannot truncate them.
-/
structure MidRad10Exp where
  /-- Midpoint integer. -/
  mid : Int
  /-- Nonnegative radius integer. -/
  rad : Nat
  /-- Base-10 exponent scaling both `mid` and `rad`. -/
  exp : Int
  deriving Repr, Inhabited

/--
Typed unary response, with decimal endpoints for reports and exact integer ball encodings for
subsequent checks.
-/
structure Result where
  /-- Echoed `func` name. -/
  func : String
  /-- Working precision (bits) used by Arb. -/
  precBits : Nat
  /-- Decimal digits used in printed endpoints. -/
  digits : Nat
  /-- Input interval as an Arb ball (exact integer encoding). -/
  inputBall : MidRad10Exp
  /-- Output interval as an Arb ball (exact integer encoding). -/
  outputBall : MidRad10Exp
  /-- Lower endpoint as a decimal string (human-friendly). -/
  outLo : String
  /-- Upper endpoint as a decimal string (human-friendly). -/
  outHi : String
  deriving Repr, Inhabited

/-!
## General request API (`kind = "expr"` / `"mlp"`)

The Python oracle also accepts JSON requests:

- `kind = "expr"`: evaluate a small, whitelisted expression language over Arb balls.
- `kind = "mlp"`: evaluate a small feedforward MLP given weights/biases/activations, over a box
  input.

Both remain external computations subject to the same trust boundary as unary queries.
-/

/-- Enclosure of a whitelisted expression evaluated over a box of interval variables. -/
structure ExprResult where
  /-- Working precision (bits) used by Arb. -/
  precBits : Nat
  /-- Decimal digits used in printed endpoints. -/
  digits : Nat
  /-- Output enclosure encoded as `mid_rad_10exp`. -/
  outputBall : MidRad10Exp
  /-- Lower decimal endpoint of the enclosure. -/
  outLo : String
  /-- Upper decimal endpoint of the enclosure. -/
  outHi : String
  deriving Repr, Inhabited

/--
Typed result for an `mlp` request.

The output is a vector of per-output-coordinate enclosures `(ball, lo, hi)`.
-/
structure MLPResult where
  /-- Working precision (bits) used by Arb. -/
  precBits : Nat
  /-- Decimal digits used in printed endpoints. -/
  digits : Nat
  /-- Per-output enclosures, each paired with decimal endpoint strings. -/
  output : Array (MidRad10Exp × String × String)
  deriving Repr, Inhabited

namespace Internal

/-- Locate the Python oracle from either the repository root or the tests workspace. -/
def oracleScriptPath : IO System.FilePath := do
  let relative := System.FilePath.mk "FloatLibTests/Arb/arb_oracle.py"
  for path in [relative, System.FilePath.mk "tests" / relative] do
    if ← path.pathExists then
      return path
  throw <| IO.userError "run Arb tests from the repository root or tests directory"

/-- Resolve `FLOATLIB_ARB_PY`, falling back to the supplied command. -/
def resolvePythonCmd (pythonCmd : String) : IO String := do
  FloatLibTests.External.Process.resolveCmdFromEnv "FLOATLIB_ARB_PY" pythonCmd

/-- Invoke the oracle and parse its standard output as JSON. -/
def runPythonJson (pythonCmd : String) (args : Array String) : IO Json := do
  let pythonCmd ← resolvePythonCmd pythonCmd
  let script ← oracleScriptPath
  FloatLibTests.External.Process.runJsonStdoutChecked (ctx := "Arb oracle")
    (cmd := pythonCmd) (args := #[script.toString] ++ args)

/-- Parse a JSON string value. -/
def jsonToString (j : Json) : Except String String :=
  match j with
  | .str s => .ok s
  | _ => .error s!"Expected string, got {j}"

/-- Parse a JSON natural used by response metadata. -/
def jsonToNat (j : Json) : Except String Nat :=
  match j with
  | .num n =>
    -- `Json.num` stores a `Scientific` number. The oracle schema uses natural numbers here, so
    -- parsing from the decimal representation is sufficient (and keeps this helper
    -- dependency-free).
    match n.toString.toNat? with
    | some k => .ok k
    | none => .error s!"Expected Nat, got number {n}"
  | _ => .error s!"Expected number, got {j}"

/-- Read an integer stored as a decimal string in an object field. -/
def jsonToIntFromStringKey (o : Json) (k : String) : Except String Int := do
  let s ← o.getObjVal? k >>= jsonToString
  match s.toInt? with
  | some i => .ok i
  | none => .error s!"Expected Int string at key '{k}', got '{s}'"

/-- Read a natural stored as a decimal string in an object field. -/
def jsonToNatFromStringKey (o : Json) (k : String) : Except String Nat := do
  let s ← o.getObjVal? k >>= jsonToString
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"Expected Nat string at key '{k}', got '{s}'"

end Internal

/-- Parse an Arb `mid_rad_10exp` object. -/
def parseMidRad10Exp (j : Json) : Except String MidRad10Exp := do
  let mid ← Internal.jsonToIntFromStringKey j "mid"
  let rad ← Internal.jsonToNatFromStringKey j "rad"
  let exp ← Internal.jsonToIntFromStringKey j "exp"
  pure { mid, rad, exp }

/-- Convert `mid ± rad`, scaled by `10^exp`, into exact lower and upper rational bounds. -/
def MidRad10Exp.toRatBounds (m : MidRad10Exp) : Rat × Rat :=
  let pow10Int (n : Nat) : Int :=
    Int.ofNat (Nat.pow 10 n)
  let scale (z : Int) : Rat :=
    if m.exp ≥ 0 then
      let e : Nat := Int.toNat m.exp
      Rat.ofInt (z * pow10Int e)
    else
      let e : Nat := Int.toNat (-m.exp)
      (Rat.ofInt z) / (Rat.ofInt (pow10Int e))
  let radius := Int.ofNat m.rad
  let loZ := m.mid - radius
  let hiZ := m.mid + radius
  (scale loZ, scale hiZ)

/--
Convert an Arb ball to rational bounds and reject an inverted enclosure.

`MidRad10Exp.rad` makes inversion impossible for the current encoding. The explicit check remains
at the oracle trust boundary so a future representation or conversion change cannot silently pass
reversed endpoints to interval arithmetic.
-/
def MidRad10Exp.toRatBoundsChecked (m : MidRad10Exp) : Except String (Rat × Rat) :=
  let bounds := m.toRatBounds
  if bounds.1 ≤ bounds.2 then
    .ok bounds
  else
    .error s!"Arb ball produced inverted rational bounds: {bounds.1} > {bounds.2}"

namespace Internal

/-- Render a unary query as arguments accepted by `arb_oracle.py`. -/
def queryArgs (q : Query) : Array String :=
  #[
    "--func", q.func,
    s!"--lo={q.lo}",
    s!"--hi={q.hi}",
    "--prec-bits", toString q.precBits,
    "--digits", toString q.digits
  ]

end Internal

/--
Run a unary `Query` via the Python oracle and return the raw JSON payload.

This only checks that:
- the process exits successfully, and
- the output parses as JSON.

Use `parseResult` if you want the typed `Result`.
-/
def runJson (q : Query) (pythonCmd : String := "python3") : IO Json := do
  Internal.runPythonJson pythonCmd (Internal.queryArgs q)

namespace Internal

/-- Parse the `(precision, printed digits)` response metadata. -/
def parseCtx (j : Json) : Except String (Nat × Nat) := do
  let ctx ← j.getObjVal? "ctx"
  let precBits ← ctx.getObjVal? "prec_bits" >>= jsonToNat
  let digits ← ctx.getObjVal? "digits" >>= jsonToNat
  pure (precBits, digits)

/-- Parse an object's `ball` field. -/
def parseBallField (o : Json) : Except String MidRad10Exp := do
  let ballJson ← o.getObjVal? "ball"
  parseMidRad10Exp ballJson

/-- Parse an object's decimal `lo` and `hi` fields. -/
def parseLoHi (o : Json) : Except String (String × String) := do
  let lo ← o.getObjVal? "lo" >>= jsonToString
  let hi ← o.getObjVal? "hi" >>= jsonToString
  pure (lo, hi)

/-- Parse an exact ball together with its decimal endpoint strings. -/
def parseBallLoHi (o : Json) : Except String (MidRad10Exp × String × String) := do
  let ball ← parseBallField o
  let (lo, hi) ← parseLoHi o
  pure (ball, lo, hi)

end Internal

/-- Parse the unary response schema, returning a plain error for malformed payloads. -/
def parseResult (j : Json) : Except String Result := do
  let func ← j.getObjVal? "func" >>= Internal.jsonToString
  let (precBits, digits) ← Internal.parseCtx j
  let input ← j.getObjVal? "input"
  let inputBall ← Internal.parseBallField input
  let output ← j.getObjVal? "output"
  let (outputBall, outLo, outHi) ← Internal.parseBallLoHi output
  pure { func, precBits, digits, inputBall, outputBall, outLo, outHi }

/--
Run a unary `Query` and parse the result.

It respects `FLOATLIB_ARB_PY` (if set) to choose the Python executable.
-/
def run (q : Query) (pythonCmd : String := "python3") : IO Result := do
  let j ← runJson q pythonCmd
  match parseResult j with
  | .ok r => pure r
  | .error msg => throw <| IO.userError s!"Arb oracle result parse error: {msg}\njson:\n{j}"

namespace Internal

/-- Scratch directory for request payloads retained after a failed oracle call. -/
def requestWorkDir : IO System.FilePath :=
  FloatLibTests.External.Process.artifactWorkDir "arb"

/--
Create the request directory. Failed requests remain there for inspection; successful requests are
removed unless `FLOATLIB_ARB_KEEP_TMP` is set.
-/
def ensureRequestWorkDir : IO System.FilePath := do
  let workDir ← requestWorkDir
  IO.FS.createDirAll workDir
  pure workDir

/-- Return `true` iff request payload files should be kept on disk even on success. -/
def keepTmpRequests : IO Bool := do
  pure <| (← IO.getEnv "FLOATLIB_ARB_KEEP_TMP") |>.isSome

/-- Best-effort file removal helper (ignore errors). -/
def tryRemoveFile (path : System.FilePath) : IO Unit := do
  try
    IO.FS.removeFile path
  catch _ =>
    pure ()

/-- Generate a request path using monotonic time and a random suffix. -/
def freshReqPath (workDir : System.FilePath) : IO System.FilePath := do
  let t ← IO.monoMsNow
  let r ← IO.rand 0 (Nat.pow 2 63 - 1)
  pure <| System.FilePath.mk s!"{workDir.toString}/request_{t}_{r}.json"

end Internal

/--
Run the oracle with a general `--request <file.json>` payload (returns raw JSON).

This is the entrypoint for the richer request schemas supported by `arb_oracle.py`, such as:
- `kind = "expr"` (expression AST evaluation), and
- `kind = "mlp"` (small feedforward MLP evaluation).

This respects `FLOATLIB_ARB_PY` (if set) to choose the Python executable.
-/
def runRequestJson (req : Json) (precBits : Nat := 200) (digits : Nat := 50)
    (pythonCmd : String := "python3") : IO Json := do
  let workDir ← Internal.ensureRequestWorkDir
  let path ← Internal.freshReqPath workDir
  IO.FS.writeFile path req.pretty
  try
    let j ← Internal.runPythonJson pythonCmd #[
      "--request", path.toString,
      "--prec-bits", toString precBits,
      "--digits", toString digits
    ]
    if !(← Internal.keepTmpRequests) then
      Internal.tryRemoveFile path
    pure j
  catch e =>
    -- Keep the request payload on disk for debugging.
    throw e

/-- Parse an expression response and its context metadata. -/
def parseExprResult (j : Json) : Except String ExprResult := do
  let (precBits, digits) ← Internal.parseCtx j
  let output ← j.getObjVal? "output"
  let (outputBall, outLo, outHi) ← Internal.parseBallLoHi output
  pure { precBits, digits, outputBall, outLo, outHi }

/-- Parse an MLP response and its per-coordinate output enclosures. -/
def parseMLPResult (j : Json) : Except String MLPResult := do
  let (precBits, digits) ← Internal.parseCtx j
  let output ← j.getObjVal? "output"
  let vec ← output.getObjVal? "vector"
  let arr ← vec.getArr?
  let out ← arr.mapM (fun yi => do
    let (ball, lo, hi) ← Internal.parseBallLoHi yi
    pure (ball, lo, hi)
  )
  pure { precBits, digits, output := out }

/-- Evaluate a whitelisted expression over interval variables and parse its enclosure. -/
def runExpr (vars : List (String × (String × String))) (expr : Json)
    (precBits : Nat := 200) (digits : Nat := 50) (pythonCmd : String := "python3") : IO ExprResult
      := do
  let varsObj : List (String × Json) :=
    vars.map (fun (name, (lo, hi)) =>
      (name, Json.mkObj [("lo", Json.str lo), ("hi", Json.str hi)]))
  let req :=
    Json.mkObj [
      ("kind", Json.str "expr"),
      ("vars", Json.mkObj varsObj),
      ("expr", expr)
    ]
  let j ← runRequestJson req (precBits := precBits) (digits := digits) pythonCmd
  match parseExprResult j with
  | .ok r => pure r
  | .error msg => throw <| IO.userError s!"Arb oracle expr parse error: {msg}\njson:\n{j}"

/-- Evaluate a feedforward-network request over a box input and parse each output enclosure. -/
def runMLP (req : Json) (precBits : Nat := 200) (digits : Nat := 50) (pythonCmd : String :=
  "python3") : IO MLPResult := do
  let j ← runRequestJson req (precBits := precBits) (digits := digits) pythonCmd
  match parseMLPResult j with
  | .ok r => pure r
  | .error msg => throw <| IO.userError s!"Arb oracle mlp parse error: {msg}\njson:\n{j}"

end FloatLibTests.Arb
