module

import FloatLib.Floats.Formats.Posit

/-!
Posit Standard (2022), §§3.4, 4.1 and 5: observations for the independent
Fraction/MPFR checker. Unary inputs exhaust widths 2–8, binary inputs widths
2–6 and fused triple products widths 2–5. Quire tests combine all these posit
inputs with nine explicit boundary words; they do not exhaust quire states.
-/

open FloatLib.Floats

set_option compiler.extract_closed false

@[noinline] def unaryOperations (bits : Nat) (valid : 2 ≤ bits) :
    List (ExecFloat.Posit bits valid → ExecFloat.Posit bits valid) :=
  [ExecFloat.Posit.negate, ExecFloat.Posit.abs, ExecFloat.Posit.sign,
    ExecFloat.Posit.nearestInt, ExecFloat.Posit.ceil, ExecFloat.Posit.floor,
    ExecFloat.Posit.next, ExecFloat.Posit.prior,
    ExecFloat.Posit.sqrt, ExecFloat.Posit.rSqrt,
    ExecFloat.Posit.exp, ExecFloat.Posit.expMinus1,
    ExecFloat.Posit.exp2, ExecFloat.Posit.exp2Minus1,
    ExecFloat.Posit.exp10, ExecFloat.Posit.exp10Minus1,
    ExecFloat.Posit.log, ExecFloat.Posit.logPlus1,
    ExecFloat.Posit.log2, ExecFloat.Posit.log2Plus1,
    ExecFloat.Posit.log10, ExecFloat.Posit.log10Plus1,
    ExecFloat.Posit.sin, ExecFloat.Posit.sinPi, ExecFloat.Posit.cos, ExecFloat.Posit.cosPi,
    ExecFloat.Posit.tan, ExecFloat.Posit.tanPi,
    ExecFloat.Posit.arcSin, ExecFloat.Posit.arcSinPi,
    ExecFloat.Posit.arcCos, ExecFloat.Posit.arcCosPi,
    ExecFloat.Posit.arcTan, ExecFloat.Posit.arcTanPi,
    ExecFloat.Posit.sinH, ExecFloat.Posit.cosH, ExecFloat.Posit.tanH,
    ExecFloat.Posit.arcSinH, ExecFloat.Posit.arcCosH, ExecFloat.Posit.arcTanH]

@[noinline] def binaryOperations (bits : Nat) (valid : 2 ≤ bits) :
    List (ExecFloat.Posit bits valid → ExecFloat.Posit bits valid →
      ExecFloat.Posit bits valid) :=
  [ExecFloat.Posit.hypot, ExecFloat.Posit.pow,
    ExecFloat.Posit.arcTan2, ExecFloat.Posit.arcTan2Pi]

@[noinline] def integerOperations (bits : Nat) (valid : 2 ≤ bits) :
    List (ExecFloat.Posit bits valid → Int → ExecFloat.Posit bits valid) :=
  [ExecFloat.Posit.compound, ExecFloat.Posit.rootN]

def emit (fields : List String) : IO Unit := do
  (← IO.getStdout).putStrLn (String.intercalate "," fields)

def emitWidth (kind : String) (bits : Nat) (valid : 2 ≤ bits) : IO Unit := do
  let value (word : Nat) : ExecFloat.Posit bits valid := ExecFloat.Posit.ofNatBits word
  let observe (x : ExecFloat.Posit bits valid) := toString (ExecFloat.Posit.toNatBits x)
  let unary := unaryOperations bits valid
  let binary := binaryOperations bits valid
  let integer := integerOperations bits valid
  for a in [:2 ^ bits] do
    let x := value a
    let fields := [kind, toString bits, toString a]
    if kind == "U" then
      emit (fields ++ unary.map (fun f => observe (f x)))
    else if kind == "I" then
      for k in [:11] do
        let exponent := (k : Int) - 5
        emit (fields ++ [toString exponent] ++ integer.map (fun f => observe (f x exponent)))
    else if kind == "B" then
      for b in [:2 ^ bits] do
        emit (fields ++ [toString b] ++ binary.map (fun f => observe (f x (value b))))
    else if kind == "T" then
      for b in [:2 ^ bits] do
        for c in [:2 ^ bits] do
          emit (fields ++ [toString b, toString c,
            observe (ExecFloat.Posit.fMM x (value b) (value c))])

def emitQuire (bits : Nat) (valid : 2 ≤ bits) : IO Unit := do
  let format : Formats.Posit.Format := { bits := bits, bits_ge_two := valid }
  let value (word : Nat) : ExecFloat.Posit bits valid := ExecFloat.Posit.ofNatBits word
  let qvalue := Formats.Posit.Quire.Model.ofNatBits format
  let observe (q : Formats.Posit.Quire.Model format) := toString q.toNatBits
  let midpoint := 2 ^ (16 * bits - 1)
  let words := [0, 1, midpoint - 1, midpoint, midpoint + 1,
    2 * midpoint - 2, 2 * midpoint - 1, midpoint / 2, midpoint + midpoint / 2]
  for a in [:2 ^ bits] do
    emit ["P", toString bits, toString a, observe (ExecFloat.Posit.Quire.pToQ (value a))]
  for qword in words do
    let q := qvalue qword
    let rounded : ExecFloat.Posit bits valid := ExecFloat.Posit.Quire.qToP q
    emit ["Q", toString bits, toString qword,
      observe (ExecFloat.Posit.Quire.qNegate q), observe (ExecFloat.Posit.Quire.qAbs q),
      toString (ExecFloat.Posit.toNatBits rounded)]
    for rword in words do
      emit ["QQ", toString bits, toString qword, toString rword,
        observe (ExecFloat.Posit.Quire.qAddQ q (qvalue rword)),
        observe (ExecFloat.Posit.Quire.qSubQ q (qvalue rword))]
    for a in [:2 ^ bits] do
      let x := value a
      emit ["QP", toString bits, toString qword, toString a,
        observe (ExecFloat.Posit.Quire.qAddP q x),
        observe (ExecFloat.Posit.Quire.qSubP q x)]
      if bits ≤ 6 then
        for b in [:2 ^ bits] do
          emit ["QPP", toString bits, toString qword, toString a, toString b,
            observe (ExecFloat.Posit.Quire.qMulAdd q x (value b)),
            observe (ExecFloat.Posit.Quire.qMulSub q x (value b))]

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (args : List String) : IO Unit := do
  let kind := args.headD "U"
  let maximum := if kind == "T" then 5 else if kind == "B" then 6 else 8
  unless ["U", "I", "B", "T", "Q"].contains kind do
    throw (IO.userError "Expected U, I, B, T or Q")
  for bits in [2:maximum + 1] do
    if valid : 2 ≤ bits then
      if kind == "Q" then emitQuire bits valid else emitWidth kind bits valid
