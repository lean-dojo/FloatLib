module

import FloatLib.Floats.Formats.FixedPoint.Embedded.Standard

/-!
Exhaustive observations for all binary fixed-point layouts through a selected width.
The companion Python oracle computes on Fraction values, independently of Lean's
rounding and representation code. Undefined results are emitted explicitly.
-/

open FloatLib.Numerics
open FloatLib.Floats.Formats.FixedPoint.Embedded

def observe {format : Format} (value : Option format.Code) : String :=
  value.map (fun x ↦ toString (bitsfx x)) |>.getD "NA"

def observeInt (value : Option Int) : String :=
  value.map toString |>.getD "NA"

def roundings : List Rounding :=
  [Rounding.floor, Rounding.ceil, NearestRounding.even.toRounding]

def overflows : List Overflow := [.DEFAULT, .SAT]

def arithmetic : List Arithmetic := [.add, .sub, .mul, .div]

def policies : List ArithmeticPolicy :=
  [.exact .ON, .exact .OFF, .neighbor false, .neighbor true,
    (ArithmeticPolicy.exact .ON).withUnitProducts,
    (ArithmeticPolicy.neighbor false).withUnitProducts]

def emit (stdout : IO.FS.Stream) (kind : String) (inputs : List String)
    (outputs : List String) : IO Unit :=
  stdout.putStrLn (String.intercalate "," (kind :: inputs ++ outputs))

def integers : List Int := [-129, -128, -17, -1, 0, 1, 17, 127, 128]

def emitFormat (format : Format) (mode : String := "all") : IO Unit := do
  let stdout ← IO.getStdout
  emit stdout "F" [] [if format.signed then "1" else "0",
    toString format.integralBits, toString format.fractionalBits]
  let size := 2 ^ format.width
  let value (word : Nat) := format.ofBits (BitVec.ofNat format.width word)
  if mode == "interface" then
    emit stdout "L" []
      ([toString (bitsfx format.minimum), toString (bitsfx format.maximum),
        toString format.precision, toString format.width] ++
        ([0, 1, 7].flatMap fun extra ↦
          let integer := format.bitsInteger extra
          [toString integer.minValue, toString integer.maxValue]) ++
        [if h : 0 < format.precision then toString (bitsfx (format.epsilon h)) else "NA"])
    for a in [:size] do
      let x := value a
      for integer in integers do
        emit stdout "V" [toString a, toString integer]
          ([IntegerLeft.«==» integer x, IntegerLeft.«!=» integer x,
            IntegerLeft.«<» integer x, IntegerLeft.«<=» integer x,
            IntegerLeft.«>» integer x, IntegerLeft.«>=» integer x,
            IntegerRight.«==» x integer, IntegerRight.«!=» x integer,
            IntegerRight.«<» x integer, IntegerRight.«<=» x integer,
            IntegerRight.«>» x integer, IntegerRight.«>=» x integer].map
              (fun result ↦ if result then "1" else "0") ++
            roundings.flatMap (fun r ↦ overflows.flatMap fun o ↦
              policies.flatMap fun policy ↦
                ([IntegerLeft.«+» r o integer x policy,
                  IntegerLeft.«-» r o integer x policy,
                  IntegerLeft.«*» r o integer x policy,
                  IntegerLeft.«/» r o integer x policy,
                  Assignment.IntegerRight.«+=» r o x integer policy,
                  Assignment.IntegerRight.«-=» r o x integer policy,
                  Assignment.IntegerRight.«*=» r o x integer policy,
                  Assignment.IntegerRight.«/=» r o x integer policy].map observe ++
                [IntegerFormat.signed 8, .unsigned 8].flatMap fun destination ↦
                  [Assignment.IntegerLeft.«+=» destination r o integer x policy,
                    Assignment.IntegerLeft.«-=» destination r o integer x policy,
                    Assignment.IntegerLeft.«*=» destination r o integer x policy,
                    Assignment.IntegerLeft.«/=» destination r o integer x policy].map observeInt)))
    return
  if mode == "policy" then
    for a in [:size] do
      for b in [:size] do
        let x := Format.decode (value a)
        let y := Format.decode (value b)
        emit stdout "P" [toString a, toString b]
          (roundings.flatMap fun r ↦ overflows.flatMap fun o ↦
            policies.flatMap fun policy ↦ arithmetic.map fun operation ↦
              observe (operation.applyWith policy format r o x y))
    return
  for a in [:size] do
    let x := value a
    let q := Format.decode x
    emit stdout "U" [toString a]
      ([toString (bitsfx x), toString q.num, toString q.den,
        toString (Format.toBits x).toNat, toString (bitsfx (absfx x)),
        toString (countlsfx x), toString (Unary.«!» x)] ++
        roundings.flatMap (fun r ↦ overflows.flatMap fun o ↦
          [observe (Unary.«-» r o x), observe (Prefix.«++» r o x),
            observe (Prefix.«--» r o x)]))
    for c in [:format.width + 2] do
      let count : Int := (c : Int) - 1
      emit stdout "S" [toString a, toString count]
        (roundings.flatMap (fun r ↦ overflows.flatMap fun o ↦
          [observe (Binary.«<<» r o x count), observe (Binary.«>>» r o x count)]) ++
          [observe (roundfx NearestRounding.even x count)])
    for integer in integers do
      emit stdout "I" [toString a, toString integer]
        (([IntegerFormat.signed 8, .unsigned 8].flatMap fun destination ↦
          [observeInt (muli destination integer x), observeInt (divi destination integer x)]) ++
          roundings.flatMap (fun r ↦ overflows.flatMap fun o ↦
            [observe (IntegerLeft.«*» r o integer x), observe (IntegerRight.«/» r o x integer)]))
    for b in [:size] do
      let y := value b
      emit stdout "B" [toString a, toString b]
        (roundings.flatMap (fun r ↦ overflows.flatMap fun o ↦
          arithmetic.map fun operation ↦ observe
              (operation.apply format r o q (Format.decode y))) ++
          [Compare.«==» x y, Compare.«!=» x y, Compare.«<» x y,
            Compare.«<=» x y, Compare.«>» x y, Compare.«>=» x y].map
            (fun result ↦ if result then "1" else "0") ++
          [observeInt (idiv (.signed 8) x y), observeInt (idiv (.unsigned 8) x y)])
  for index in [:4 * (size + 4)] do
    let q : ℚ :=
      ((format.integerFormat.minValue - 2 : Int) : ℚ) /
        (2 : ℚ) ^ format.fractionalBits +
      (index : ℚ) / (4 * (2 : ℚ) ^ format.fractionalBits)
    emit stdout "C" [toString q.num, toString q.den]
      (roundings.flatMap (fun r ↦ overflows.map fun o ↦ observe (convert format r o q)) ++
        [observe (convert (_Sat format) NearestRounding.even.toRounding .DEFAULT q)])
  for numerator in integers do
    for denominator in integers do
      emit stdout "Q" [toString numerator, toString denominator]
        (roundings.map fun r ↦ observe (fxdivi format r numerator denominator))

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (arguments : List String) : IO Unit := do
  if arguments.head? = some "fract8" then
    emitFormat (_Fract true 7)
    emitFormat (_Fract false 8)
    return
  let mode := arguments.head?.getD "all"
  let selected := mode == "policy" || mode == "interface"
  let maximum := ((if selected then arguments[1]? else arguments.head?).bind
    String.toNat?).getD 6
  for width in [1:maximum + 1] do
    for signed in [false, true] do
      let precision := width - if signed then 1 else 0
      for fractional in [:precision + 1] do
        emitFormat ⟨signed, precision - fractional, fractional, false⟩ mode
