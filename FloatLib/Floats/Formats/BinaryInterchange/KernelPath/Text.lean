/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.BoundedParsing
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Literal
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Payload
public import FloatLib.Numerics.Kernel.Text

/-!
# Conversions to and from character sequences on encodings

IEEE 754-2019 §5.12 converts a value to a character sequence and back. The reference
`Model.format` and `Model.parse` work on strings, and Lean's kernel evaluates a string through
its UTF-8 bytes, which costs more than the conversion itself and grows faster than the number of
characters. This module gives both conversions on encodings and lists of characters:

* `formatCharacters fmt style mode a` is the list of characters that `Model.format` writes for
  the value with encoding `a`, in every style and rounding direction
  (`ofList_formatCharacters`). A finite word is decoded by `KernelPath.decode`, the shortest
  decimal reads its candidate back with `decimalWord` on encodings, and the digits are written
  by the loop of `Numerics.Kernel.Text`.
* `parseCharacters fmt mode characters` is the encoding of the value that `Model.parse` reads
  (`parseCharacters_eq`): decimal and hexadecimal text is rounded on encodings, by `decimalWord`
  and `roundDyadic`, an infinity or a NaN is built from its scanned fields, and text that does
  not scan as it stands (spaces around it, an error) goes to the reference parser.
* `decimalWord fmt mode d` is the encoding of the decimal record `d` rounded in the direction
  `mode` (`decimalWord_eq`): the record is brought to a reduced quotient of natural numbers and
  rounded by `ofRatio`.

Every statement holds for every format descriptor and every rounding direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/-! ## Decimal records rounded on encodings -/

/--
Encoding of the decimal record `d` rounded in the direction `mode`, from its exact value
(`decimalWordExact_eq`): the value is the quotient of `significand * 10 ^ exponent` by one, or
of `significand` by `10 ^ (-exponent)`, reduced by the greatest common divisor as the reference
reduces its rational, and rounded by `ofRatio`.
-/
def decimalWordExact (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (d : DecimalText.Decimal) : Nat :=
  (fun num den =>
    (fun g => ofRatio fmt mode (signNat d.negative) (Nat.div num g) (Nat.div den g))
      (Nat.gcd num den))
    (Nat.mul d.significand (Nat.pow 10 (Int.toNat d.exponent)))
    (Nat.pow 10 (Int.toNat (Int.neg d.exponent)))

/--
Encoding of the decimal record `d` rounded in the direction `mode` (`decimalWord_eq`):
`decimalWordExact`, after the exponent clamp of the reference for a record whose exponent is
beyond the decimal range of the format.
-/
def decimalWord (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (d : DecimalText.Decimal) : Nat :=
  decimalWordExact fmt mode
    (Bool.casesOn (motive := fun _ => DecimalText.Decimal)
      (Nat.ble d.exponent.natAbs (Nat.add (Nat.div (Nat.add fmt.exponentBias fmt.fracWidth) 3) 8))
      (Model.clampDecimalExponent fmt d) d)

/-- The magnitude of a decimal record as a quotient of natural numbers. -/
theorem decimal_magnitude_eq (significand : Nat) (exponent : Int) :
    (significand : ℚ) * (10 : ℚ) ^ exponent =
      ((significand * 10 ^ exponent.toNat : Nat) : ℚ) / ((10 ^ (-exponent).toNat : Nat) : ℚ) := by
  cases exponent with
  | ofNat k =>
      have hneg : (-Int.ofNat k).toNat = 0 := by
        cases k <;> rfl
      rw [hneg]
      simp
  | negSucc k =>
      have hneg : (-Int.negSucc k).toNat = k + 1 := rfl
      have hpos : (Int.negSucc k).toNat = 0 := rfl
      rw [hneg, hpos, zpow_negSucc]
      simp [div_eq_mul_inv]

/--
`decimalWordExact` computes the encoding of the value of the reference conversion of an exact
decimal record, for every format descriptor and rounding direction.
-/
theorem decimalWordExact_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (d : DecimalText.Decimal) :
    decimalWordExact fmt mode d =
      (Model.convertDecimalTextExact fmt mode d).value.toNatBits := by
  have hden : 10 ^ (-d.exponent).toNat ≠ 0 := by positivity
  obtain ⟨g, hg, hnum, hdenEq, -⟩ :=
    exists_common_factor _ _ _ hden (decimal_magnitude_eq d.significand d.exponent)
  have hgcd : Nat.gcd (d.significand * 10 ^ d.exponent.toNat) (10 ^ (-d.exponent).toNat) = g := by
    conv_lhs => rw [hnum, hdenEq]
    rw [Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one (Rat.reduced _), Nat.one_mul]
  have hn : d.significand * 10 ^ d.exponent.toNat / g =
      ((d.significand : ℚ) * (10 : ℚ) ^ d.exponent).num.natAbs := by
    conv_lhs => rw [hnum]
    exact Nat.mul_div_cancel _ hg
  have hd : 10 ^ (-d.exponent).toNat / g = ((d.significand : ℚ) * (10 : ℚ) ^ d.exponent).den := by
    conv_lhs => rw [hdenEq]
    exact Nat.mul_div_cancel _ hg
  change ofRatio fmt mode (signNat d.negative)
      (d.significand * 10 ^ d.exponent.toNat /
        Nat.gcd (d.significand * 10 ^ d.exponent.toNat) (10 ^ (-d.exponent).toNat))
      (10 ^ (-d.exponent).toNat /
        Nat.gcd (d.significand * 10 ^ d.exponent.toNat) (10 ^ (-d.exponent).toNat)) = _
  rw [hgcd, hn, hd, ofRatio_eq_directed]
  rfl

/--
`decimalWord` computes the encoding of the value of the reference conversion of a decimal
record, for every format descriptor and rounding direction.
-/
theorem decimalWord_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (d : DecimalText.Decimal) :
    decimalWord fmt mode d = (Model.convertDecimalText fmt mode d).value.toNatBits := by
  unfold decimalWord Model.convertDecimalText
  rw [decimalWordExact_eq]
  by_cases h : d.exponent.natAbs ≤ (fmt.exponentBias + fmt.fracWidth) / 3 + 8
  · have hble : Nat.ble d.exponent.natAbs
        (Nat.add (Nat.div (Nat.add fmt.exponentBias fmt.fracWidth) 3) 8) = true :=
      Nat.ble_eq.mpr h
    rw [hble, ite_eq_left h]
    rfl
  · have hble : Nat.ble d.exponent.natAbs
        (Nat.add (Nat.div (Nat.add fmt.exponentBias fmt.fracWidth) 3) 8) = false := by
      rw [Bool.eq_false_iff]
      exact fun hb => h (Nat.ble_eq.mp hb)
    rw [hble, ite_eq_right h]
    rfl

/-! ## Characters of a value -/

/--
The number of significant decimal digits that always identify a value of the format
(`digitCount_eq`): one more than the number of digits of `2 ^ precision`. The bit length gives
an estimate of that number, which two comparisons with powers of ten confirm; an estimate that
they do not confirm is replaced by a count of the digits.
-/
def digitCount (fmt : FloatFormat) : Nat :=
  (fun power =>
    (fun estimate =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.pow 10 estimate) power)
        (Bool.casesOn (motive := fun _ => Nat)
          (Bool.and (Nat.ble 1 estimate) (Nat.ble (Nat.pow 10 (Nat.pred estimate)) power))
          (Nat.succ (Kernel.Text.naturalDigits power 10 []).length) (Nat.succ estimate))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.pow 10 (Nat.succ estimate)) power)
          (Nat.succ (Nat.succ estimate))
          (Nat.succ (Kernel.Text.naturalDigits power 10 []).length)))
      (Nat.shiftRight (Nat.mul (Kernel.size power) 1233) 12))
    (Nat.pow 2 (Nat.succ fmt.fracWidth))

/-- `digitCount` is the digit count of the reference. -/
theorem digitCount_eq (fmt : FloatFormat) : digitCount fmt = Model.Shortest.digits fmt := by
  have hcount : Nat.succ (Kernel.Text.naturalDigits (2 ^ (fmt.fracWidth + 1)) 10 []).length =
      Nat.log 10 (2 ^ (fmt.fracWidth + 1)) + 2 := by
    rw [Kernel.Text.length_naturalDigits]
  unfold digitCount Model.Shortest.digits
  change Bool.casesOn (motive := fun _ => Nat) (Nat.ble (10 ^ _) (2 ^ (fmt.fracWidth + 1)))
    (Bool.casesOn (motive := fun _ => Nat)
      (Bool.and (Nat.ble 1 _) (Nat.ble (10 ^ Nat.pred _) (2 ^ (fmt.fracWidth + 1))))
      (Nat.succ (Kernel.Text.naturalDigits (2 ^ (fmt.fracWidth + 1)) 10 []).length)
      (Nat.succ _))
    (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (10 ^ Nat.succ _) (2 ^ (fmt.fracWidth + 1)))
      (Nat.succ (Nat.succ _))
      (Nat.succ (Kernel.Text.naturalDigits (2 ^ (fmt.fracWidth + 1)) 10 []).length)) = _
  generalize Nat.shiftRight (Nat.mul (Kernel.size (Nat.pow 2 (Nat.succ fmt.fracWidth))) 1233)
    12 = estimate
  cases habove : Nat.ble (10 ^ estimate) (2 ^ (fmt.fracWidth + 1))
  · cases hbelow : (Bool.and (Nat.ble 1 estimate)
        (Nat.ble (10 ^ Nat.pred estimate) (2 ^ (fmt.fracWidth + 1))))
    · exact hcount
    · obtain ⟨hpositive, hlow⟩ := Bool.and_eq_true_iff.mp hbelow
      have hpositive' : 1 ≤ estimate := Nat.ble_eq.mp hpositive
      have hlow' : 10 ^ (estimate - 1) ≤ 2 ^ (fmt.fracWidth + 1) := Nat.ble_eq.mp hlow
      have hhigh : 2 ^ (fmt.fracWidth + 1) < 10 ^ (estimate - 1 + 1) := by
        rw [Nat.sub_add_cancel hpositive']
        exact Nat.lt_of_not_ge (fun h => by rw [Nat.ble_eq.mpr h] at habove; cases habove)
      have hlog := Nat.log_eq_of_pow_le_of_lt_pow hlow' hhigh
      change estimate + 1 = _
      omega
  · cases hnext : Nat.ble (10 ^ Nat.succ estimate) (2 ^ (fmt.fracWidth + 1))
    · have hlow : 10 ^ estimate ≤ 2 ^ (fmt.fracWidth + 1) := Nat.ble_eq.mp habove
      have hhigh : 2 ^ (fmt.fracWidth + 1) < 10 ^ (estimate + 1) :=
        Nat.lt_of_not_ge (fun h => by rw [Nat.ble_eq.mpr h] at hnext; cases hnext)
      have hlog := Nat.log_eq_of_pow_le_of_lt_pow hlow hhigh
      change estimate + 2 = _
      omega
    · exact hcount

/--
The shortest candidate of the reference search for the finite nonzero word `a` with exact value
`exact`, kept only if it reads back as `a` in the direction `mode` (`verified_eq`): the
reference `Model.Shortest.verified` with the candidate rounded on encodings by `decimalWord`,
and with the loop bounds of the search and of the compact record taken from `Kernel.log2`.
-/
def verified (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat)
    (exact : Numerics.Dyadic) : DecimalText.Decimal :=
  match Model.Shortest.searchWith Kernel.log2
      (Model.Shortest.range mode exact.negative exact.significand exact.exponent
        (Nat.beq (fracCode fmt a) 0 && Nat.blt 1 (expCode fmt a)))
      (4 * exact.significand) exact.negative with
  | some candidate =>
      Bool.casesOn (motive := fun _ => DecimalText.Decimal)
        (Nat.beq (decimalWord fmt mode candidate) a)
        (Kernel.Text.compact (DecimalText.ofDyadic exact)) candidate
  | none => Kernel.Text.compact (DecimalText.ofDyadic exact)

/--
The decimal record displayed for the finite word `a` with exact value `exact`
(`shortestDecimal_eq`): the reference `Model.Shortest.decimal` with `verified` on encodings.
-/
def shortestDecimal (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat)
    (exact : Numerics.Dyadic) : DecimalText.Decimal :=
  if exact.significand = 0 then
    { negative := exact.negative, significand := 0, exponent := 0 }
  else
    let precision := fmt.fracWidth + 1
    let count := digitCount fmt
    if -((precision + 2 * count : Nat) : Int) ≤ exact.exponent ∧
        exact.exponent ≤ ((2 * precision + 4 * count : Nat) : Int) then
      let exactRecord := Kernel.Text.compact (DecimalText.ofDyadic exact)
      if exactRecord.significand < 10 ^ count then exactRecord else verified fmt mode a exact
    else
      verified fmt mode a exact

/--
Characters of a displayed decimal record (`shortestCharacters_eq`): fixed notation when the
leading digit lies between four places after the point and `count` places before it, and
scientific notation otherwise. The position of the leading digit is read off the digits that
are written.
-/
def shortestCharacters (count : Nat) (record : DecimalText.Decimal) : List Char :=
  (fun (leading : Int) =>
    if -4 ≤ leading ∧ leading < count then Kernel.Text.fixedCharacters record
    else Kernel.Text.scientificCharacters record)
    (Int.ofNat (Nat.pred (Kernel.Text.naturalDigits record.significand 10 []).length) +
      record.exponent)

/--
Characters of the finite word `a` with exact value `exact` in `style`
(`ofList_finiteCharacters`).
-/
def finiteCharacters (fmt : FloatFormat) (style : Model.TextStyle)
    (mode : Model.IEEERoundingMode) (a : Nat) (exact : Numerics.Dyadic) : List Char :=
  match style with
  | .shortest => shortestCharacters (digitCount fmt) (shortestDecimal fmt mode a exact)
  | .exact => Kernel.Text.decimalCharacters (DecimalText.ofDyadic exact)
  | .significant digits =>
      Kernel.Text.decimalCharacters
        (DecimalText.significantDecimal (Model.roundTextMagnitude mode)
          (DecimalText.ofDyadic exact) digits)
  | .fixed places =>
      Kernel.Text.fixedCharacters (Model.roundFixed mode places (DecimalText.ofDyadic exact))
  | .scientific places =>
      Kernel.Text.scientificCharacters
        (Model.roundScientific mode places (DecimalText.ofDyadic exact))
  | .hex .exact => Kernel.Text.hexCharacters exact
  | .hex (.significant digits) =>
      Kernel.Text.hexCharacters
        (HexText.significant (Model.roundTextMagnitude mode) exact digits)

/--
Characters that `Model.format` writes for the value with encoding `a` in `style`
(`ofList_formatCharacters`): the word is classified and decoded by `exactValue`, a finite word
goes to `finiteCharacters`, and an infinity or a NaN is spelled as the reference spells it.
-/
def formatCharacters (fmt : FloatFormat) (style : Model.TextStyle)
    (mode : Model.IEEERoundingMode) (a : Nat) : List Char :=
  match exactValue fmt a with
  | .finite exact => finiteCharacters fmt style mode a exact
  | .infinity negative =>
      match style with
      | .shortest => if negative then ['-', 'i', 'n', 'f'] else ['i', 'n', 'f']
      | _ => Kernel.Text.infinityCharacters negative
  | .nan negative signaling payload =>
      match style with
      | .shortest => ['n', 'a', 'n']
      | _ => Kernel.Text.nanCharacters negative signaling payload

/-- `verified` is the reference check of the shortest candidate, on the encoding. -/
theorem verified_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model fmt)
    (exact : Numerics.Dyadic) :
    verified fmt mode x.toNatBits exact = Model.Shortest.verified mode x exact := by
  have hbottom : (Nat.beq (Model.fracField x) 0 && Nat.blt 1 (Model.expField x)) =
      (Model.fracField x == 0 && decide (1 < Model.expField x)) := by
    rw [Bool.eq_iff_iff]
    simp [Nat.beq_eq, Nat.blt_eq]
  have hsearch : ∀ (range : Model.Shortest.Range) (target : Nat) (negative : Bool),
      Model.Shortest.searchWith Kernel.log2 range target negative =
        Model.Shortest.search range target negative := fun range target negative =>
    congrArg (fun log2 => Model.Shortest.searchWith log2 range target negative)
      (funext Kernel.log2_eq)
  unfold verified Model.Shortest.verified
  rw [fracCode_eq, expCode_eq, hbottom, hsearch, Kernel.Text.compact_eq]
  dsimp only
  generalize Model.Shortest.search _ _ _ = found
  cases found with
  | none => rfl
  | some candidate =>
      change Bool.casesOn (motive := fun _ => DecimalText.Decimal)
          (Nat.beq (decimalWord fmt mode candidate) x.toNatBits)
          (DecimalText.ofDyadic exact).compact candidate =
        if (Model.convertDecimalText fmt mode candidate).value = x then candidate
        else (DecimalText.ofDyadic exact).compact
      rw [decimalWord_eq]
      by_cases h : (Model.convertDecimalText fmt mode candidate).value = x
      · have hbeq : Nat.beq (Model.convertDecimalText fmt mode candidate).value.toNatBits
            x.toNatBits = true := by
          rw [h]
          exact Nat.beq_refl _
        rw [ite_eq_left h, hbeq]
      · have hbeq : Nat.beq (Model.convertDecimalText fmt mode candidate).value.toNatBits
            x.toNatBits = false := by
          rw [Bool.eq_false_iff]
          exact fun hb => h ((toNatBits_eq_iff _ _).mp (Nat.eq_of_beq_eq_true hb))
        rw [ite_eq_right h, hbeq]

/-- `shortestDecimal` is the decimal record that the reference displays, on the encoding. -/
theorem shortestDecimal_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model fmt)
    (exact : Numerics.Dyadic) :
    shortestDecimal fmt mode x.toNatBits exact = Model.Shortest.decimal mode x exact := by
  unfold shortestDecimal Model.Shortest.decimal
  simp only [verified_eq, digitCount_eq, Kernel.Text.compact_eq]

/-- `shortestCharacters` writes a displayed decimal record as the reference does. -/
theorem shortestCharacters_eq (count : Nat) (record : DecimalText.Decimal) :
    shortestCharacters count record = Model.Shortest.characters count record := by
  unfold shortestCharacters Model.Shortest.characters
  rw [Kernel.Text.length_naturalDigits, Kernel.Text.fixedCharacters_eq,
    Kernel.Text.scientificCharacters_eq]
  rfl

/-- The characters of a finite value are the text of the reference, in every style. -/
theorem ofList_finiteCharacters {fmt : FloatFormat} (style : Model.TextStyle)
    (mode : Model.IEEERoundingMode) (x : Model fmt) (exact : Numerics.Dyadic) :
    String.ofList (finiteCharacters fmt style mode x.toNatBits exact) =
      (Model.Internal.Status.formatFinite style mode x exact).text := by
  cases style with
  | shortest =>
      change String.ofList (shortestCharacters (digitCount fmt)
        (shortestDecimal fmt mode x.toNatBits exact)) = _
      rw [shortestCharacters_eq, digitCount_eq, shortestDecimal_eq]
      rfl
  | exact =>
      change String.ofList (Kernel.Text.decimalCharacters _) = _
      rw [Kernel.Text.decimalCharacters_eq]
      rfl
  | significant digits =>
      change String.ofList (Kernel.Text.decimalCharacters _) = _
      rw [Kernel.Text.decimalCharacters_eq]
      rfl
  | fixed places =>
      change String.ofList (Kernel.Text.fixedCharacters _) = _
      rw [Kernel.Text.fixedCharacters_eq]
      rfl
  | scientific places =>
      change String.ofList (Kernel.Text.scientificCharacters _) = _
      rw [Kernel.Text.scientificCharacters_eq]
      rfl
  | hex precision =>
      cases precision <;>
        (change String.ofList (Kernel.Text.hexCharacters _) = _
         rw [Kernel.Text.hexCharacters_eq]
         rfl)

/--
`formatCharacters` lists the characters of the text that `Model.format` writes, for every format
descriptor, style, rounding direction and value.
-/
theorem ofList_formatCharacters {fmt : FloatFormat} (x : Model fmt) (style : Model.TextStyle)
    (mode : Model.IEEERoundingMode) :
    String.ofList (formatCharacters fmt style mode x.toNatBits) = Model.format x style mode := by
  change _ = (Model.Internal.Status.format x style mode).text
  unfold formatCharacters Model.Internal.Status.format
  rw [exactValue_eq]
  cases Model.exactValue x with
  | finite exact => exact ofList_finiteCharacters style mode x exact
  | infinity negative =>
      cases style <;> cases negative <;> rfl
  | nan negative signaling payload =>
      cases style <;>
        first
        | rfl
        | exact congrArg String.ofList (Kernel.Text.nanCharacters_eq _ _ _)

/-! ## The value of a list of characters -/

/--
Decode a complete list of characters before choosing a destination format or rounding: the
reference `Model.readText` on the characters of its string (`readText_eq`), with the digits of
a significand read off the character codes.
-/
def readCharacters (characters : List Char) : Option Model.TextValue :=
  match Kernel.Text.parseDecimal characters with
  | some value => some (.decimal value)
  | none =>
      match Kernel.Text.parseHex characters with
      | some value => some (.dyadic value)
      | none =>
          let (negative, rest) := DecimalText.splitSign characters
          SpecialText.parseSpecial Model.TextValue.infinity Model.TextValue.nan negative rest

/--
Encoding of the value that `Model.parse` reads from `characters` in the direction `mode`, or its
error (`parseCharacters_eq`). Decimal and hexadecimal text is rounded on encodings, and an
infinity or a NaN is the value of the reference for the scanned sign, signaling state and
payload. Only text that does not scan as it stands, text with spaces around it or text that is
not a number, goes to the reference parser on the string.
-/
def parseCharacters (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (characters : List Char) : Except Model.ParseError Nat :=
  match readCharacters characters with
  | some (.decimal value) => .ok (decimalWord fmt mode value)
  | some (.dyadic value) => .ok (roundDyadic fmt mode value)
  | some (.infinity negative) =>
      match Model.infinity? fmt negative with
      | some value => .ok value.toNatBits
      | none => .error (.unsupportedInfinity negative)
  | some (.nan negative signaling payload) =>
      (Model.convertNaNText fmt (String.ofList characters) negative signaling payload).map
        (·.value.toNatBits)
  | none => (Model.parse fmt (String.ofList characters) mode).map Model.toNatBits

/-- The reference scan of a string is `readCharacters` on its characters. -/
theorem readText_eq (text : String) : Model.readText text = readCharacters text.toList := by
  unfold readCharacters
  rw [Kernel.Text.parseDecimal_eq, Kernel.Text.parseHex_eq]
  rfl

/--
`parseCharacters` computes the encoding of the value that `Model.parse` reads, with the same
errors, for every format descriptor, rounding direction and string.
-/
theorem parseCharacters_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (text : String) :
    parseCharacters fmt mode text.toList =
      (Model.parse fmt text mode).map Model.toNatBits := by
  have hparse : Model.parse fmt text mode =
      (Model.readTextInput text).bind (Model.Internal.Value.convertText fmt mode text) := rfl
  unfold parseCharacters
  rw [← readText_eq, String.ofList_toList]
  cases hread : Model.readText text with
  | none => rfl
  | some value =>
      have hinput : Model.readTextInput text = .ok value := by
        unfold Model.readTextInput
        rw [hread]
      cases value with
      | decimal value =>
          rw [hparse, hinput]
          change Except.ok (decimalWord fmt mode value) =
            Except.ok (Model.convertDecimalText fmt mode value).value.toNatBits
          rw [decimalWord_eq]
      | dyadic value =>
          rw [hparse, hinput]
          change Except.ok (roundDyadic fmt mode value) =
            Except.ok (Model.Internal.Directed.roundDyadic fmt mode value).toNatBits
          rw [roundDyadic_eq]
      | infinity negative =>
          rw [hparse, hinput]
          change (match Model.infinity? fmt negative with
              | some value => Except.ok value.toNatBits
              | none => Except.error (Model.ParseError.unsupportedInfinity negative)) =
            Except.map Model.toNatBits
              (match Model.infinity? fmt negative with
                | some value => Except.ok value
                | none => Except.error (Model.ParseError.unsupportedInfinity negative))
          cases Model.infinity? fmt negative <;> rfl
      | nan negative signaling payload =>
          rw [hparse, hinput]
          change (Model.convertNaNText fmt text negative signaling payload).map
              (·.value.toNatBits) =
            Except.map Model.toNatBits
              ((Model.convertNaNText fmt text negative signaling payload).map (·.value))
          cases Model.convertNaNText fmt text negative signaling payload <;> rfl

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
