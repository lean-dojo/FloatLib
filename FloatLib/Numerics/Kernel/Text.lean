/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.DecimalText.Notation
public import FloatLib.Numerics.Exact.DecimalText.Special
public import FloatLib.Numerics.Exact.HexText.Runtime
public import FloatLib.Numerics.Kernel.Log2
public import FloatLib.Tactic.KernelOptimize
public import Mathlib.Data.Nat.Digits.Lemmas
import all Init.Data.Repr

/-!
# Characters of numbers for Lean's kernel

The exact text of a number is built from the digits of a natural number
(`RadixText.naturalDigits`), which the reference takes from Mathlib's `Nat.digits`. Lean's
kernel evaluates that function by recursion on a proof-carrying fuel, and every later use of one
of its digits is slow.

`naturalDigits value radix tail` writes the digits of `value` in front of `tail` with a loop on
the bit length `Kernel.size value`, the most significant digit first (`naturalDigits_eq`). Each
digit is written by `digitChar`, core's `Nat.digitChar` (`digitChar_eq`) as a definition that
the kernel can unfold in every module: the body of `Nat.digitChar` is not visible to it outside
core. The other functions are the notations of the reference on these digits, each proved equal
to its reference:

* `integerDigits`, `decimalCharacters`, `fixedCharacters`, `scientificCharacters`: a signed
  integer, and a decimal record as a significand with an exponent, in fixed notation and in
  scientific notation (`DecimalText`).
* `hexCharacters`: a dyadic as a hexadecimal significand with a binary exponent (`HexText`).
* `nanCharacters`, `infinityCharacters`: the exact spellings of a NaN and of an infinity
  (`SpecialText`).
* `parseDecimal`, `parseHex`: the parsers of the reference with the digits of the significand
  read off the character codes by `decimalDigit` and `hexDigit`.
* `length_naturalDigits`: the number of decimal digits is `Nat.log 10 value + 1`, so a caller
  reads the decimal exponent of a number off the digits it writes anyway.
* `compact`: the compact form of a decimal record, with the loop bound of the reference taken
  from `Kernel.log2`.

Lean's kernel evaluates a string through its UTF-8 bytes, at a cost that grows faster than the
number of characters. Three rules tagged `@[kernel_optimize]` keep a text that `float_decide`
computes as a list of characters: `String.length_ofList`, `String.toList_ofList` and
`ofList_eq_iff`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Text

/--
The character of a digit: `0` to `9`, `a` to `f`, and `*` from sixteen on (`digitChar_eq`). The
digit selects one of seventeen character constants by comparisons, so the kernel evaluates each
constant once.
-/
def digitChar (digit : Nat) : Char :=
  Bool.casesOn (motive := fun _ => Char) (Nat.ble 8 digit)
    (Bool.casesOn (motive := fun _ => Char) (Nat.ble 4 digit)
      (Bool.casesOn (motive := fun _ => Char) (Nat.ble 2 digit)
        (Bool.casesOn (motive := fun _ => Char) (Nat.ble 1 digit) '0' '1')
        (Bool.casesOn (motive := fun _ => Char) (Nat.ble 3 digit) '2' '3'))
      (Bool.casesOn (motive := fun _ => Char) (Nat.ble 6 digit)
        (Bool.casesOn (motive := fun _ => Char) (Nat.ble 5 digit) '4' '5')
        (Bool.casesOn (motive := fun _ => Char) (Nat.ble 7 digit) '6' '7')))
    (Bool.casesOn (motive := fun _ => Char) (Nat.ble 12 digit)
      (Bool.casesOn (motive := fun _ => Char) (Nat.ble 10 digit)
        (Bool.casesOn (motive := fun _ => Char) (Nat.ble 9 digit) '8' '9')
        (Bool.casesOn (motive := fun _ => Char) (Nat.ble 11 digit) 'a' 'b'))
      (Bool.casesOn (motive := fun _ => Char) (Nat.ble 14 digit)
        (Bool.casesOn (motive := fun _ => Char) (Nat.ble 13 digit) 'c' 'd')
        (Bool.casesOn (motive := fun _ => Char) (Nat.ble 15 digit) 'e'
          (Bool.casesOn (motive := fun _ => Char) (Nat.ble 16 digit) 'f' '*'))))

/--
The value of a decimal digit character, read off its code (`decimalDigit_eq`).
-/
def decimalDigit (character : Char) : Option Nat :=
  (fun code =>
    Bool.casesOn (motive := fun _ => Option Nat) (Bool.and (Nat.ble 48 code) (Nat.ble code 57))
      none (some (Nat.sub code 48)))
    character.toNat

/--
The value of a hexadecimal digit character of either letter case, read off its code
(`hexDigit_eq`).
-/
def hexDigit (character : Char) : Option Nat :=
  (fun code =>
    Bool.casesOn (motive := fun _ => Option Nat) (Bool.and (Nat.ble 48 code) (Nat.ble code 57))
      (Bool.casesOn (motive := fun _ => Option Nat)
        (Bool.and (Nat.ble 97 code) (Nat.ble code 102))
        (Bool.casesOn (motive := fun _ => Option Nat)
          (Bool.and (Nat.ble 65 code) (Nat.ble code 70))
          none (some (Nat.sub code 55)))
        (some (Nat.sub code 87)))
      (some (Nat.sub code 48)))
    character.toNat

/--
Parse decimal characters with an optional leading sign (`parseDecimal_eq`): the reference
`DecimalText.parseCharacters` with the digits of the significand read by `decimalDigit`.
-/
def parseDecimal (characters : List Char) : Option DecimalText.Decimal := do
  let (negative, rest) := DecimalText.splitSign characters
  let (significand, exponent) ←
    RadixText.parseMagnitude rest 10 decimalDigit DecimalText.parseExponent 1
  some { negative, significand, exponent }

/--
Parse a hexadecimal significand with a `0x` prefix and a `p` exponent (`parseHex_eq`): the
reference `HexText.parseCharacters` with the digits of the significand read by `hexDigit`.
-/
def parseHex (characters : List Char) : Option Dyadic := do
  let (negative, rest) := DecimalText.splitSign characters
  let magnitude ← match rest with
    | '0' :: 'x' :: rest | '0' :: 'X' :: rest => some rest
    | _ => none
  let (significand, exponent) ←
    RadixText.parseMagnitude magnitude 16 hexDigit HexText.parseExponent 4
  some { negative, significand, exponent }

/--
Characters of the digits of `value` in `radix` in front of `tail`, the most significant digit
first, for a `value` below `2 ^ fuel` (`digitsLoop_eq`). Zero writes no digit.
-/
def digitsLoop (radix : Nat) : Nat → Nat → List Char → List Char
  | 0, _, tail => tail
  | fuel + 1, value, tail =>
      Bool.casesOn (motive := fun _ => List Char) (Nat.beq value 0)
        (digitsLoop radix fuel (Nat.div value radix)
          (digitChar (Nat.mod value radix) :: tail))
        tail

/--
Characters of `value` in `radix` in front of `tail`, with one digit for zero
(`naturalDigits_eq`).
-/
def naturalDigits (value radix : Nat) (tail : List Char) : List Char :=
  Bool.casesOn (motive := fun _ => List Char) (Nat.beq value 0)
    (digitsLoop radix (size value) value tail) ('0' :: tail)

/-- The sign of a negative number in front of `rest`. -/
def signed (negative : Bool) (rest : List Char) : List Char :=
  Bool.casesOn (motive := fun _ => List Char) negative rest ('-' :: rest)

/-- Characters of a signed integer in front of `tail` (`integerDigits_eq`). -/
def integerDigits (value : Int) (tail : List Char) : List Char :=
  Int.casesOn (motive := fun _ => List Char) value (fun n => naturalDigits n 10 tail)
    (fun n => '-' :: naturalDigits (Nat.succ n) 10 tail)

/--
Characters of a decimal record as a significand with an optional `e` exponent
(`decimalCharacters_eq`).
-/
def decimalCharacters (value : DecimalText.Decimal) : List Char :=
  signed value.negative
    (naturalDigits value.significand 10
      (if value.exponent = 0 then [] else 'e' :: integerDigits value.exponent []))

/--
Characters of `coefficient` with `places` digits after the point
(`fractionalCharacters_eq`).
-/
def fractionalCharacters (coefficient places : Nat) : List Char :=
  (fun digits =>
    (fun count =>
      Bool.casesOn (motive := fun _ => List Char) (Nat.blt places count)
        (DecimalText.pointCharacters ['0']
          (List.replicate (Nat.sub places count) '0' ++ digits))
        (DecimalText.pointCharacters (digits.take (Nat.sub count places))
          (digits.drop (Nat.sub count places))))
      digits.length)
    (naturalDigits coefficient 10 [])

/-- Characters of a decimal record in fixed notation (`fixedCharacters_eq`). -/
def fixedCharacters (value : DecimalText.Decimal) : List Char :=
  signed value.negative
    (Int.casesOn (motive := fun _ => List Char) value.exponent
      (fun exponent => naturalDigits (Nat.mul value.significand (Nat.pow 10 exponent)) 10 [])
      (fun exponent => fractionalCharacters value.significand (Nat.succ exponent)))

/-- Characters of a decimal record in scientific notation (`scientificCharacters_eq`). -/
def scientificCharacters (value : DecimalText.Decimal) : List Char :=
  (fun digits =>
    (fun fraction =>
      signed value.negative
        (if value.significand = 0 ∧ value.exponent ≤ 0 then
          fractionalCharacters 0 value.exponent.natAbs ++ ['e', '0']
        else
          DecimalText.pointCharacters (digits.take 1) fraction ++
            'e' :: integerDigits (value.exponent + (fraction.length : Int)) []))
      (digits.drop 1))
    (naturalDigits value.significand 10 [])

/--
Characters of a dyadic as a hexadecimal significand with a binary exponent
(`hexCharacters_eq`).
-/
def hexCharacters (value : Dyadic) : List Char :=
  signed value.negative
    ('0' :: 'x' :: naturalDigits value.significand 16
      ('p' :: integerDigits value.exponent []))

/-- Characters of a NaN with its sign, signaling state and payload (`nanCharacters_eq`). -/
def nanCharacters (negative signaling : Bool) (payload : Nat) : List Char :=
  signed negative
    (Bool.casesOn (motive := fun _ => List Char) signaling
      ('N' :: 'a' :: 'N' :: naturalDigits payload 10 [])
      ('s' :: 'N' :: 'a' :: 'N' :: naturalDigits payload 10 []))

/-- Characters of an infinity with its sign (`infinityCharacters_eq`). -/
def infinityCharacters (negative : Bool) : List Char :=
  signed negative ['I', 'n', 'f', 'i', 'n', 'i', 't', 'y']

/--
A decimal record with every trailing zero of a nonzero significand moved into the exponent
(`compact_eq`): the loop of the reference, bounded by the kernel logarithm of the significand.
-/
def compact (value : DecimalText.Decimal) : DecimalText.Decimal :=
  DecimalText.Decimal.compactLoop (log2 value.significand) value

/-- `digitChar` is core's `Nat.digitChar`. -/
theorem digitChar_eq (digit : Nat) : digitChar digit = Nat.digitChar digit := by
  by_cases hdigit : digit < 16
  · interval_cases digit <;> rfl
  · obtain ⟨k, rfl⟩ : ∃ k, digit = k + 16 := ⟨digit - 16, by omega⟩
    have hble : ∀ bound : Nat, bound ≤ 16 → Nat.ble bound (k + 16) = true := fun bound h =>
      Nat.ble_eq.mpr (by omega)
    unfold digitChar
    rw [hble 8 (by decide), hble 12 (by decide), hble 14 (by decide), hble 15 (by decide),
      hble 16 (by decide)]
    simp [Nat.digitChar]

/-- A branch on a character code in a range. -/
theorem casesOn_codeRange {α : Type} (low high code : Nat) (otherwise value : α) :
    Bool.casesOn (motive := fun _ => α) (Bool.and (Nat.ble low code) (Nat.ble code high))
        otherwise value =
      if low ≤ code ∧ code ≤ high then value else otherwise := by
  by_cases h : low ≤ code ∧ code ≤ high
  · rw [ite_eq_left h, Nat.ble_eq.mpr h.1, Nat.ble_eq.mpr h.2]
    rfl
  · have hfalse : Bool.and (Nat.ble low code) (Nat.ble code high) = false := by
      rw [Bool.eq_false_iff, Ne, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
      exact h
    rw [ite_eq_right h, hfalse]

/-- `decimalDigit` is the digit reader of the reference. -/
theorem decimalDigit_eq (character : Char) :
    decimalDigit character = DecimalText.digitValue? character := by
  have hrange : ('0' ≤ character ∧ character ≤ '9') ↔
      (48 ≤ character.toNat ∧ character.toNat ≤ 57) := Iff.rfl
  unfold DecimalText.digitValue?
  change Bool.casesOn (motive := fun _ => Option Nat)
    (Bool.and (Nat.ble 48 character.toNat) (Nat.ble character.toNat 57)) none
    (some (character.toNat - 48)) = _
  rw [casesOn_codeRange]
  by_cases h : '0' ≤ character ∧ character ≤ '9'
  · rw [ite_eq_left h, ite_eq_left (hrange.mp h)]
    rfl
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (hrange.mpr hc))]

/-- `hexDigit` is the hexadecimal digit reader of the reference. -/
theorem hexDigit_eq (character : Char) : hexDigit character = HexText.digitValue? character := by
  have hdigit : ('0' ≤ character ∧ character ≤ '9') ↔
      (48 ≤ character.toNat ∧ character.toNat ≤ 57) := Iff.rfl
  have hlower : ('a' ≤ character ∧ character ≤ 'f') ↔
      (97 ≤ character.toNat ∧ character.toNat ≤ 102) := Iff.rfl
  have hupper : ('A' ≤ character ∧ character ≤ 'F') ↔
      (65 ≤ character.toNat ∧ character.toNat ≤ 70) := Iff.rfl
  unfold HexText.digitValue? DecimalText.digitValue?
  change Bool.casesOn (motive := fun _ => Option Nat)
    (Bool.and (Nat.ble 48 character.toNat) (Nat.ble character.toNat 57))
    (Bool.casesOn (motive := fun _ => Option Nat)
      (Bool.and (Nat.ble 97 character.toNat) (Nat.ble character.toNat 102))
      (Bool.casesOn (motive := fun _ => Option Nat)
        (Bool.and (Nat.ble 65 character.toNat) (Nat.ble character.toNat 70))
        none (some (character.toNat - 55)))
      (some (character.toNat - 87)))
    (some (character.toNat - 48)) = _
  rw [casesOn_codeRange, casesOn_codeRange, casesOn_codeRange]
  by_cases h1 : '0' ≤ character ∧ character ≤ '9'
  · rw [ite_eq_left h1, ite_eq_left (hdigit.mp h1)]
    rfl
  · rw [ite_eq_right h1, ite_eq_right (fun hc => h1 (hdigit.mpr hc))]
    change _ = if 'a' ≤ character ∧ character ≤ 'f' then some (character.toNat - 97 + 10)
      else if 'A' ≤ character ∧ character ≤ 'F' then some (character.toNat - 65 + 10) else none
    by_cases h2 : 'a' ≤ character ∧ character ≤ 'f'
    · have hcode := hlower.mp h2
      rw [ite_eq_left h2, ite_eq_left hcode]
      congr 1
      omega
    · rw [ite_eq_right h2, ite_eq_right (fun hc => h2 (hlower.mpr hc))]
      by_cases h3 : 'A' ≤ character ∧ character ≤ 'F'
      · have hcode := hupper.mp h3
        rw [ite_eq_left h3, ite_eq_left hcode]
        congr 1
        omega
      · rw [ite_eq_right h3, ite_eq_right (fun hc => h3 (hupper.mpr hc))]

/-- `parseDecimal` is the decimal parser of the reference. -/
theorem parseDecimal_eq (characters : List Char) :
    parseDecimal characters = DecimalText.parseCharacters characters := by
  unfold parseDecimal DecimalText.parseCharacters
  rw [show decimalDigit = DecimalText.digitValue? from funext decimalDigit_eq]

/-- `parseHex` is the hexadecimal parser of the reference. -/
theorem parseHex_eq (characters : List Char) :
    parseHex characters = HexText.parseCharacters characters := by
  unfold parseHex HexText.parseCharacters
  rw [show hexDigit = HexText.digitValue? from funext hexDigit_eq]
  rfl

/-- `compact` is the compact record of the reference. -/
theorem compact_eq (value : DecimalText.Decimal) : compact value = value.compact := by
  unfold compact DecimalText.Decimal.compact
  rw [log2_eq]

/-- The digit loop writes the digits of Mathlib's `Nat.digits`, the last one first. -/
theorem digitsLoop_eq {radix : Nat} (hradix : 1 < radix) :
    ∀ (fuel value : Nat) (tail : List Char), value < 2 ^ fuel →
      digitsLoop radix fuel value tail =
        (Nat.digits radix value).reverse.map Nat.digitChar ++ tail := by
  intro fuel
  induction fuel with
  | zero =>
      intro value tail hvalue
      have hzero : value = 0 := by simpa using hvalue
      subst hzero
      simp [digitsLoop]
  | succ fuel ih =>
      intro value tail hvalue
      by_cases hzero : value = 0
      · subst hzero
        simp [digitsLoop]
      · have hbeq : Nat.beq value 0 = false := by
          rw [Bool.eq_false_iff]
          exact fun hb => hzero (Nat.eq_of_beq_eq_true hb)
        have hquotient : value / radix < 2 ^ fuel := by
          have hle : value / radix ≤ value / 2 := Nat.div_le_div_left hradix (by decide)
          have hhalf : value / 2 < 2 ^ fuel := by
            rw [Nat.div_lt_iff_lt_mul (by decide)]
            rwa [Nat.pow_succ] at hvalue
          omega
        change Bool.casesOn (motive := fun _ => List Char) (Nat.beq value 0)
          (digitsLoop radix fuel (value / radix) (digitChar (value % radix) :: tail))
          tail = _
        rw [hbeq]
        change digitsLoop radix fuel (value / radix) (digitChar (value % radix) :: tail) = _
        rw [ih _ _ hquotient, Nat.digits_def' hradix (Nat.pos_of_ne_zero hzero), digitChar_eq]
        simp

/-- `naturalDigits` writes the digits of the reference in front of `tail`. -/
theorem naturalDigits_eq (value : Nat) {radix : Nat} (hradix : 1 < radix) (tail : List Char) :
    naturalDigits value radix tail = RadixText.naturalDigits value radix ++ tail := by
  unfold naturalDigits RadixText.naturalDigits
  by_cases hzero : value = 0
  · subst hzero
    rfl
  · have hbeq : Nat.beq value 0 = false := by
      rw [Bool.eq_false_iff]
      exact fun hb => hzero (Nat.eq_of_beq_eq_true hb)
    rw [hbeq, ite_eq_right hzero]
    refine digitsLoop_eq hradix _ _ _ ?_
    rw [size_eq]
    exact Nat.lt_size_self value

/-- The number of decimal digits of a natural number is one more than its logarithm. -/
theorem length_naturalDigits (value : Nat) :
    (naturalDigits value 10 []).length = Nat.log 10 value + 1 := by
  rw [naturalDigits_eq value (by decide), List.append_nil]
  unfold RadixText.naturalDigits
  by_cases hzero : value = 0
  · subst hzero
    simp
  · rw [ite_eq_right hzero, List.length_map, List.length_reverse,
      Nat.length_digits 10 value (by decide) hzero]

/-- `signed` writes the sign as the reference does. -/
theorem signed_eq (negative : Bool) (rest : List Char) :
    signed negative rest = (if negative then ['-'] else []) ++ rest := by
  cases negative <;> rfl

/-- `integerDigits` writes the integer of the reference in front of `tail`. -/
theorem integerDigits_eq (value : Int) (tail : List Char) :
    integerDigits value tail = DecimalText.integerDigits value ++ tail := by
  cases value with
  | ofNat n => exact naturalDigits_eq n (by decide) tail
  | negSucc n =>
      change '-' :: naturalDigits (n + 1) 10 tail = _
      rw [naturalDigits_eq (n + 1) (by decide)]
      rfl

/-- `decimalCharacters` is the exact spelling of a decimal record of the reference. -/
theorem decimalCharacters_eq (value : DecimalText.Decimal) :
    decimalCharacters value = value.characters := by
  unfold decimalCharacters DecimalText.Decimal.characters
  rw [signed_eq, naturalDigits_eq _ (by decide), integerDigits_eq, List.append_nil,
    List.append_assoc]

/-- `fractionalCharacters` is the fractional notation of the reference. -/
theorem fractionalCharacters_eq (coefficient places : Nat) :
    fractionalCharacters coefficient places =
      DecimalText.fractionalCharacters coefficient places := by
  unfold fractionalCharacters DecimalText.fractionalCharacters
  rw [naturalDigits_eq _ (by decide), List.append_nil]
  by_cases hplaces : places < (RadixText.naturalDigits coefficient 10).length
  · have hblt : Nat.blt places (RadixText.naturalDigits coefficient 10).length = true :=
      Nat.blt_eq.mpr hplaces
    simp only [hblt, Nat.sub_eq]
    rw [ite_eq_left hplaces]
  · have hblt : Nat.blt places (RadixText.naturalDigits coefficient 10).length = false := by
      rw [Bool.eq_false_iff]
      exact fun hb => hplaces (Nat.blt_eq.mp hb)
    simp only [hblt, Nat.sub_eq]
    rw [ite_eq_right hplaces]

/-- `fixedCharacters` is the fixed notation of the reference. -/
theorem fixedCharacters_eq (value : DecimalText.Decimal) :
    fixedCharacters value = value.fixedCharacters := by
  obtain ⟨negative, significand, exponent⟩ := value
  unfold fixedCharacters DecimalText.Decimal.fixedCharacters
  rw [signed_eq]
  cases exponent with
  | ofNat exponent =>
      change _ ++ naturalDigits (significand * 10 ^ exponent) 10 [] = _
      rw [naturalDigits_eq _ (by decide), List.append_nil]
  | negSucc exponent =>
      change _ ++ fractionalCharacters significand (exponent + 1) = _
      rw [fractionalCharacters_eq]

/-- `scientificCharacters` is the scientific notation of the reference. -/
theorem scientificCharacters_eq (value : DecimalText.Decimal) :
    scientificCharacters value = value.scientificCharacters := by
  unfold scientificCharacters DecimalText.Decimal.scientificCharacters
  simp only [signed_eq, naturalDigits_eq _ (by decide : 1 < 10), List.append_nil,
    integerDigits_eq, fractionalCharacters_eq]

/-- `hexCharacters` is the exact hexadecimal spelling of the reference. -/
theorem hexCharacters_eq (value : Dyadic) : hexCharacters value = HexText.characters value := by
  unfold hexCharacters HexText.characters
  rw [signed_eq, naturalDigits_eq _ (by decide), integerDigits_eq, List.append_nil]
  simp

/-- `nanCharacters` is the NaN spelling of the reference. -/
theorem nanCharacters_eq (negative signaling : Bool) (payload : Nat) :
    nanCharacters negative signaling payload =
      SpecialText.nanCharacters negative signaling payload := by
  have hsignaling : "sNaN".toList = ['s', 'N', 'a', 'N'] :=
    String.toList_ofList (l := ['s', 'N', 'a', 'N'])
  have hquiet : "NaN".toList = ['N', 'a', 'N'] := String.toList_ofList (l := ['N', 'a', 'N'])
  unfold nanCharacters SpecialText.nanCharacters
  rw [signed_eq, hsignaling, hquiet]
  cases signaling <;> simp [naturalDigits_eq _ (by decide : 1 < 10)]

/-- `infinityCharacters` is the infinity spelling of the reference. -/
theorem infinityCharacters_eq (negative : Bool) :
    infinityCharacters negative = SpecialText.infinityCharacters negative := by
  have hname : "Infinity".toList = ['I', 'n', 'f', 'i', 'n', 'i', 't', 'y'] :=
    String.toList_ofList (l := ['I', 'n', 'f', 'i', 'n', 'i', 't', 'y'])
  unfold infinityCharacters SpecialText.infinityCharacters
  rw [signed_eq, hname]

/--
A string built from a list of characters equals a string exactly when the list is the list of
characters of that string, so a computed text is compared with a string as a list.
-/
@[kernel_optimize] theorem ofList_eq_iff (characters : List Char) (text : String) :
    String.ofList characters = text ↔ characters = text.toList := by
  constructor
  · rintro rfl
    exact String.toList_ofList.symm
  · rintro rfl
    exact String.ofList_toList

attribute [kernel_optimize] String.length_ofList String.toList_ofList

end FloatLib.Numerics.Kernel.Text
