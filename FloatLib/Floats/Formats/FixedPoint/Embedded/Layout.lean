/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Embedded.Precision

/-!
# N1169 layouts and usual arithmetic conversions

WG14 N1169 (2006 TR 18037 draft), C clauses 6.2.6.3, 6.3.1.3a, 6.3.1.8 and
7.18a.3. A layout leaves every fractional and integral precision variable.
`Layout.Valid` records the mandatory precision constraints; smaller layouts remain
available for exhaustive tests. `Layout.example` also satisfies the recommended
practice. Value widths exclude object padding and alignment.

Mixed signedness first converts the unsigned operand to its own corresponding
signed type. Same-signedness operands retain their values until result conversion.
These functions model fixed/fixed value arithmetic, not a C compiler.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint.Embedded

/-- N1169's two fixed-point kinds.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.1.
-/
inductive Kind where
  /-- A fract type: fractional bits only. -/
  | fract
  /-- An accum type: integral bits as well as fractional bits. -/
  | accum
  deriving DecidableEq, Repr

/-- Reconstruct a `Kind` constructor from its constructor index. -/
add_decl_doc Kind.ofNat_ctorIdx

/-- N1169's three lengths, in increasing order within each kind.

Reference: WG14 N1169 (2006 TR 18037 draft), §4.1.1.
-/
inductive Length where
  /-- The `short` types. -/
  | short
  /-- The types written without a length keyword. -/
  | default
  /-- The `long` types. -/
  | long
  deriving DecidableEq, Repr

/-- Reconstruct a `Length` constructor from its constructor index. -/
add_decl_doc Length.ofNat_ctorIdx

/-- The position within the three lengths of a fixed-point kind. -/
def Length.ordinal : Length → Nat
  | .short => 0
  | .default => 1
  | .long => 2

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: minimum fractional precision for each
    length. -/
def Length.minFractionalBits : Length → Nat
  | .short => 7
  | .default => 15
  | .long => 23

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.5: kind, length, sign and saturation describe
    all 24 types. -/
structure CType where
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.5: `_Fract` or `_Accum`. -/
  kind : Kind
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.5: `short`, unmodified, or `long`. -/
  length : Length
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.5: whether negative values are
    representable. -/
  signed : Bool
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.5: whether the type carries the `_Sat`
    qualifier. -/
  saturating : Bool := false
  deriving DecidableEq, Repr

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.3a: every accum rank follows every fract
    rank. -/
def CType.rank (type : CType) : Nat :=
  (if type.kind = .fract then 0 else 3) + type.length.ordinal

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.8: the corresponding signed type preserves
    rank and saturation. -/
def CType.correspondingSigned (type : CType) : CType :=
  { type with signed := true }

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.8: result type for two fixed-point operands. -/
def CType.common (left right : CType) : CType :=
  { (if left.rank ≤ right.rank then right else left) with
    signed := left.signed || right.signed
    saturating := left.saturating || right.saturating }

/-- Implementation-selected binary precisions of the twelve primary types. -/
structure Layout where
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: fractional value-bit counts by
    signedness, kind and length. -/
  fractionalBits : Bool → Kind → Length → Nat
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.3: integral value-bit counts for
    accumulator types, excluding the sign. -/
  integralBits : Bool → Length → Nat

/-- The value format for a type under the implementation's layout. -/
def Layout.format (layout : Layout) (type : CType) : Format where
  signed := type.signed
  integralBits := if type.kind = .fract then 0 else layout.integralBits type.signed type.length
  fractionalBits := layout.fractionalBits type.signed type.kind type.length
  saturating := type.saturating

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.6.3 and 7.18a.3: all mandatory constraints on
    value precisions. -/
structure Layout.Valid (layout : Layout) : Prop where
  /-- Every type has at least the minimal fractional bits of its length. -/
  fractional_min (signed : Bool) (kind : Kind) (length : Length) :
    length.minFractionalBits ≤ layout.fractionalBits signed kind length
  /-- Every accum type has at least four integral bits. -/
  integral_min (signed : Bool) (length : Length) :
    4 ≤ layout.integralBits signed length
  /-- An unsigned fract type has the fractional bits of the signed fract type of its length, or one
  more. -/
  unsigned_fract (length : Length) :
    layout.fractionalBits false .fract length = layout.fractionalBits true .fract length ∨
      layout.fractionalBits false .fract length = layout.fractionalBits true .fract length + 1
  /-- Within one signedness and kind, a longer type has no fewer fractional bits. -/
  fractional_mono (signed : Bool) (kind : Kind) (left right : Length)
      (h : left.ordinal ≤ right.ordinal) :
    layout.fractionalBits signed kind left ≤ layout.fractionalBits signed kind right
  /-- Within one signedness, a longer accum type has no fewer integral bits. -/
  integral_mono (signed : Bool) (left right : Length) (h : left.ordinal ≤ right.ordinal) :
    layout.integralBits signed left ≤ layout.integralBits signed right
  /-- An unsigned accum type has at most the integral bits of the signed one of its length. -/
  signed_integral (length : Length) :
    layout.integralBits false length ≤ layout.integralBits true length

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.2.6.3: additional recommended practice,
    separate from conformance. -/
structure Layout.Recommended (layout : Layout) : Prop where
  /-- `long fract` has at least 31 fractional bits. -/
  long_fract : 31 ≤ layout.fractionalBits true .fract .long
  /-- Every accum type has at least eight integral bits. -/
  integral_min (signed : Bool) (length : Length) : 8 ≤ layout.integralBits signed length
  /-- An unsigned accum type has the fractional bits of the unsigned fract type of its length. -/
  unsigned_fractional (length : Length) :
    layout.fractionalBits false .accum length = layout.fractionalBits false .fract length
  /-- A signed accum type has the fractional bits of the signed or of the unsigned fract type of its
  length. -/
  signed_fractional (length : Length) :
    layout.fractionalBits true .accum length = layout.fractionalBits true .fract length ∨
      layout.fractionalBits true .accum length = layout.fractionalBits false .fract length

/-- A concrete layout satisfying both the mandatory and recommended constraints. -/
def Layout.example : Layout where
  fractionalBits signed _ length :=
    (match length with | .short => 7 | .default => 15 | .long => 31) + (!signed).toNat
  integralBits _ _ := 8

/-- The example gives an instance of every mandatory precision constraint. -/
theorem Layout.example_valid : Layout.example.Valid := by
  constructor
  · intro signed kind length
    cases signed <;> cases kind <;> cases length <;> decide
  · intro signed length
    change 4 ≤ 8
    decide
  · intro length
    cases length <;> decide
  · intro signed kind left right h
    cases signed <;> cases kind <;> cases left <;> cases right <;>
      simp_all [Length.ordinal, Layout.example]
  · intro signed left right _
    exact Nat.le_refl _
  · intro length
    exact Nat.le_refl _

/-- The example also meets all recommended precision relationships. -/
theorem Layout.example_recommended : Layout.example.Recommended := by
  constructor
  · decide
  · intro _ _
    exact Nat.le_refl _
  · intro length
    rfl
  · intro length
    exact Or.inl rfl

/-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.4–5: precision and overflow pragmas, with
    per-type rounding choices. -/
structure Environment where
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.3a: implementation-selected conversion
    rounding for each type. -/
  rounding : CType → Rounding
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.5: overflow pragma for nonsaturating
    `_Fract` results. -/
  FX_FRACT_OVERFLOW : Overflow := .DEFAULT
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.5: overflow pragma for nonsaturating
    `_Accum` results. -/
  FX_ACCUM_OVERFLOW : Overflow := .DEFAULT
  /-- WG14 N1169 (2006 TR 18037 draft), C clause 7.18a.4: admissible arithmetic result choices
    under the precision pragma. -/
  arithmetic : ArithmeticPolicy := .exact .OFF

-- Preserve the pragma identifiers specified in N1169 C 7.18a.5.
attribute [nolint defsWithUnderscore]
  Environment.FX_FRACT_OVERFLOW Environment.FX_ACCUM_OVERFLOW

/-- The kind selects its own overflow pragma; the destination's `_Sat` qualifier is separate. -/
def Environment.overflow (environment : Environment) (type : CType) : Overflow :=
  if type.kind = .fract then environment.FX_FRACT_OVERFLOW
  else environment.FX_ACCUM_OVERFLOW

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.8: convert an unsigned operand only when
    paired with a signed operand. -/
def Layout.preconvert (layout : Layout) (environment : Environment)
    (source other : CType) (value : (layout.format source).Code) : Option ℚ :=
  if !source.signed && other.signed then
    let destination := source.correspondingSigned
    (convert (layout.format destination) (environment.rounding destination)
      (environment.overflow destination) (Format.decode value)).map Format.decode
  else some (Format.decode value)

/-- WG14 N1169 (2006 TR 18037 draft), C clause 6.3.1.8 and §4.1.6.2.1: fixed/fixed arithmetic
    with the usual type conversions.
Any undefined preliminary conversion, division, or result overflow propagates as `none`. -/
def Layout.evaluate (layout : Layout) (environment : Environment) (operation : Arithmetic)
    (left right : CType) (x : (layout.format left).Code) (y : (layout.format right).Code) :
    Option (layout.format (left.common right)).Code :=
  (layout.preconvert environment left right x).bind fun x' ↦
    (layout.preconvert environment right left y).bind fun y' ↦
      let result := left.common right
      operation.applyWith environment.arithmetic (layout.format result) (environment.rounding
        result)
        (environment.overflow result) x' y'

/-- Mixed type evaluation is exactly the two preliminary conversions and the result operation. -/
theorem Layout.evaluate_eq_some_iff (layout : Layout) (environment : Environment)
    (operation : Arithmetic) (left right : CType)
    (x : (layout.format left).Code) (y : (layout.format right).Code)
    (result : (layout.format (left.common right)).Code) :
    layout.evaluate environment operation left right x y = some result ↔
      ∃ x' y', layout.preconvert environment left right x = some x' ∧
        layout.preconvert environment right left y = some y' ∧
        operation.applyWith environment.arithmetic (layout.format (left.common right))
          (environment.rounding (left.common right))
          (environment.overflow (left.common right)) x' y' = some result := by
  simp only [Layout.evaluate, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨x', hx, y', hy, hr⟩
    exact ⟨x', y', hx, hy, hr⟩
  · rintro ⟨x', y', hx, hy, hr⟩
    exact ⟨x', hx, y', hy, hr⟩

end FloatLib.Floats.Formats.FixedPoint.Embedded
