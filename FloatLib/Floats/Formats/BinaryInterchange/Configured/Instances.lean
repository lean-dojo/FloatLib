/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Instances -- shake: keep
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Formatting
public import FloatLib.Floats.ExecFloat.Comparison
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof

/-!
# Ordinary Lean instances for configured binary values

Configured binary values `ExecFloat (Configured.Family format code plan)` receive the ordinary
Lean interfaces here, generically in the storage codec, so byte, machine-word, and wide carriers
share one set of instances. Numerical literals are rounded once from exact rationals. Display,
comparison, equality, and hashing operate on the exact-width model, independently of the packed
carrier.

Two different notions of equality are installed and callers must keep them apart.

* `==` (`BEq`) is IEEE numerical equality through `ExecFloat.compareEqual`: `NaN == NaN` is
  `false` and `-0 == +0` is `true` when the format represents these values. `List.contains`,
  `List.elem`, and every other `BEq`-based search use this notion.
* `=` (`DecidableEq`) is structural equality of the stored interchange word: distinct signed-zero
  encodings are unequal and every NaN equals itself. `decide (x = y)`, `List.Nodup`, `Multiset`,
  and `Finset` use this notion. `Hashable` hashes the same word, so `x = y` implies
  `hash x = hash y`.

These instances do not provide `LawfulBEq`. Using configured values as `Std.HashMap` or
`Std.HashSet` keys requires an equality and hashing convention that satisfies their laws.

`<` and `≤` use IEEE numerical comparisons: `a < b` holds exactly when the numerical comparison
returns `some .lt`, and `a ≤ b` when it returns `some .lt` or `some .eq`. Every comparison
involving a NaN is false, so `a ≤ a` fails for NaN and these relations are not a `Preorder`.
`max` and `min` are IEEE `maximum` and `minimum`: they propagate NaN and order `-0` below `+0`,
so `max a b = if a ≤ b then b else a` fails on NaN inputs.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.Binary

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Configured binary comparison follows the descriptor's IEEE-style numerical order.

NaNs are unordered, signed zeros compare equal, and every other pair is ordered by exact value.
-/
instance :
    FloatLib.Floats.ExecFloat.Comparison (Configured.Family format code plan) where
  compare left right := Model.compare (toModel left) (toModel right)

/-- The stored word determines the value, so decoding to the model is injective. -/
@[simp] theorem toModel_inj
    {left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)} :
    toModel left = toModel right ↔ left = right :=
  ⟨Configured.Family.toModel_injective, fun h => h ▸ rfl⟩

/-- Comparison on configured values is comparison of their exact-width models. -/
theorem compare_eq_compare_toModel
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.compare left right =
      Model.compare (toModel left) (toModel right) :=
  rfl

/-- Comparison against a NaN is unordered. -/
theorem compare_eq_none_of_isNaN
    {left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)}
    (h : isNaN left = true ∨ isNaN right = true) :
    FloatLib.Floats.ExecFloat.compare left right = none :=
  (Model.compare_eq_none_iff _ _).2 h

/-- The default configured binary value is positive zero. -/
instance : Inhabited (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  default := zero false

/-- The default configured binary value is positive zero. -/
@[simp] theorem default_eq_zero :
    (default : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) = zero false :=
  rfl

/--
Structural equality of the stored interchange word.

This differs from `==`: distinct signed-zero encodings are unequal and a NaN equals itself.
Deciding equality on the
exact-width model keeps the instance independent of the packed carrier.
-/
instance : DecidableEq (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :=
  fun left right =>
    if h : toModel left = toModel right then
      isTrue (Configured.Family.toModel_injective h)
    else
      isFalse fun equality => h (congrArg toModel equality)

/--
Hash of the complete interchange word.

Structural equality `=` guarantees equal hashes. Numerical equality `==` alone does not,
since distinct signed-zero encodings compare numerically equal.
-/
instance : Hashable (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  hash value := hash (toNatBits value)

/-- The hash of a configured binary value is the hash of its interchange word. -/
theorem hash_eq_hash_toNatBits
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    hash value = hash (toNatBits value) :=
  rfl

/-- IEEE strict order: `a < b` holds when the numerical comparison returns `some .lt`. -/
instance : LT (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  lt left right := FloatLib.Floats.ExecFloat.compareLess left right = true

/-- IEEE weak order: `a ≤ b` holds when the comparison returns `some .lt` or `some .eq`. -/
instance : LE (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  le left right := FloatLib.Floats.ExecFloat.compareLessEqual left right = true

/-- `<` is decided by the executable comparison. -/
instance (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    Decidable (left < right) :=
  inferInstanceAs (Decidable (FloatLib.Floats.ExecFloat.compareLess left right = true))

/-- `≤` is decided by the executable comparison. -/
instance (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    Decidable (left ≤ right) :=
  inferInstanceAs (Decidable (FloatLib.Floats.ExecFloat.compareLessEqual left right = true))

/--
IEEE `maximum`: NaN operands propagate as a quiet NaN and `max (-0) (+0) = +0`.

This is not the order-theoretic maximum of `≤`, since NaNs are unordered by `≤`.
-/
instance : Max (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  max left right :=
    FloatLib.Floats.ExecFloat.ModelCodec.liftBinary
      (Model := Model format) (plan := plan) Model.maximum left right

/--
IEEE `minimum`: NaN operands propagate as a quiet NaN and `min (-0) (+0) = -0`.

This is not the order-theoretic minimum of `≤`, since NaNs are unordered by `≤`.
-/
instance : Min (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  min left right :=
    FloatLib.Floats.ExecFloat.ModelCodec.liftBinary
      (Model := Model format) (plan := plan) Model.minimum left right

/-- `max` decodes to IEEE `maximum` on the exact-width models. -/
@[simp] theorem toModel_max
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    toModel (max left right) = Model.maximum (toModel left) (toModel right) :=
  FloatLib.Floats.ExecFloat.ModelCodec.decode_liftBinary
    (Model := Model format) (plan := plan) Model.maximum left right

/-- `min` decodes to IEEE `minimum` on the exact-width models. -/
@[simp] theorem toModel_min
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    toModel (min left right) = Model.minimum (toModel left) (toModel right) :=
  FloatLib.Floats.ExecFloat.ModelCodec.decode_liftBinary
    (Model := Model format) (plan := plan) Model.minimum left right

section Order

variable {left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)}

/-- `<` is the executable strict comparison. -/
theorem lt_iff_compareLess :
    left < right ↔ FloatLib.Floats.ExecFloat.compareLess left right = true :=
  Iff.rfl

/-- `≤` is the executable weak comparison. -/
theorem le_iff_compareLessEqual :
    left ≤ right ↔ FloatLib.Floats.ExecFloat.compareLessEqual left right = true :=
  Iff.rfl

/-- `<` holds exactly when the model comparison returns `some .lt`. -/
theorem lt_iff_compare_eq_lt :
    left < right ↔ Model.compare (toModel left) (toModel right) = some .lt := by
  rw [lt_iff_compareLess, FloatLib.Floats.ExecFloat.compareLess, compare_eq_compare_toModel]
  exact beq_iff_eq

/-- `<` on configured values is `Model.lt` on their models. -/
theorem lt_iff_lt_toModel :
    left < right ↔ Model.lt (toModel left) (toModel right) :=
  lt_iff_compare_eq_lt

/-- `≤` holds exactly when the model comparison returns `some .lt` or `some .eq`. -/
theorem le_iff_compare_eq_lt_or_eq :
    left ≤ right ↔
      Model.compare (toModel left) (toModel right) = some .lt ∨
        Model.compare (toModel left) (toModel right) = some .eq := by
  rw [le_iff_compareLessEqual, FloatLib.Floats.ExecFloat.compareLessEqual,
    compare_eq_compare_toModel]
  generalize Model.compare (toModel left) (toModel right) = order
  rcases order with _ | (_ | _ | _) <;> simp

/-- `≤` on configured values is `Model.le` on their models. -/
theorem le_iff_le_toModel :
    left ≤ right ↔ Model.le (toModel left) (toModel right) := by
  rw [le_iff_compare_eq_lt_or_eq, Model.le]
  generalize Model.compare (toModel left) (toModel right) = order
  rcases order with _ | (_ | _ | _) <;> simp

/-- `≤` is `<` or numerical equality `==`. -/
theorem le_iff_lt_or_compareEqual :
    left ≤ right ↔
      left < right ∨ FloatLib.Floats.ExecFloat.compareEqual left right = true := by
  rw [le_iff_compare_eq_lt_or_eq, lt_iff_compare_eq_lt,
    FloatLib.Floats.ExecFloat.compareEqual, compare_eq_compare_toModel, beq_iff_eq]

/-- Nothing is strictly below or above a NaN. -/
theorem not_lt_of_isNaN (h : isNaN left = true ∨ isNaN right = true) :
    ¬ left < right := by
  rw [lt_iff_compare_eq_lt, (Model.compare_eq_none_iff _ _).2 h]
  exact nofun

/-- Nothing is weakly below or above a NaN. -/
theorem not_le_of_isNaN (h : isNaN left = true ∨ isNaN right = true) :
    ¬ left ≤ right := by
  rw [le_iff_compare_eq_lt_or_eq, (Model.compare_eq_none_iff _ _).2 h]
  rintro (h | h) <;> cases h

/-- Strict order is irreflexive, for NaN because it is unordered and otherwise by equality. -/
theorem lt_irrefl (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    ¬ value < value := by
  rw [lt_iff_compare_eq_lt]
  cases h : isNaN value
  · rw [Model.compare_self_of_isNaN_eq_false _ h]
    simp
  · rw [(Model.compare_eq_none_iff _ _).2 (Or.inl h)]
    exact nofun

/-- `≤` is reflexive exactly on non-NaN values. -/
theorem le_self_iff (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    value ≤ value ↔ isNaN value = false := by
  rw [le_iff_compare_eq_lt_or_eq]
  cases h : isNaN value
  · simp [Model.compare_self_of_isNaN_eq_false _ h]
  · simp [(Model.compare_eq_none_iff _ _).2 (Or.inl h)]

end Order

end ExecFloat.Binary

namespace Formats.BinaryInterchange

/-- Configured binary values print their mathematical value rather than their packed carrier. -/
instance {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [codec : FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    FloatLib.Floats.ExecFloat.FormatDisplay (Configured.Family format code plan) where
  format raw := Model.format (codec.toModel raw)

/-- Numeral literals are rounded once from the exact natural number into the destination format. -/
instance {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] (value : Nat) :
    OfNat (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) value where
  ofNat :=
    Configured.Family.ofModel <|
      Model.roundRatQ format (value : Rat)

/--
Scientific and decimal literals are rounded once from their exact rational value into the
destination format.
-/
instance {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    OfScientific (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  ofScientific mantissa exponentSign decimalExponent :=
    Configured.Family.ofModel <|
      Model.roundRatQ format <|
        (OfScientific.ofScientific mantissa exponentSign decimalExponent : Rat)

/-- Negation follows the destination format's signed-zero and exceptional-value policy. -/
instance {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code] :
    Neg (FloatLib.Floats.ExecFloat (Configured.Family format code plan)) where
  neg value :=
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary
      (Model := Model format) (plan := plan) Model.neg value

end Formats.BinaryInterchange
end FloatLib.Floats
