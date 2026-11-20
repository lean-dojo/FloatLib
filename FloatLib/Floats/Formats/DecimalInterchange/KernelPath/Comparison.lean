/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Comparison.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Recommended.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.TotalOrder.Runtime

/-!
# Kernel path of the decimal comparisons, the total order and the minimum and maximum operations

`Datum.compare` is specified on exact rational values extended by the two infinities, and the
22 comparisons of IEEE 754-2019 §5.11 and the eight minimum and maximum operations of §9.6 are
built on it. `Datum.totalOrder` (§5.10) compares keys with a rational component. Lean's kernel
spends milliseconds on one rational comparison of two decimal data.

`KernelPath.compare` computes the same order on the fields of the data: two finite data are
aligned at the smaller of their two quantum exponents, where their coefficients are natural
numbers, and compared by their signs and two natural-number comparisons. `compare_eq` proves it
equal to `Datum.compare` for every pair of data, with no hypothesis on a format.

The rules tagged `@[kernel_optimize]`, which `float_decide` rewrites with:

* `compareQuiet_eq` and `compareSignaling_eq`: the two families of comparisons with the kernel
  comparison. The 22 members under their names are unfolded to their family.
* `totalOrder_eq`: the total order of IEEE 754-2019 §5.10, specified on lexicographic keys with
  a rational component, as `KernelPath.totalOrder`: the classes of the two data by their
  constructors and signs, two finite data of one sign by the kernel comparison and then by
  their quantum exponents, and two NaNs of one sign by their signaling state and payload.
  `Datum.totalOrderMag` is unfolded to the total order of the absolute values.
* `extremum_eq`: the minimum and maximum operations as `KernelPath.extremum`, which selects
  between two data that are not NaNs with the kernel comparison, orders two operands of equal
  value with the kernel total order, and leaves a NaN operand to the specification, a match
  on constructors. The eight members `Arithmetic.minimum` to
  `Arithmetic.maximumMagnitudeNumber` are unfolded to `Arithmetic.extremum`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics

/-! ## The order of two data on their fields -/

/-- The ordering of two natural numbers, by two comparisons (`compareNat_eq`). -/
def compareNat (a b : Nat) : Ordering :=
  Bool.casesOn (motive := fun _ => Ordering) (Nat.ble a b) .gt
    (Bool.casesOn (motive := fun _ => Ordering) (Nat.ble b a) .lt .eq)

/--
The ordering of two finite data with signs `s` and `t` whose coefficients `c` and `d` stand at
exponents `above` and `below` apart, one of the two being zero: the coefficients are aligned at
the smaller exponent and compared by their signs, and two zeros are equal.
-/
def compareFinite (s : Bool) (c : Nat) (t : Bool) (d : Nat) (above below : Nat) : Ordering :=
  (fun a b =>
    Bool.casesOn (motive := fun _ => Ordering) s
      (Bool.casesOn (motive := fun _ => Ordering) t (compareNat a b)
        (Bool.casesOn (motive := fun _ => Ordering) (Nat.beq (Nat.add a b) 0) .gt .eq))
      (Bool.casesOn (motive := fun _ => Ordering) t
        (Bool.casesOn (motive := fun _ => Ordering) (Nat.beq (Nat.add a b) 0) .lt .eq)
        (compareNat b a)))
    (Nat.mul c (Nat.pow 10 above)) (Nat.mul d (Nat.pow 10 below))

/--
Kernel form of `Datum.compare` (`compare_eq`): `none` when either datum is a NaN, an infinity
by its sign, and two finite data by `compareFinite` on the gaps of their exponents.
-/
def compare (x y : Datum) : Option Ordering :=
  Datum.casesOn (motive := fun _ => Option Ordering) x
    (fun s c q => Datum.casesOn (motive := fun _ => Option Ordering) y
      (fun t d r => some (gaps q r fun above below => compareFinite s c t d above below))
      (fun t => some (Bool.casesOn (motive := fun _ => Ordering) t .lt .gt))
      (fun _ _ _ => none))
    (fun s => Datum.casesOn (motive := fun _ => Option Ordering) y
      (fun _ _ _ => some (Bool.casesOn (motive := fun _ => Ordering) s .gt .lt))
      (fun t => some
        (Bool.casesOn (motive := fun _ => Ordering) s
          (Bool.casesOn (motive := fun _ => Ordering) t .eq .gt)
          (Bool.casesOn (motive := fun _ => Ordering) t .lt .eq)))
      (fun _ _ _ => none))
    (fun _ _ _ => none)

/-- `compareNat` is the comparison of natural numbers. -/
theorem compareNat_eq (a b : Nat) : compareNat a b = Ord.compare a b := by
  have hfalse : ∀ {m n : Nat}, n < m → Nat.ble m n = false := fun h => by
    rw [← Bool.not_eq_true, Nat.ble_eq]
    omega
  unfold compareNat
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, Nat.ble_eq_true_of_le h.le, hfalse h]
  · subst h
    rw [compare_eq_iff_eq.mpr rfl, Nat.ble_eq_true_of_le le_rfl]
  · rw [compare_gt_iff_gt.mpr h, hfalse h]

/-- The ordering of two rationals from the ordering of two naturals that they follow. -/
theorem compare_of_nat {a b : ℚ} {m n : Nat} (hlt : m < n → a < b) (heq : m = n → a = b)
    (hgt : n < m → b < a) : Ord.compare a b = Ord.compare m n := by
  rcases lt_trichotomy m n with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (hlt h)]
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr (heq h)]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (hgt h)]

/--
The exact order of two finite values is `compareFinite` on the gaps of their exponents, for all
signs, coefficients and exponents.
-/
theorem compare_finiteValue (s t : Bool) (c d : Nat) (q r : Int) :
    Ord.compare (Datum.finiteValue s c q) (Datum.finiteValue t d r) =
      compareFinite s c t d (q - r).toNat (r - q).toNat := by
  have hq : (q - min q r).toNat = (q - r).toNat := by omega
  have hr : (r - min q r).toNat = (r - q).toNat := by omega
  rw [finiteValue_aligned s c (min_le_left q r), finiteValue_aligned t d (min_le_right q r), hq,
    hr]
  unfold compareFinite
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Datum.finiteValue]
  generalize c * 10 ^ (q - r).toNat = a
  generalize d * 10 ^ (r - q).toNat = b
  have hpos : (0 : ℚ) < (10 : ℚ) ^ min q r := zpow_pos (by norm_num) _
  generalize (10 : ℚ) ^ min q r = scale at hpos ⊢
  have hmul : ∀ {m n : Nat}, m < n → (m : ℚ) * scale < n * scale := fun h =>
    mul_lt_mul_of_pos_right (Nat.cast_lt.mpr h) hpos
  have hsum : a + b ≠ 0 → -((b : ℚ) * scale) < a * scale ∧ -((a : ℚ) * scale) < b * scale := by
    intro hzero
    have hcast : (0 : ℚ) < ((a + b : Nat) : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
    have hprod := mul_pos hcast hpos
    rw [Nat.cast_add, add_mul] at hprod
    constructor <;> linarith
  have hbeq : a + b ≠ 0 → Nat.beq (a + b) 0 = false := fun hzero => by
    rw [← Bool.not_eq_true, Nat.beq_eq]
    exact hzero
  cases s <;> cases t <;>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul]
  · rw [compareNat_eq]
    exact compare_of_nat hmul (fun h => by rw [h]) hmul
  · by_cases hzero : a + b = 0
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      simp
    · rw [hbeq hzero]
      exact compare_gt_iff_gt.mpr (hsum hzero).1
  · by_cases hzero : a + b = 0
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      simp
    · rw [hbeq hzero]
      exact compare_lt_iff_lt.mpr (hsum hzero).2
  · rw [compareNat_eq]
    exact compare_of_nat (fun h => neg_lt_neg (hmul h)) (fun h => by rw [h])
      (fun h => neg_lt_neg (hmul h))

/-- The order of two rationals is the order of their images among the extended values. -/
theorem compare_coe (a b : ℚ) :
    Ord.compare (((a : WithTop ℚ) : NumericValue)) (((b : WithTop ℚ) : NumericValue)) =
      Ord.compare a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h,
      compare_lt_iff_lt.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h))]
  · subst h
    rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h,
      compare_gt_iff_gt.mpr (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h))]

/-- A rational lies below the positive infinity of the extended values. -/
theorem coe_lt_top (a : ℚ) : (((a : WithTop ℚ) : NumericValue)) < ⊤ :=
  WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top a)

/-- `KernelPath.compare` is `Datum.compare`, for every pair of data. -/
theorem compare_eq (x y : Datum) : Datum.compare x y = compare x y := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> rcases y with ⟨t', d, r⟩ | t' | ⟨s', t', p'⟩
  · change some (Ord.compare _ _) = some (gaps q r fun above below => _)
    rw [gaps_eq, ← compare_finiteValue, compare_coe]
  · cases t' <;> simp [Datum.compare, Datum.numericValue?, compare, compare_lt_iff_lt,
      compare_gt_iff_gt, coe_lt_top]
  · rfl
  · cases s <;> simp [Datum.compare, Datum.numericValue?, compare, compare_lt_iff_lt,
      compare_gt_iff_gt, coe_lt_top]
  · cases s <;> cases t' <;> simp [Datum.compare, Datum.numericValue?, compare,
      compare_lt_iff_lt, compare_gt_iff_gt]
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## Comparisons (IEEE 754-2019 §5.11) -/

/-- A quiet decimal comparison is its predicate at the kernel comparison of the two data. -/
@[kernel_optimize] theorem compareQuiet_eq (predicate : IEEEComparison.Predicate)
    (x y : Datum) :
    Datum.compareQuiet predicate x y =
      { value := predicate.accepts (compare x y)
        status := { invalid := x.isSignaling || y.isSignaling } } := by
  unfold Datum.compareQuiet
  rw [compare_eq]

/-- A signaling decimal comparison is its predicate at the kernel comparison of the two data. -/
@[kernel_optimize] theorem compareSignaling_eq (predicate : IEEEComparison.Predicate)
    (x y : Datum) :
    Datum.compareSignaling predicate x y =
      { value := predicate.accepts (compare x y)
        status := { invalid := x.isNaN || y.isNaN } } := by
  unfold Datum.compareSignaling
  rw [compare_eq]

/-! ## The total order (§5.10) -/

/--
The total order of two finite data of one sign `s` whose exponents are `above` and `below`
apart: by the order of their values, and between equal values the smaller quantum exponent
first for positive data and the larger first for negative data.
-/
def totalOrderFinite (s : Bool) (c d : Nat) (above below : Nat) : Bool :=
  Ordering.casesOn (motive := fun _ => Bool) (compareFinite s c s d above below) true
    (Nat.beq (Bool.casesOn (motive := fun _ => Nat) s above below) 0) false

/--
Kernel form of `Datum.totalOrder` (`totalOrder_eq`): negative NaNs, `-∞`, negative finite
data, positive finite data, `+∞` and positive NaNs in this order; two finite data of one sign
by `totalOrderFinite`; and two NaNs of one sign by their signaling state and then by their
payload, a signaling NaN and a smaller payload first when positive and last when negative.
-/
def totalOrder (x y : Datum) : Bool :=
  Datum.casesOn (motive := fun _ => Bool) x
    (fun s c q => Datum.casesOn (motive := fun _ => Bool) y
      (fun t d r =>
        Bool.casesOn (motive := fun _ => Bool) s
          (Bool.casesOn (motive := fun _ => Bool) t
            (gaps q r fun above below => totalOrderFinite false c d above below) false)
          (Bool.casesOn (motive := fun _ => Bool) t true
            (gaps q r fun above below => totalOrderFinite true c d above below)))
      (fun t => Bool.casesOn (motive := fun _ => Bool) t true false)
      (fun t _ _ => Bool.casesOn (motive := fun _ => Bool) t true false))
    (fun s => Datum.casesOn (motive := fun _ => Bool) y
      (fun _ _ _ => s)
      (fun t => Bool.casesOn (motive := fun _ => Bool) s
        (Bool.casesOn (motive := fun _ => Bool) t true false) true)
      (fun t _ _ => Bool.casesOn (motive := fun _ => Bool) t true false))
    (fun s tx p => Datum.casesOn (motive := fun _ => Bool) y
      (fun _ _ _ => s)
      (fun _ => s)
      (fun t ty p' =>
        Bool.casesOn (motive := fun _ => Bool) s
          (Bool.casesOn (motive := fun _ => Bool) t
            (Bool.casesOn (motive := fun _ => Bool) tx
              (Bool.casesOn (motive := fun _ => Bool) ty (Nat.ble p p') false)
              (Bool.casesOn (motive := fun _ => Bool) ty true (Nat.ble p p')))
            false)
          (Bool.casesOn (motive := fun _ => Bool) t true
            (Bool.casesOn (motive := fun _ => Bool) tx
              (Bool.casesOn (motive := fun _ => Bool) ty (Nat.ble p' p) true)
              (Bool.casesOn (motive := fun _ => Bool) ty false (Nat.ble p' p))))))

/--
`totalOrderFinite` decides the lexicographic order of two finite data of one sign: the values
first, and then the quantum exponents, reversed for negative data.
-/
theorem totalOrderFinite_eq (s : Bool) (c d : Nat) (q r : Int) :
    totalOrderFinite s c d (q - r).toNat (r - q).toNat =
      decide (Datum.finiteValue s c q < Datum.finiteValue s d r ∨
        Datum.finiteValue s c q = Datum.finiteValue s d r ∧ if s then r ≤ q else q ≤ r) := by
  unfold totalOrderFinite
  rw [← compare_finiteValue]
  rcases lt_trichotomy (Datum.finiteValue s c q) (Datum.finiteValue s d r) with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    simp [h]
  · rw [compare_eq_iff_eq.mpr h]
    have habove : Nat.beq (q - r).toNat 0 = decide (q ≤ r) := by
      rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
      omega
    have hbelow : Nat.beq (r - q).toNat 0 = decide (r ≤ q) := by
      rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
      omega
    cases s <;> simp [h, habove, hbelow]
  · rw [compare_gt_iff_gt.mpr h]
    simp [h.not_gt, h.ne']

/-- `KernelPath.totalOrder` is `Datum.totalOrder`, for every pair of data. -/
@[kernel_optimize] theorem totalOrder_eq (x y : Datum) :
    Datum.totalOrder x y = totalOrder x y := by
  unfold Datum.totalOrder
  rcases x with ⟨s, c, q⟩ | s | ⟨s, tx, p⟩ <;> rcases y with ⟨t, d, r⟩ | t | ⟨t, ty, p'⟩
  · cases s <;> cases t
    · change _ = gaps q r fun above below => totalOrderFinite false c d above below
      rw [gaps_eq, totalOrderFinite_eq]
      simp [Datum.orderKey, Prod.Lex.toLex_le_toLex]
    · simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
    · simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
    · change _ = gaps q r fun above below => totalOrderFinite true c d above below
      rw [gaps_eq, totalOrderFinite_eq]
      simp [Datum.orderKey, Prod.Lex.toLex_le_toLex]
  · cases s <;> cases t <;> simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
  · cases s <;> cases t <;> simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
  · cases s <;> cases t <;> simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
  · cases s <;> cases t <;> simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
  · cases s <;> cases t <;> simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
  · cases s <;> cases t <;> simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
  · cases s <;> cases t <;> simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex]
  · cases s <;> cases t <;> cases tx <;> cases ty <;>
      simp [Datum.orderKey, totalOrder, Prod.Lex.toLex_le_toLex, natBle_eq]

/-! ## Minimum and maximum (§9.6) -/

/--
Kernel form of `Arithmetic.selectExtremum` (`selectExtremum_eq`): the selection by the kernel
comparison, and by the kernel total order between two data of equal value.
-/
def selectExtremum (larger : Bool) (x y : Datum) : Datum :=
  match compare x y with
  | some .lt => if larger then y else x
  | some .gt => if larger then x else y
  | _ => if totalOrder x y = larger then y else x

/--
Kernel form of `Arithmetic.selectByMagnitude` (`selectByMagnitude_eq`): the selection by the
kernel comparison of the absolute values, and `selectExtremum` between equal magnitudes.
-/
def selectByMagnitude (larger : Bool) (x y : Datum) : Datum :=
  match compare x.abs y.abs with
  | some .lt => if larger then y else x
  | some .gt => if larger then x else y
  | _ => selectExtremum larger x y

/--
Kernel form of `Arithmetic.extremum` (`extremum_eq`): two data that are not NaNs are selected
with the kernel comparison, and a NaN operand is left to the specification.
-/
def extremum (f : Format) (larger magnitude number : Bool) (x y : Datum) : Outcome :=
  Bool.casesOn (motive := fun _ => Outcome) (x.isNaN || y.isNaN)
    { value := Bool.casesOn (motive := fun _ => Datum) magnitude (selectExtremum larger x y)
        (selectByMagnitude larger x y) }
    (Arithmetic.extremum f larger magnitude number x y)

/-- `KernelPath.selectExtremum` is `Arithmetic.selectExtremum`. -/
theorem selectExtremum_eq (larger : Bool) (x y : Datum) :
    Arithmetic.selectExtremum larger x y = selectExtremum larger x y := by
  unfold Arithmetic.selectExtremum selectExtremum
  rw [compare_eq, totalOrder_eq]
  rfl

/-- `KernelPath.selectByMagnitude` is `Arithmetic.selectByMagnitude`. -/
theorem selectByMagnitude_eq (larger : Bool) (x y : Datum) :
    Arithmetic.selectByMagnitude larger x y = selectByMagnitude larger x y := by
  unfold Arithmetic.selectByMagnitude selectByMagnitude
  rw [compare_eq, selectExtremum_eq]
  rfl

/--
The minimum and maximum operations of IEEE 754-2019 §9.6 on decimal data are
`KernelPath.extremum`, for every format, every selection and every pair of data.
-/
@[kernel_optimize] theorem extremum_eq (f : Format) (larger magnitude number : Bool)
    (x y : Datum) :
    Arithmetic.extremum f larger magnitude number x y =
      extremum f larger magnitude number x y := by
  unfold extremum
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> rcases y with ⟨t', d, r⟩ | t' | ⟨s', t', p'⟩ <;>
    first
    | rfl
    | (cases magnitude <;>
        simp [Arithmetic.extremum, Datum.isNaN, selectExtremum_eq, selectByMagnitude_eq])

/-! ## Kernel shapes -/

kernel_shape compareNat
kernel_shape compareFinite
kernel_shape compare
kernel_shape totalOrderFinite
kernel_shape totalOrder
kernel_shape selectExtremum
kernel_shape selectByMagnitude
kernel_shape extremum

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath

/-
The members under the names of the standard are their family at one predicate or selection:
`float_decide` unfolds them, and the rules of the family apply.
-/
ieee_tag_members [kernel_optimize unfold]
  FloatLib.Floats.Formats.DecimalInterchange.Datum.compareQuiet
  by predicate

ieee_tag_members [kernel_optimize unfold]
  FloatLib.Floats.Formats.DecimalInterchange.Datum.compareSignaling
  by predicate without unordered ordered

ieee_tag_members [kernel_optimize unfold] FloatLib.Floats.Formats.DecimalInterchange.Arithmetic
  by extremum

attribute [kernel_optimize unfold] FloatLib.Floats.Formats.DecimalInterchange.Datum.totalOrderMag
