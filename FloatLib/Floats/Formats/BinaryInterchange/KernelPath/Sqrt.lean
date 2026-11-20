/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Reference

/-!
# Kernel square root on encodings

`sqrt fmt mode a` is the encoding of the square root of the value encoded by `a`, rounded in the
direction `mode`, computed with natural-number operations that Lean's kernel accelerates.

For a finite positive nonzero operand in a format with `fracWidth + 1 ≤ exponentBias`, the root
is a normal number. The significand is shifted so that its integer square root has
`fracWidth + 1` bits. Eight Newton steps from `2 ^ (fracWidth + 1)` find that root, one
correction step brings a root that is one too large back, and the result is checked:
`r * r ≤ N < (r + 1) * (r + 1)`. The remainder decides the rounding (`rootUp`): above the root
in the two nearest directions (an exact square root is never a tie), nonzero in the directions
that round a positive value up, never in the directions that round it down. The exponent field
and the rounded root are packed with one addition.

A zero, a negative value, an infinity and a NaN are answered by `sqrtSpecial` with a few
comparisons. Eight steps are enough for a fraction of about 380 bits. A root that fails its
check is computed again with sixteen steps and checked again (`sqrtRetry`), which is enough for
a fraction of tens of thousands of bits and costs the narrower formats nothing. A format with a
smaller bias and a root that fails both checks take the reference square root on the encoding,
so `sqrt_eq_spec` holds for every descriptor, every rounding direction and every operand without
a convergence argument.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The reference square root in the direction `mode`, in the form the kernel evaluates: the
nearest-even specification in both nearest directions and the directed kernel otherwise
(`referenceRoot_eq`).
-/
def referenceRoot {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model fmt) :
    Model fmt :=
  match mode with
  | .nearest | .nearestAway => Model.Spec.sqrt x
  | .towardZero => Model.Internal.Directed.sqrt .towardZero x
  | .up => Model.Internal.Directed.sqrt .up x
  | .down => Model.Internal.Directed.sqrt .down x
  | .away => Model.Internal.Directed.sqrt .away x

/-- `referenceRoot` is the reference square root in every direction. -/
theorem referenceRoot_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model fmt) :
    referenceRoot mode x = Model.sqrt x (mode := mode) := by
  cases mode
  case nearest => exact (Model.Proof.sqrt_eq_spec x).symm
  case nearestAway => exact (Model.Proof.sqrt_eq_spec x).symm
  all_goals rfl

/-- The encoding of the reference square root of the value encoded by `a`, in a direction. -/
def sqrtReference (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (referenceRoot mode (Model.ofNatBits (fmt := fmt) a)).toNatBits

/--
The square root of a word outside the checked path, by the rules of the reference square root:
a NaN is quieted, the positive infinity and the zeros are returned, a negative value and the
negative infinity give the invalid result. A positive finite value takes `sqrtReference`.
-/
def sqrtSpecial (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (fun s u =>
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (nanFlag fmt s u) 0)
      (Nat.lor a (quietMask fmt))
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (infFlag fmt u) 0)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq s 0)
          (invalidWord fmt) (overflowWord fmt false))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (zeroFlag fmt s u) 0)
          a
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq s 0)
            (invalidWord fmt) (sqrtReference fmt mode a)))))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

kernel_constant sqrtSpecial

/-- Zero when `fracWidth + 1 ≤ exponentBias`, the formats whose roots are all normal. -/
def sqrtSlow (fmt : FloatFormat) : Nat :=
  Nat.sub (Nat.succ fmt.fracWidth) fmt.exponentBias

kernel_constant sqrtSlow

/-- One Newton step toward the integer square root of `N`. -/
def newton (N x : Nat) : Nat :=
  Nat.shiftRight (Nat.add x (Nat.div N x)) 1

/-- Eight Newton steps from `2 ^ (fracWidth + 1)`, which lies above the root of `N`. -/
def newtonRoot (fmt : FloatFormat) (N : Nat) : Nat :=
  newton N (newton N (newton N (newton N (newton N (newton N (newton N (newton N
    (Nat.shiftLeft 1 (Nat.succ fmt.fracWidth)))))))))

/-- The integer square root of `N` rounded to nearest: one more when `N` is above the midpoint. -/
def roundedRoot (N : Nat) : Nat :=
  if N - Nat.sqrt N * Nat.sqrt N ≤ Nat.sqrt N then Nat.sqrt N else Nat.sqrt N + 1

/--
One when the root `r` of a radicand with remainder `rem` rounds up in the direction `mode` for a
positive result, and zero when it stays: above the midpoint in the two nearest directions, never
toward zero and down, and for a nonzero remainder up and away from zero.
-/
def rootUp (mode : Model.IEEERoundingMode) (r rem : Nat) : Nat :=
  Model.IEEERoundingMode.casesOn (motive := fun _ => Nat) mode
    (Nat.sub 1 (Nat.sub 1 (Nat.sub rem r)))
    (Nat.sub 1 (Nat.sub 1 (Nat.sub rem r)))
    0
    (Nat.sub 1 (Nat.sub 1 rem))
    0
    (Nat.sub 1 (Nat.sub 1 rem))

/-- The integer square root of `N` rounded in the direction `mode` for a positive result. -/
def directedRoot (mode : Model.IEEERoundingMode) (N : Nat) : Nat :=
  Nat.sqrt N + rootUp mode (Nat.sqrt N) (N - Nat.sqrt N * Nat.sqrt N)

/--
The packed root of the scaled significand `N` with exponent field `q` before a rounding carry,
from a candidate `x` for the integer square root: `special` unless `guard` is zero and `x`,
lowered by one when its square exceeds `N`, passes the check `r * r ≤ N < (r + 1) * (r + 1)`.
-/
def sqrtChecked (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (N q guard special x : Nat) :
    Nat :=
  (fun r =>
    Bool.casesOn (motive := fun _ => Nat)
      (Nat.beq
        (Nat.add guard
          (Nat.add (Nat.sub (Nat.mul r r) N)
            (Nat.sub (Nat.succ N) (Nat.mul (Nat.succ r) (Nat.succ r)))))
        0)
      special
      (Nat.add (Nat.shiftLeft (Nat.sub q 1) fmt.fracWidth)
        (Nat.add r (rootUp mode r (Nat.sub N (Nat.mul r r))))))
    (Nat.sub x (Nat.sub 1 (Nat.sub 1 (Nat.sub (Nat.mul x x) N))))

/--
The second attempt at a root whose first candidate failed its check: sixteen Newton steps from
`2 ^ (fracWidth + 1)`, checked again. A wide format takes this path, since eight steps do not
reach the precision of a fraction of more than about 380 bits.
-/
def sqrtRetry (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (N q special : Nat) : Nat :=
  sqrtChecked fmt mode N q 0 special
    (newton N (newton N (newton N (newton N (newton N (newton N (newton N (newton N
      (newtonRoot fmt N)))))))))

/--
The square root of the scaled significand `N` with exponent field `q` before a rounding carry:
`special` unless `guard` is zero and the Newton root passes its check, at the first attempt or
after the refinement of `sqrtRetry`.
-/
def sqrtCore (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (N q guard special : Nat) :
    Nat :=
  sqrtChecked fmt mode N q guard
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq guard 0)
      special
      (sqrtRetry fmt mode N q special))
    (newtonRoot fmt N)

/--
Square root on encodings, rounded in the direction `mode`. See the module documentation.
-/
def sqrt (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a : Nat) : Nat :=
  (fun s u =>
    (fun h =>
      (fun m =>
        (fun L =>
          (fun num =>
            sqrtCore fmt mode
              (Nat.shiftLeft m
                (Nat.sub (Nat.add (Nat.land num 1) (Nat.succ (Nat.mul 2 fmt.fracWidth))) L))
              (Nat.shiftRight num 1)
              (Nat.add
                (Nat.add (Nat.add (nonFinite fmt s u) s) (Nat.add (Nat.sub 1 m) (sqrtSlow fmt)))
                (Nat.sub (Nat.succ (Nat.shiftRight num 1)) fmt.maxFiniteExpField))
              (sqrtSpecial fmt mode a))
            (Nat.add (Nat.add L h) (Nat.sub fmt.exponentBias fmt.fracWidth)))
          (significandLength fmt.fracWidth m))
        (Nat.sub u (Nat.shiftLeft h fmt.fracWidth)))
      (Nat.sub (Nat.shiftRight u fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.land a (magnitudeMask fmt))

/-! ## The checked root -/

/--
`sqrtChecked` returns `special` whenever the packed rounded root is `special` on the checked
path. Nothing is assumed about the candidate `x`: a root that fails its check selects `special`.
-/
theorem sqrtChecked_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (N q guard special x : Nat)
    (hfast : guard = 0 → special = (q - 1) * 2 ^ fmt.fracWidth + directedRoot mode N) :
    sqrtChecked fmt mode N q guard special x = special := by
  unfold sqrtChecked
  dsimp only
  generalize Nat.sub x (Nat.sub 1 (Nat.sub 1 (Nat.sub (Nat.mul x x) N))) = r
  cases hcheck : Nat.beq
      (Nat.add guard
        (Nat.add (Nat.sub (Nat.mul r r) N)
          (Nat.sub (Nat.succ N) (Nat.mul (Nat.succ r) (Nat.succ r)))))
      0
  · rfl
  · have hzero : guard + (r * r - N + (N + 1 - (r + 1) * (r + 1))) = 0 :=
      Nat.eq_of_beq_eq_true hcheck
    obtain ⟨hguard, _⟩ := Nat.eq_zero_of_add_eq_zero hzero
    have hr : r = Nat.sqrt N := Nat.eq_sqrt.mpr ⟨by omega, by omega⟩
    change (q - 1) <<< fmt.fracWidth + (r + rootUp mode r (N - r * r)) = special
    rw [hfast hguard, directedRoot, ← hr, Nat.shiftLeft_eq]

/--
`sqrtCore` returns `special` whenever the packed rounded root is `special` on the checked path,
whatever the Newton steps and the refinement deliver.
-/
theorem sqrtCore_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (N q guard special : Nat)
    (hfast : guard = 0 → special = (q - 1) * 2 ^ fmt.fracWidth + directedRoot mode N) :
    sqrtCore fmt mode N q guard special = special := by
  have hretry : Bool.casesOn (motive := fun _ => Nat) (Nat.beq guard 0) special
      (sqrtRetry fmt mode N q special) = special := by
    cases hguard : Nat.beq guard 0
    · rfl
    · exact sqrtChecked_eq fmt mode N q 0 special _
        (fun _ => hfast (Nat.eq_of_beq_eq_true hguard))
  exact (congrArg (fun s => sqrtChecked fmt mode N q guard s (newtonRoot fmt N)) hretry).trans
    (sqrtChecked_eq fmt mode N q guard special _ hfast)

/-- In the nearest-even direction the directed root is the root rounded to nearest. -/
theorem directedRoot_nearest (N : Nat) : directedRoot .nearest N = roundedRoot N := by
  unfold directedRoot roundedRoot
  change Nat.sqrt N + (1 - (1 - (N - Nat.sqrt N * Nat.sqrt N - Nat.sqrt N))) = _
  split <;> omega

/-- Away from zero on ties the directed root is the root rounded to nearest: no tie occurs. -/
theorem directedRoot_nearestAway (N : Nat) : directedRoot .nearestAway N = roundedRoot N :=
  directedRoot_nearest N

/-- The root rounded up: one more than the integer root unless the radicand is a square. -/
theorem directedRoot_up (N : Nat) :
    directedRoot .up N =
      if N - Nat.sqrt N * Nat.sqrt N = 0 then Nat.sqrt N else Nat.sqrt N + 1 := by
  unfold directedRoot
  change Nat.sqrt N + (1 - (1 - (N - Nat.sqrt N * Nat.sqrt N))) = _
  split <;> omega

/-! ## The reference root of a normalizable significand -/

/-- The largest finite exponent field of a conventional IEEE format is twice its bias. -/
theorem maxFiniteExpField_of_isIEEE (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    fmt.maxFiniteExpField = 2 * fmt.bias := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hpow := fmt.two_pow_expWidth_eq_two_mul_bias_add_two
  simp only [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent, hencoding]
  omega

/--
The rounded root of a radicand with `2 * f + 1` or `2 * f + 2` bits has `f + 1` bits or is
`2 ^ (f + 1)`.
-/
theorem roundedRoot_bounds (f N : Nat) (hlow : 2 ^ f ≤ Nat.sqrt N)
    (hhigh : Nat.sqrt N < 2 ^ (f + 1)) :
    2 ^ f ≤ roundedRoot N ∧ roundedRoot N ≤ 2 ^ (f + 1) := by
  unfold roundedRoot
  split <;> omega

/--
The encoding of the reference square root of `m * 2 ^ (scale + minSubnormalExponent)`, for a
nonzero significand below `2 ^ (fracWidth + 1)` in a format with `fracWidth + 1 ≤ exponentBias`,
when the exponent field of the root stays finite: the exponent field before a rounding carry is
`num / 2` for `num = log2 m + 1 + scale + (exponentBias - fracWidth)`, and the significand is
the rounded integer root of `m` shifted to `2 * fracWidth + 1 + num % 2` bits.
-/
theorem sqrtPositiveDyadic_bits (fmt : FloatFormat) (m scale : Nat) (hm : m ≠ 0)
    (hmlt : m < 2 ^ (fmt.fracWidth + 1)) (hbias : fmt.fracWidth + 1 ≤ fmt.exponentBias)
    (hq : (m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) / 2 + 1 ≤
      fmt.maxFiniteExpField) :
    (Model.FiniteSqrt.sqrtPositiveDyadic fmt m
        ((scale : Int) + fmt.minSubnormalExponent)).toNatBits =
      ((m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) / 2 - 1) * 2 ^ fmt.fracWidth +
        roundedRoot (m <<< ((m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) % 2 +
          (2 * fmt.fracWidth + 1) - (m.log2 + 1))) := by
  have hf := fmt.fracWidth_pos
  have hleading : m.log2 ≤ fmt.fracWidth := by
    have := (Nat.log2_lt hm).2 hmlt
    omega
  have hmaxlt := fmt.maxFiniteExpField_lt_two_pow
  generalize hnum : m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth) = num at hq ⊢
  generalize hshift : num % 2 + (2 * fmt.fracWidth + 1) - (m.log2 + 1) = shift
  have hshiftLower : 2 * fmt.fracWidth ≤ m.log2 + shift := by omega
  have hshiftUpper : m.log2 + 1 + shift ≤ 2 * fmt.fracWidth + 2 := by omega
  obtain ⟨-, -, hrootLow, hrootHigh⟩ :=
    Model.sqrt_shiftLeft_bounds fmt.fracWidth m shift hm hshiftLower hshiftUpper
  obtain ⟨hroundedLow, hroundedHigh⟩ := roundedRoot_bounds fmt.fracWidth _ hrootLow hrootHigh
  have hqpos : 1 ≤ num / 2 := by omega
  have hexp : (scale : Int) + fmt.minSubnormalExponent =
      Int.ofNat scale - Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) := by
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have hnumInt : (Int.ofNat m.log2 + Int.ofNat scale +
      Int.ofNat (fmt.exponentBias + 1 - fmt.fracWidth)).ediv 2 = Int.ofNat (num / 2) := by
    simp only [Int.ofNat_eq_natCast, ← Int.div_def]
    omega
  have key := FloatLib.Floats.ExecFloat.Backends.Compiled.SqrtArithmetic.target_exponent
    m.log2 scale (fmt.exponentBias + fmt.fracWidth - 1) (fmt.exponentBias + 1 - fmt.fracWidth)
    fmt.exponentBias fmt.fracWidth hleading (by omega) (by omega)
  rw [hnumInt] at key
  have hshiftEq : (Int.ofNat scale - Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) -
      2 * (Int.ofNat (num / 2) - Int.ofNat fmt.exponentBias - fmt.fracWidth)).toNat = shift := by
    simp only [Int.ofNat_eq_natCast]
    lia
  have hpow2 : Model.pow2 fmt.fracWidth = 2 ^ fmt.fracWidth := Model.pow2_eq_two_pow _
  have hpow2' : Model.pow2 (fmt.fracWidth + 1) = 2 ^ (fmt.fracWidth + 1) :=
    Model.pow2_eq_two_pow _
  have hsplit : 2 ^ (fmt.fracWidth + 1) = 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
    rw [Nat.pow_succ]
    omega
  have hexpand : (num / 2) * 2 ^ fmt.fracWidth =
      (num / 2 - 1) * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
    obtain ⟨k, hk⟩ : ∃ k, num / 2 = k + 1 := ⟨num / 2 - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
  rw [hexp]
  unfold Model.FiniteSqrt.sqrtPositiveDyadic
  rw [dite_eq_right hm]
  by_cases hieee : fmt.isIEEE = true
  · have hbiasEq := FloatFormat.exponentBias_eq_bias_of_isIEEE fmt hieee
    have hmax := maxFiniteExpField_of_isIEEE fmt hieee
    rw [hbiasEq] at hshiftEq hbias
    have htarget :
        min ((Int.ofNat scale - Int.ofNat (fmt.bias + fmt.fracWidth - 1)).ediv 2)
            ((FloatFormat.toModel fmt).targetExponent
              ((Float.Model.totalExponent m
                (Int.ofNat scale - Int.ofNat (fmt.bias + fmt.fracWidth - 1)) + 1).ediv 2)) =
          Int.ofNat (num / 2) - Int.ofNat fmt.bias - fmt.fracWidth := by
      rw [Model.NativeSmallWordSqrt.target_exponent_eq fmt hbias m scale hleading,
        show (m.log2 + scale + (fmt.bias + 1 - fmt.fracWidth)) / 2 = num / 2 by lia]
    have hfields := Model.ofModel_sqrt_finite_positive_eq_ofFields fmt m shift (num / 2)
      (Int.ofNat scale - Int.ofNat (fmt.bias + fmt.fracWidth - 1)) (Nat.pos_of_ne_zero hm)
      hshiftLower hshiftUpper hqpos (by omega) htarget hshiftEq
    simp only [hieee, ite_true, Model.NativeModelSqrt.sqrt_eq, hbiasEq]
    rw [show Model.ofModel fmt _ = _ from hfields]
    change (Model.ofFields fmt false
        (num / 2 + if roundedRoot (m <<< shift) = Model.pow2 (fmt.fracWidth + 1) then 1 else 0)
        ((if roundedRoot (m <<< shift) = Model.pow2 (fmt.fracWidth + 1) then
            Model.pow2 fmt.fracWidth
          else roundedRoot (m <<< shift)) - Model.pow2 fmt.fracWidth)).toNatBits = _
    rw [hpow2, hpow2']
    by_cases hcarry : roundedRoot (m <<< shift) = 2 ^ (fmt.fracWidth + 1)
    · rw [ite_eq_left hcarry, ite_eq_left hcarry,
        toNatBits_ofFields fmt false _ _ (by omega) (by omega)]
      simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
      rw [hcarry, Nat.add_mul, Nat.one_mul, hexpand, hsplit, Nat.sub_self]
      omega
    · rw [ite_eq_right hcarry, ite_eq_right hcarry,
        toNatBits_ofFields fmt false _ _ (by omega) (by omega)]
      simp only [Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero]
      omega
  · have hfalse : fmt.isIEEE = false := Bool.eq_false_of_not_eq_true hieee
    have hfinal : Model.FiniteSqrt.targetExponent fmt m
        (Int.ofNat scale - Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1)) =
          Int.ofNat (num / 2) - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth := by
      simp only [Model.FiniteSqrt.targetExponent, FloatFormat.minSubnormalExponent,
        FloatFormat.minNormalExponent, Int.ofNat_eq_natCast, ← Int.div_def] at key ⊢
      lia
    have hrootExp : min ((Int.ofNat scale -
          Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1)).ediv 2)
        (Int.ofNat (num / 2) - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth) =
          Int.ofNat (num / 2) - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth := by
      simp only [Int.ofNat_eq_natCast, ← Int.div_def]
      lia
    simp only [hfalse, Bool.false_eq_true, ite_false, Model.FiniteSqrt.sqrtGeneral_eq_unscaled,
      beq_iff_eq, hm, hfinal, hrootExp, Int.sub_self, Int.toNat_zero]
    rw [show (Int.ofNat scale - Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) -
        2 * (Int.ofNat (num / 2) - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth)).toNat =
          shift from hshiftEq]
    have hround : Model.FiniteSqrt.roundRoot (Nat.sqrt (m <<< shift))
        (m <<< shift - Nat.sqrt (m <<< shift) * Nat.sqrt (m <<< shift)) 0 =
          roundedRoot (m <<< shift) := by
      unfold Model.FiniteSqrt.roundRoot roundedRoot
      by_cases hle : m <<< shift - Nat.sqrt (m <<< shift) * Nat.sqrt (m <<< shift) ≤
          Nat.sqrt (m <<< shift)
      · simp [hle]
      · have hne : m <<< shift - Nat.sqrt (m <<< shift) * Nat.sqrt (m <<< shift) ≠ 0 := by
          omega
        simp [hle, hne]
    rw [hround, ← congrFun (congrFun Model.roundDyadic_eq_internal fmt) _,
      ← Model.roundDyadicGeneral_eq_roundDyadic]
    have hdyadic : (Int.ofNat (num / 2) - Int.ofNat fmt.exponentBias - Int.ofNat fmt.fracWidth) =
        ((num / 2 - 1 : Nat) : Int) - (0 : Nat) + fmt.minSubnormalExponent := by
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      omega
    rw [hdyadic]
    by_cases hcarry : roundedRoot (m <<< shift) = 2 ^ (fmt.fracWidth + 1)
    · have hlog : (roundedRoot (m <<< shift)).log2 = fmt.fracWidth + 1 := by
        rw [hcarry, Nat.log2_two_pow]
      rw [roundDyadicGeneral_bits fmt false (roundedRoot (m <<< shift)) (num / 2 - 1) 0
        (by omega) (num / 2) (2 ^ fmt.fracWidth) (by omega) (by
          rw [hcarry, show num / 2 - 1 - (num / 2 + 0) = 0 by omega,
            show num / 2 + 0 - (num / 2 - 1) = 1 by omega, Nat.shiftLeft_zero,
            roundShiftRightEven_eq_roundQuotientEven, Nat.pow_one, hsplit]
          unfold roundQuotientEven
          have hdiv : (2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth) / 2 = 2 ^ fmt.fracWidth := by
            omega
          have hmod : (2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth) % 2 = 0 := by omega
          simp [hdiv, hmod])]
      have hpos : 2 ^ fmt.fracWidth ≠ 0 := (Nat.two_pow_pos _).ne'
      have hfin : num / 2 * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth ≤ maxFinite fmt := by
        have h := (le_maxFinite_iff fmt (num / 2 + 1) 0 (Nat.two_pow_pos _)).mpr (by
          rcases Nat.lt_or_ge (num / 2 + 1) fmt.maxFiniteExpField with h | h
          · exact Or.inl h
          · exact Or.inr ⟨by omega, Nat.zero_le _⟩)
        rw [Nat.add_mul, Nat.one_mul, Nat.add_zero] at h
        exact h
      rw [ite_eq_right hpos, ite_eq_left hfin, hcarry]
      simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
      omega
    · have hlt : roundedRoot (m <<< shift) < 2 ^ (fmt.fracWidth + 1) := by omega
      have hlog : (roundedRoot (m <<< shift)).log2 = fmt.fracWidth :=
        (Nat.log2_eq_iff (by omega)).mpr ⟨hroundedLow, hlt⟩
      rw [roundDyadicGeneral_bits fmt false (roundedRoot (m <<< shift)) (num / 2 - 1) 0
        (by omega) (num / 2 - 1) (roundedRoot (m <<< shift)) (by omega) (by
          rw [show num / 2 - 1 - (num / 2 - 1 + 0) = 0 by omega,
            show num / 2 - 1 + 0 - (num / 2 - 1) = 0 by omega, Nat.shiftLeft_zero,
            roundShiftRightEven_zero])]
      have hpos : roundedRoot (m <<< shift) ≠ 0 := by
        have := Nat.two_pow_pos fmt.fracWidth
        omega
      have hfin : (num / 2 - 1) * 2 ^ fmt.fracWidth + roundedRoot (m <<< shift) ≤
          maxFinite fmt := by
        have hfrac : roundedRoot (m <<< shift) - 2 ^ fmt.fracWidth < 2 ^ fmt.fracWidth := by
          omega
        have h := (le_maxFinite_iff fmt (num / 2)
          (roundedRoot (m <<< shift) - 2 ^ fmt.fracWidth) hfrac).mpr (Or.inl (by omega))
        omega
      rw [ite_eq_right hpos, ite_eq_left hfin]
      simp only [Bool.false_eq_true, ite_false, Nat.zero_add]

/-! ## The directed root of a normalizable significand -/

/-- An exact quotient is returned in every rounding direction. -/
theorem roundQuot_exact (mode : Model.IEEERoundingMode) (negative : Bool) (entropy num den : Nat)
    (h : num % den = 0) :
    Model.Policy.roundQuot mode.toRoundingMode negative entropy num den = num / den := by
  unfold Model.Policy.roundQuot
  simp [h]

/--
A positive significand of `fracWidth + 1` bits, or the next power of two, at the exponent of the
exponent field `t + 1` is a value of the format when that field stays finite: it rounds to
itself in every direction.
-/
theorem roundDyadic_exact (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (t r : Nat)
    (hlow : 2 ^ fmt.fracWidth ≤ r) (hhigh : r ≤ 2 ^ (fmt.fracWidth + 1))
    (ht : t + 2 ≤ fmt.maxFiniteExpField) :
    (Model.Internal.Directed.roundDyadic fmt mode
        ⟨false, r, (t : Int) - (0 : Nat) + fmt.minSubnormalExponent⟩).toNatBits =
      t * 2 ^ fmt.fracWidth + r := by
  have hF := Nat.two_pow_pos fmt.fracWidth
  have hsplit : 2 ^ (fmt.fracWidth + 1) = 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
    rw [Nat.pow_succ]
    omega
  have hr0 : r ≠ 0 := by omega
  by_cases hcarry : r = 2 ^ (fmt.fracWidth + 1)
  · have hlog : r.log2 = fmt.fracWidth + 1 := by rw [hcarry, Nat.log2_two_pow]
    have hmod : r % 2 = 0 := by
      rw [hcarry, Nat.pow_succ]
      exact Nat.mul_mod_left _ _
    have hdiv : r / 2 = 2 ^ fmt.fracWidth := by
      rw [hcarry, Nat.pow_succ]
      exact Nat.mul_div_cancel _ (by decide)
    rw [roundDyadic_bits fmt mode 0 false r t 0 hr0 (t + 1) (2 ^ fmt.fracWidth) (by omega) (by
      rw [show t - (t + 1 + 0) = 0 by omega, show t + 1 + 0 - t = 1 by omega,
        Nat.shiftLeft_zero, Nat.pow_one, roundQuot_exact _ _ _ _ _ hmod, hdiv])]
    have hfin : (t + 1) * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth ≤ maxFinite fmt := by
      have h := (le_maxFinite_iff fmt (t + 2) 0 hF).mpr (by
        rcases Nat.lt_or_ge (t + 2) fmt.maxFiniteExpField with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, Nat.zero_le _⟩)
      have hexpand : (t + 2) * 2 ^ fmt.fracWidth =
          (t + 1) * 2 ^ fmt.fracWidth + 2 ^ fmt.fracWidth := by
        rw [show t + 2 = t + 1 + 1 by omega, Nat.add_mul (t + 1), Nat.one_mul]
      omega
    rw [ite_eq_right hF.ne', ite_eq_left hfin, hcarry, hsplit]
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hlt : r < 2 ^ (fmt.fracWidth + 1) := by omega
    have hlog : r.log2 = fmt.fracWidth := (Nat.log2_eq_iff hr0).mpr ⟨hlow, hlt⟩
    rw [roundDyadic_bits fmt mode 0 false r t 0 hr0 t r (by omega) (by
      rw [show t - (t + 0) = 0 by omega, show t + 0 - t = 0 by omega, Nat.shiftLeft_zero,
        Nat.pow_zero, roundQuot_exact _ _ _ _ _ (Nat.mod_one _), Nat.div_one])]
    have hfin : t * 2 ^ fmt.fracWidth + r ≤ maxFinite fmt := by
      have hfrac : r - 2 ^ fmt.fracWidth < 2 ^ fmt.fracWidth := by omega
      have h := (le_maxFinite_iff fmt (t + 1) (r - 2 ^ fmt.fracWidth) hfrac).mpr
        (Or.inl (by omega))
      rw [Nat.add_mul, Nat.one_mul] at h
      omega
    rw [ite_eq_right hr0, ite_eq_left hfin]
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]

/--
The enclosure of the square root of `m * 2 ^ (scale + minSubnormalExponent)`, for a nonzero
significand below `2 ^ (fracWidth + 1)` in a format with `fracWidth + 1 ≤ exponentBias`, in the
quantities `sqrt` computes. Both endpoints have the exponent of the exponent field `num / 2`
before a rounding carry, for `num = log2 m + 1 + scale + (exponentBias - fracWidth)`. The lower
one is the integer root of `m` shifted to `2 * fracWidth + 1 + num % 2` bits, and the upper one
is one more unless the shifted significand is a square.
-/
theorem sqrtDyadicBracket_eq (fmt : FloatFormat) (negative : Bool) (m scale : Nat) (hm : m ≠ 0)
    (hmlt : m < 2 ^ (fmt.fracWidth + 1)) (hbias : fmt.fracWidth + 1 ≤ fmt.exponentBias)
    (num N : Nat) (hnum : num = m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth))
    (hN : N = m <<< (num % 2 + (2 * fmt.fracWidth + 1) - (m.log2 + 1))) :
    Model.sqrtDyadicBracket fmt ⟨negative, m, (scale : Int) + fmt.minSubnormalExponent⟩ =
      ⟨⟨false, Nat.sqrt N, ((num / 2 - 1 : Nat) : Int) - (0 : Nat) + fmt.minSubnormalExponent⟩,
        ⟨false, if N - Nat.sqrt N * Nat.sqrt N = 0 then Nat.sqrt N else Nat.sqrt N + 1,
          ((num / 2 - 1 : Nat) : Int) - (0 : Nat) + fmt.minSubnormalExponent⟩⟩ := by
  have hleading : m.log2 ≤ fmt.fracWidth := by
    have := (Nat.log2_lt hm).2 hmlt
    omega
  have hf := fmt.fracWidth_pos
  have hdouble : (m * 2).log2 = m.log2 + 1 := by
    rw [Nat.mul_comm]
    exact Nat.log2_two_mul hm
  subst hnum hN
  unfold Model.sqrtDyadicBracket
  dsimp only
  by_cases hodd : ((scale : Int) + fmt.minSubnormalExponent) % 2 = 0
  · have hne : (((scale : Int) + fmt.minSubnormalExponent) % 2 != 0) = false := by
      simp [hodd]
    simp only [hne, Bool.false_eq_true, ite_false]
    have hshift : 2 * (fmt.fracWidth - m.log2 / 2) =
        (m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) % 2 +
          (2 * fmt.fracWidth + 1) - (m.log2 + 1) := by
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast] at hodd
      omega
    have hexp : ((scale : Int) + fmt.minSubnormalExponent) / 2 -
          Int.ofNat (fmt.fracWidth - m.log2 / 2) =
        (((m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) / 2 - 1 : Nat) : Int) -
          (0 : Nat) + fmt.minSubnormalExponent := by
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast] at hodd ⊢
      omega
    simp only [Nat.shiftLeft_eq', hshift, hexp, beq_iff_eq]
  · have hne : (((scale : Int) + fmt.minSubnormalExponent) % 2 != 0) = true := by
      simp [hodd]
    simp only [hne, ite_true]
    have hshift : 2 * (fmt.fracWidth - (m.log2 + 1) / 2) + 1 =
        (m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) % 2 +
          (2 * fmt.fracWidth + 1) - (m.log2 + 1) := by
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast] at hodd
      omega
    have hexp : ((scale : Int) + fmt.minSubnormalExponent - 1) / 2 -
          Int.ofNat (fmt.fracWidth - (m.log2 + 1) / 2) =
        (((m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) / 2 - 1 : Nat) : Int) -
          (0 : Nat) + fmt.minSubnormalExponent := by
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast] at hodd ⊢
      omega
    have hscaled : ∀ k : Nat, (m * 2) <<< k = m <<< (k + 1) := by
      intro k
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
    simp only [hdouble, Nat.shiftLeft_eq', hscaled, hshift, hexp, beq_iff_eq]

/--
The encoding of the reference root `positiveRoot` of `m * 2 ^ (scale + minSubnormalExponent)` in
the direction `mode`, under the premises of `sqrtPositiveDyadic_bits`: the exponent field before
a rounding carry is `num / 2`, and the significand is the directed integer root of `m` shifted
to `2 * fracWidth + 1 + num % 2` bits.
-/
theorem positiveRoot_bits (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (m scale : Nat) (hm : m ≠ 0) (hmlt : m < 2 ^ (fmt.fracWidth + 1))
    (hbias : fmt.fracWidth + 1 ≤ fmt.exponentBias)
    (hq : (m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) / 2 + 1 ≤
      fmt.maxFiniteExpField) :
    (positiveRoot fmt mode ⟨negative, m, (scale : Int) + fmt.minSubnormalExponent⟩).toNatBits =
      ((m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) / 2 - 1) * 2 ^ fmt.fracWidth +
        directedRoot mode (m <<< ((m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth)) % 2 +
          (2 * fmt.fracWidth + 1) - (m.log2 + 1))) := by
  have hnearest := sqrtPositiveDyadic_bits fmt m scale hm hmlt hbias hq
  have hbracket := sqrtDyadicBracket_eq fmt negative m scale hm hmlt hbias _ _ rfl rfl
  have hf := fmt.fracWidth_pos
  have hleading : m.log2 ≤ fmt.fracWidth := by
    have := (Nat.log2_lt hm).2 hmlt
    omega
  generalize hnum : m.log2 + 1 + scale + (fmt.exponentBias - fmt.fracWidth) = num
    at hq hnearest hbracket ⊢
  generalize hshift : num % 2 + (2 * fmt.fracWidth + 1) - (m.log2 + 1) = shift
    at hnearest hbracket ⊢
  obtain ⟨-, -, hrootLow, hrootHigh⟩ :=
    Model.sqrt_shiftLeft_bounds fmt.fracWidth m shift hm (by omega) (by omega)
  have hfield : num / 2 - 1 + 2 ≤ fmt.maxFiniteExpField := by omega
  have hlower := roundDyadic_exact fmt .down (num / 2 - 1) (Nat.sqrt (m <<< shift)) hrootLow
    (by omega) hfield
  have hupper := roundDyadic_exact fmt .up (num / 2 - 1)
    (if m <<< shift - Nat.sqrt (m <<< shift) * Nat.sqrt (m <<< shift) = 0 then
      Nat.sqrt (m <<< shift) else Nat.sqrt (m <<< shift) + 1)
    (by split <;> omega) (by split <;> omega) hfield
  cases mode
  case nearest => rw [directedRoot_nearest]; exact hnearest
  case nearestAway => rw [directedRoot_nearestAway]; exact hnearest
  case towardZero =>
    change (Model.roundDyadicDown fmt (Model.sqrtDyadicBracket fmt _).lower).toNatBits = _
    rw [hbracket]
    exact hlower
  case down =>
    change (Model.roundDyadicDown fmt (Model.sqrtDyadicBracket fmt _).lower).toNatBits = _
    rw [hbracket]
    exact hlower
  case up =>
    change (Model.roundDyadicUp fmt (Model.sqrtDyadicBracket fmt _).upper).toNatBits = _
    rw [hbracket, directedRoot_up]
    exact hupper
  case away =>
    change (Model.roundDyadicUp fmt (Model.sqrtDyadicBracket fmt _).upper).toNatBits = _
    rw [hbracket]
    exact hupper.trans (by rw [← directedRoot_up]; rfl)

/-! ## Correctness -/

/-- `sqrtSpecial` computes the encoding of the reference square root, for every operand. -/
theorem sqrtSpecial_eq {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model fmt) :
    sqrtSpecial fmt mode x.toNatBits = (Model.sqrt x (mode := mode)).toNatBits := by
  unfold sqrtSpecial
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, infFlag_eq,
    nanFlag_eq, zeroFlag_eq]
  rw [sqrt_cases mode x]
  refine (chooseNaN1_getD_bits x _ _ ?_).symm
  intro _
  have href : sqrtReference fmt mode x.toNatBits = (Model.sqrt x (mode := mode)).toNatBits := by
    rw [sqrtReference, Model.ofNatBits_toNatBits, referenceRoot_eq]
  rw [href]
  simp only [invalidWord_eq, overflowWord_eq]
  cases Model.isInfinite x <;> cases Model.isZero x <;> cases Model.signBit x <;> rfl

/--
`sqrt` computes the encoding of the reference square root `Model.sqrt x (mode := mode)`, for
every format descriptor, every rounding direction and every operand.
-/
theorem sqrt_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x : Model fmt) :
    sqrt fmt mode x.toNatBits = (Model.sqrt x (mode := mode)).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  have hspecial := sqrtSpecial_eq mode x
  unfold sqrt
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.succ_eq_add_one, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_sub_shiftLeft]
  rw [sqrtCore_eq, hspecial]
  intro hguard
  rw [hspecial]
  obtain ⟨hrest, hfield⟩ := Nat.eq_zero_of_add_eq_zero hguard
  obtain ⟨hclass, hvalue⟩ := Nat.eq_zero_of_add_eq_zero hrest
  obtain ⟨hnonFinite, hsignBit⟩ := Nat.eq_zero_of_add_eq_zero hclass
  obtain ⟨hnonzero, hslow⟩ := Nat.eq_zero_of_add_eq_zero hvalue
  obtain ⟨d, hd, hnegative, hsignificand, hexponent⟩ :=
    toDyadic?_of_isFinite x (isFinite_of_nonFinite_eq_zero x hnonFinite)
  have hmlt := decoded_significand_lt x
  rw [← hsignificand] at hmlt hnonzero hfield ⊢
  have hm : d.significand ≠ 0 := by omega
  have hsign : Model.signBit x = false := by
    cases hs : Model.signBit x
    · rfl
    · simp [hs] at hsignBit
  have hbias : fmt.fracWidth + 1 ≤ fmt.exponentBias := by
    unfold sqrtSlow at hslow
    have : fmt.fracWidth + 1 - fmt.exponentBias = 0 := hslow
    omega
  have hlen := significandLength_eq hmlt
  rw [ite_eq_right hm] at hlen
  rw [hlen] at hfield ⊢
  have hzero : Model.isZero x = false := by
    rw [Model.isZero_eq_beq_zero_of_toDyadic?_some hd]
    simpa using hm
  have hdyadic : d = ⟨d.negative, d.significand,
      ((Model.expField x - 1 : Nat) : Int) + fmt.minSubnormalExponent⟩ := by
    rw [← hexponent hm]
  rw [sqrt_of_positive mode x d hd hzero hsign, hdyadic]
  have hq : (d.significand.log2 + 1 + (Model.expField x - 1) +
      (fmt.exponentBias - fmt.fracWidth)) / 2 + 1 ≤ fmt.maxFiniteExpField := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one] at hfield
    omega
  rw [positiveRoot_bits fmt mode d.negative d.significand (Model.expField x - 1) hm hmlt hbias
    hq, Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.and_one_is_mod]

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
