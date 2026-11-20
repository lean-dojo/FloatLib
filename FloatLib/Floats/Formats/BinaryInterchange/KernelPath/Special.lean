/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Decode

/-!
# Infinities and NaNs on encodings

The kernel operations classify a word that is not finite with natural-number arithmetic: `infFlag`
and `nanFlag` are one for an infinity and for a NaN, `signalingFlag` is one for a NaN whose quiet
bit is clear, and quieting a NaN is one `Nat.lor` with `quietMask`. The constants `infMagnitude`
and `quietMask` depend on the encoding policy, so one definition serves the IEEE encoding and the
three finite-only ones, which have no infinity and no signaling NaN.

`nanChoice` is the NaN that a two-operand operation returns, the rule of `Model.chooseNaN2`: the
first signaling NaN, else the first NaN, quieted (`chooseNaN2_bits`). `nanChoice3` is the same
rule for three operands (`chooseNaN3_bits`), and `zeroFlag` is one for a zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The exponent and fraction fields of an infinity. An encoding without infinities gets a value
that no word reaches.
-/
def infMagnitude (fmt : FloatFormat) : Nat :=
  match fmt.encoding with
  | .ieee => fmt.expAllOnesNat * 2 ^ fmt.fracWidth
  | .finiteMaxNaN | .finiteUnsignedZero | .finite => 2 ^ signPos fmt

kernel_constant infMagnitude

/-- The quiet bit of a NaN, and zero in an encoding without signaling NaNs. -/
def quietMask (fmt : FloatFormat) : Nat :=
  match fmt.encoding with
  | .ieee => fmt.quietBitNat
  | .finiteMaxNaN | .finiteUnsignedZero | .finite => 0

kernel_constant quietMask

/--
The encoding of the result of an invalid operation, `Model.invalidResult` (`invalidWord_eq`), by
the encoding: the quiet NaN with an empty payload, the largest pattern, the word of the sign
bit, and zero for a format without a NaN. It is written on the two widths, so that Lean's
kernel computes it without unpacking a word of the model.
-/
def invalidWord (fmt : FloatFormat) : Nat :=
  FloatFormat.Encoding.casesOn (motive := fun _ => Nat) fmt.encoding
    ((2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth % 2 ^ fmt.bitWidth |||
      2 ^ (fmt.fracWidth - 1) % 2 ^ fmt.bitWidth)
    ((2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth + (2 ^ fmt.fracWidth - 1))
    (2 ^ signPos fmt)
    0

/-- `invalidWord` is the encoding of the invalid-operation result of the model, for every
format. -/
theorem invalidWord_eq (fmt : FloatFormat) :
    invalidWord fmt = (Model.invalidResult fmt).toNatBits := by
  have hE : fmt.expAllOnesNat < 2 ^ fmt.expWidth :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have hF : fmt.fracMaskNat < 2 ^ fmt.fracWidth :=
    Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  unfold invalidWord Model.invalidResult
  cases h : fmt.encoding
  · simp only [Model.canonicalNaN, Model.ofBits, Model.toNatBits, FloatFormat.expMask,
      FloatFormat.quietBit, FloatFormat.ofWordNat, BitVec.toNat_or, BitVec.toNat_ofNat,
      FloatFormat.expMaskNat, FloatFormat.expAllOnesNat, FloatFormat.quietBitNat]
  · rw [toNatBits_ofFields fmt false _ _ hE hF]
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
    rfl
  · simp [signPos, FloatFormat.signMaskNat_eq_two_pow]
  · simp

kernel_constant invalidWord

/-- One when the exponent and fraction fields `magnitude` are those of an infinity. -/
def infFlag (fmt : FloatFormat) (magnitude : Nat) : Nat :=
  Nat.sub 1
    (Nat.add (Nat.sub magnitude (infMagnitude fmt)) (Nat.sub (infMagnitude fmt) magnitude))

kernel_constant infFlag

/-- One when a word is a NaN: it is not finite and not an infinity. -/
def nanFlag (fmt : FloatFormat) (sign magnitude : Nat) : Nat :=
  Nat.mul (Nat.sub 1 (Nat.sub 1 (nonFinite fmt sign magnitude)))
    (Nat.sub 1 (infFlag fmt magnitude))

kernel_constant nanFlag

/-- For a NaN word `a`: one when it is signaling, that is, the encoding has a quiet bit and it
is clear in `a`. -/
def signalingFlag (fmt : FloatFormat) (a : Nat) : Nat :=
  Nat.sub (Nat.sub 1 (Nat.sub 1 (quietMask fmt)))
    (Nat.sub 1 (Nat.sub 1 (Nat.land a (quietMask fmt))))

kernel_constant signalingFlag

/--
The NaN that an operation on the words `a` and `b` returns when one of them is a NaN: `a` if it
is signaling, else `b` if it is signaling, else `a` if it is a NaN, else `b`, with the quiet bit
set. The flags say which operands are signaling NaNs and whether `a` is a NaN.
-/
def nanChoice (fmt : FloatFormat) (a b signalingA signalingB nanA : Nat) : Nat :=
  Nat.lor
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq signalingA 0) a
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq signalingB 0) b
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq nanA 0) a b)))
    (quietMask fmt)

kernel_constant nanChoice

/--
The NaN that an operation on the words `a`, `b` and `c` returns when one of them is a NaN: the
first signaling NaN, else the first NaN, with the quiet bit set.
-/
def nanChoice3 (fmt : FloatFormat) (a b c signalingA signalingB signalingC nanA nanB : Nat) :
    Nat :=
  Nat.lor
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq signalingA 0) a
      (Bool.casesOn (motive := fun _ => Nat) (Nat.beq signalingB 0) b
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq signalingC 0) c
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq nanA 0) a
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq nanB 0) b c)))))
    (quietMask fmt)

kernel_constant nanChoice3

/-- One when a word with sign `sign` and fields `magnitude` is a zero. -/
def zeroFlag (fmt : FloatFormat) (sign magnitude : Nat) : Nat :=
  Nat.mul (Nat.sub 1 magnitude) (Nat.sub 1 (Nat.mul (negZeroNaN fmt) sign))

kernel_constant zeroFlag

/-! ## Classification of a word by its fields -/

/-- The `nonFinite` flag of a finite word is zero. -/
theorem nonFinite_eq_zero_of_isFinite {fmt : FloatFormat} (x : Model fmt)
    (hfinite : Model.isFinite x = true) :
    nonFinite fmt (if Model.signBit x then 1 else 0)
      (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) = 0 := by
  have he := Model.expField_lt_pow2 x
  have hf := Model.fracField_lt_pow2 x
  have hiff := le_maxFinite_iff fmt (Model.expField x) (Model.fracField x) hf
  have hmul := Nat.le_mul_of_pos_right (Model.expField x) (Nat.two_pow_pos fmt.fracWidth)
  rw [← Model.ofFields_signBit_expField_fracField x,
    Model.isFinite_ofFields fmt _ _ _ he hf] at hfinite
  cases hencoding : fmt.encoding <;> cases hsign : Model.signBit x
  all_goals
    simp only [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent,
      FloatFormat.maxFiniteFracField, FloatFormat.fracMaskNat, hencoding] at hiff
    simp only [hencoding, hsign, bne_iff_ne, ne_eq, FloatFormat.expAllOnesNat,
      FloatFormat.fracMaskNat, Bool.not_eq_true', Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, Bool.true_eq_false] at hfinite
    have hle : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x ≤
        maxFinite fmt := hiff.2 (by omega)
    simp only [nonFinite, negZeroNaN, hencoding, Nat.add_eq, Nat.sub_eq,
      Nat.mul_eq, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.one_mul]
    first
    | omega
    | have hpos : 0 < Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x := by
        rcases hfinite with (hfalse | he0) | hf0
        · exact hfalse.elim
        · exact Nat.add_pos_left (Nat.mul_pos (Nat.pos_of_ne_zero he0)
            (Nat.two_pow_pos _)) _
        · exact Nat.add_pos_right _ (Nat.pos_of_ne_zero hf0)
      omega

/-- The arithmetic classification flag vanishes exactly on finite stored values. -/
theorem nonFinite_eq_zero_iff {fmt : FloatFormat} (x : Model fmt) :
    nonFinite fmt (if Model.signBit x then 1 else 0)
      (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) = 0 ↔
        Model.isFinite x = true :=
  ⟨isFinite_of_nonFinite_eq_zero x, nonFinite_eq_zero_of_isFinite x⟩

/-- A NaN is a word that is neither finite nor an infinity, in every encoding. -/
theorem isNaN_eq_not_isFinite_and_not_isInfinite {fmt : FloatFormat} (x : Model fmt) :
    Model.isNaN x = (!Model.isFinite x && !Model.isInfinite x) := by
  cases hencoding : fmt.encoding <;>
    simp only [Model.isNaN, Model.isFinite, Model.isInfinite, hencoding, Model.IEEE.isNaN,
      Model.IEEE.isFinite, Model.IEEE.isInfinite]
  · simp only [bne]
    cases Model.expField x == fmt.expAllOnesNat <;> cases Model.fracField x == 0 <;> rfl
  · simp
  · simp
  · rfl

/-- `infFlag` is one exactly on the infinities. -/
theorem infFlag_eq {fmt : FloatFormat} (x : Model fmt) :
    infFlag fmt (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) =
      if Model.isInfinite x then 1 else 0 := by
  have hf := Model.fracField_lt_pow2 x
  have hlt := fields_lt_two_pow_signPos x
  unfold infFlag infMagnitude
  simp only [Nat.add_eq, Nat.sub_eq]
  cases hencoding : fmt.encoding <;> simp only [Model.isInfinite, hencoding]
  · simp only [Model.IEEE.isInfinite, Bool.and_eq_true, beq_iff_eq]
    by_cases hinf : Model.expField x = fmt.expAllOnesNat ∧ Model.fracField x = 0
    · rw [ite_eq_left hinf, hinf.1, hinf.2]
      omega
    · rw [ite_eq_right hinf]
      have hne : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x ≠
          fmt.expAllOnesNat * 2 ^ fmt.fracWidth := by
        intro heq
        have hexp : (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) >>>
            fmt.fracWidth = (fmt.expAllOnesNat * 2 ^ fmt.fracWidth) >>> fmt.fracWidth := by
          rw [heq]
        rw [fields_shiftRight _ _ _ hf] at hexp
        have hzero := fields_shiftRight fmt.expAllOnesNat 0 fmt.fracWidth (Nat.two_pow_pos _)
        rw [Nat.add_zero] at hzero
        rw [hzero] at hexp
        rw [hexp] at heq
        exact hinf ⟨hexp, by omega⟩
      omega
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

/-- `nanFlag` is one exactly on the NaNs. -/
theorem nanFlag_eq {fmt : FloatFormat} (x : Model fmt) :
    nanFlag fmt (if Model.signBit x then 1 else 0)
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) =
      if Model.isNaN x then 1 else 0 := by
  unfold nanFlag
  rw [infFlag_eq, isNaN_eq_not_isFinite_and_not_isInfinite]
  simp only [Nat.mul_eq, Nat.sub_eq]
  cases hfinite : Model.isFinite x
  · have hflag : nonFinite fmt (if Model.signBit x then 1 else 0)
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) ≠ 0 := by
      intro h
      rw [isFinite_of_nonFinite_eq_zero x h] at hfinite
      exact Bool.noConfusion hfinite
    have hone : 1 - (1 - nonFinite fmt (if Model.signBit x then 1 else 0)
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x)) = 1 := by omega
    rw [hone]
    cases Model.isInfinite x <;> simp
  · rw [nonFinite_eq_zero_of_isFinite x hfinite]
    simp

/-- The quiet bit of a format lies inside its word. -/
theorem quietBit_toNat (fmt : FloatFormat) :
    (FloatFormat.quietBit fmt).toNat = fmt.quietBitNat := by
  unfold FloatFormat.quietBit FloatFormat.ofWordNat FloatFormat.quietBitNat
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  apply Nat.pow_lt_pow_right (by decide)
  unfold FloatFormat.bitWidth
  omega

/-- `signalingFlag` is one exactly on the signaling NaNs, among the NaNs. -/
theorem signalingFlag_eq {fmt : FloatFormat} (x : Model fmt) (hnan : Model.isNaN x = true) :
    signalingFlag fmt x.toNatBits = if Model.isSignaling x then 1 else 0 := by
  unfold signalingFlag quietMask
  simp only [Nat.sub_eq, Nat.land_eq]
  cases hencoding : fmt.encoding <;> simp only [Model.isSignaling, hencoding]
  · have hieee : Model.IEEE.isNaN x = true := by simpa [Model.isNaN, hencoding] using hnan
    have hpos : fmt.quietBitNat ≠ 0 := by
      unfold FloatFormat.quietBitNat
      exact (Nat.two_pow_pos _).ne'
    have hbits : (x.bits &&& FloatFormat.quietBit fmt == 0) =
        decide (x.toNatBits &&& fmt.quietBitNat = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, decide_eq_true_eq]
      rw [← BitVec.toNat_inj, BitVec.toNat_and, quietBit_toNat]
      rfl
    simp only [Model.IEEE.isSignaling, hieee, Bool.true_and, hbits, decide_eq_true_eq]
    by_cases hclear : x.toNatBits &&& fmt.quietBitNat = 0
    · rw [ite_eq_left hclear, hclear]
      omega
    · rw [ite_eq_right hclear]
      omega
  · simp
  · simp
  · simp

/-- Quieting a NaN sets the quiet bit of its word. -/
theorem quietNaN_bits {fmt : FloatFormat} (x : Model fmt) (hnan : Model.isNaN x = true) :
    (Model.quietNaN x).toNatBits = x.toNatBits ||| quietMask fmt := by
  unfold quietMask
  cases hencoding : fmt.encoding <;> simp only [Model.quietNaN, hencoding]
  · have hieee : Model.IEEE.isNaN x = true := by simpa [Model.isNaN, hencoding] using hnan
    rw [ite_eq_left hieee]
    change (x.bits ||| FloatFormat.quietBit fmt).toNat = _
    rw [BitVec.toNat_or, quietBit_toNat]
    rfl
  · simp
  · simp
  · simp

/-- The encoding of the NaN that `Model.chooseNaN2` selects, and `none` without a NaN operand. -/
theorem chooseNaN2_bits {fmt : FloatFormat} (x y : Model fmt) :
    (Model.chooseNaN2 x y).map Model.toNatBits =
      if Model.isNaN x = true ∨ Model.isNaN y = true then
        some (nanChoice fmt x.toNatBits y.toNatBits
          (if Model.isSignaling x then 1 else 0) (if Model.isSignaling y then 1 else 0)
          (if Model.isNaN x then 1 else 0))
      else none := by
  have hone : Nat.beq 1 0 = false := rfl
  unfold Model.chooseNaN2 nanChoice
  cases hnx : Model.isNaN x <;> cases hny : Model.isNaN y
  · simp [Model.isSignaling_eq_false_of_isNaN_eq_false x hnx,
      Model.isSignaling_eq_false_of_isNaN_eq_false y hny]
  · have hsx := Model.isSignaling_eq_false_of_isNaN_eq_false x hnx
    cases hsy : Model.isSignaling y <;> simp [hsx, quietNaN_bits y hny, hone]
  · have hsy := Model.isSignaling_eq_false_of_isNaN_eq_false y hny
    cases hsx : Model.isSignaling x <;> simp [hsy, quietNaN_bits x hnx, hone]
  · cases hsx : Model.isSignaling x <;> cases hsy : Model.isSignaling y <;>
      simp [quietNaN_bits x hnx, quietNaN_bits y hny, hone]

/-- `zeroFlag` is one exactly on the zeros. -/
theorem zeroFlag_eq {fmt : FloatFormat} (x : Model fmt) :
    zeroFlag fmt (if Model.signBit x then 1 else 0)
        (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) =
      if Model.isZero x then 1 else 0 := by
  have he := Model.expField_lt_pow2 x
  have hf := Model.fracField_lt_pow2 x
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hzero : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x = 0 ↔
      Model.expField x = 0 ∧ Model.fracField x = 0 := by
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := Nat.eq_zero_of_add_eq_zero h
      exact ⟨(Nat.mul_eq_zero.mp h1).resolve_right hpos.ne', h2⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2, Nat.zero_mul]
  have hfields : Model.isZero x =
      match fmt.encoding with
      | .finiteUnsignedZero =>
          !Model.signBit x && Model.expField x == 0 && Model.fracField x == 0
      | .ieee | .finiteMaxNaN | .finite => Model.expField x == 0 && Model.fracField x == 0 := by
    have h := Model.isZero_ofFields fmt (Model.signBit x) _ _ he hf
    rwa [Model.ofFields_signBit_expField_fracField x] at h
  rw [hfields]
  unfold zeroFlag
  simp only [Nat.mul_eq, Nat.sub_eq]
  generalize Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x = u at hzero
  cases hencoding : fmt.encoding <;>
    simp only [negZeroNaN, hencoding, Nat.zero_mul, Nat.one_mul, Nat.sub_zero, Nat.mul_one,
      Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  · by_cases hu : u = 0
    · rw [ite_eq_left (hzero.mp hu), hu]
    · rw [ite_eq_right (fun h => hu (hzero.mpr h))]
      omega
  · by_cases hu : u = 0
    · rw [ite_eq_left (hzero.mp hu), hu]
    · rw [ite_eq_right (fun h => hu (hzero.mpr h))]
      omega
  · cases hsign : Model.signBit x
    · by_cases hu : u = 0
      · have := hzero.mp hu
        simp [hu, this]
      · have hne : ¬(Model.expField x = 0 ∧ Model.fracField x = 0) := fun h => hu (hzero.mpr h)
        have hflag : 1 - u = 0 := by omega
        simp only [hflag, Nat.zero_mul]
        split
        · rename_i h
          exact absurd ⟨h.1.2, h.2⟩ hne
        · rfl
    · simp
  · by_cases hu : u = 0
    · rw [ite_eq_left (hzero.mp hu), hu]
    · rw [ite_eq_right (fun h => hu (hzero.mpr h))]
      omega

/-- The encoding of the NaN that `Model.chooseNaN1` selects, and `none` for another operand. -/
theorem chooseNaN1_bits {fmt : FloatFormat} (x : Model fmt) :
    (Model.chooseNaN1 x).map Model.toNatBits =
      if Model.isNaN x = true then some (x.toNatBits ||| quietMask fmt) else none := by
  unfold Model.chooseNaN1
  cases hnx : Model.isNaN x
  · simp
  · simp [quietNaN_bits x hnx]

/-- The encoding of the NaN that `Model.chooseNaN3` selects, and `none` without a NaN operand. -/
theorem chooseNaN3_bits {fmt : FloatFormat} (x y z : Model fmt) :
    (Model.chooseNaN3 x y z).map Model.toNatBits =
      if Model.isNaN x = true ∨ Model.isNaN y = true ∨ Model.isNaN z = true then
        some (nanChoice3 fmt x.toNatBits y.toNatBits z.toNatBits
          (if Model.isSignaling x then 1 else 0) (if Model.isSignaling y then 1 else 0)
          (if Model.isSignaling z then 1 else 0) (if Model.isNaN x then 1 else 0)
          (if Model.isNaN y then 1 else 0))
      else none := by
  have hone : Nat.beq 1 0 = false := rfl
  have hsx : Model.isNaN x = false → Model.isSignaling x = false :=
    Model.isSignaling_eq_false_of_isNaN_eq_false x
  have hsy : Model.isNaN y = false → Model.isSignaling y = false :=
    Model.isSignaling_eq_false_of_isNaN_eq_false y
  have hsz : Model.isNaN z = false → Model.isSignaling z = false :=
    Model.isSignaling_eq_false_of_isNaN_eq_false z
  have hqx := quietNaN_bits x
  have hqy := quietNaN_bits y
  have hqz := quietNaN_bits z
  unfold Model.chooseNaN3 nanChoice3
  cases hnx : Model.isNaN x <;> cases hny : Model.isNaN y <;> cases hnz : Model.isNaN z <;>
    cases hx : Model.isSignaling x <;> cases hy : Model.isSignaling y <;> cases hz :
      Model.isSignaling z <;>
    simp_all

/-- A NaN flag times the signaling flag of the word is the signaling-NaN flag. -/
theorem nanFlag_mul_signalingFlag {fmt : FloatFormat} (x : Model fmt) :
    (if Model.isNaN x then 1 else 0) * signalingFlag fmt x.toNatBits =
      if Model.isSignaling x then 1 else 0 := by
  cases hnan : Model.isNaN x
  · simp [Model.isSignaling_eq_false_of_isNaN_eq_false x hnan]
  · simp [signalingFlag_eq x hnan]

/-- Sign bits as naturals are equal exactly when the bits are. -/
theorem beq_sign (p q : Bool) :
    Nat.beq (if p then 1 else 0) (if q then 1 else 0) = (p == q) := by
  cases p <;> cases q <;> rfl

/-- A value that is not finite has no exact dyadic value. -/
theorem toDyadic?_eq_none_of_isFinite_eq_false {fmt : FloatFormat} (x : Model fmt)
    (h : Model.isFinite x = false) : Model.toDyadic? x = none := by
  have hsome := Model.toDyadic?_isSome_eq_isFinite x
  rw [h] at hsome
  cases hd : Model.toDyadic? x
  · rfl
  · rw [hd] at hsome
    exact Bool.noConfusion hsome

/--
The NaN branch of a one-operand operation on encodings: with a NaN operand the result is the
quieted operand, and otherwise the word of the rest of the operation.
-/
theorem chooseNaN1_getD_bits {fmt : FloatFormat} (x rest : Model fmt) (word : Nat)
    (hrest : Model.isNaN x = false → rest.toNatBits = word) :
    ((Model.chooseNaN1 x).getD rest).toNatBits =
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq (if Model.isNaN x then 1 else 0) 0)
        (Nat.lor x.toNatBits (quietMask fmt)) word := by
  have hchoice := chooseNaN1_bits x
  cases hnx : Model.isNaN x
  · rw [hnx] at hchoice
    simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at hchoice
    rw [hchoice]
    exact hrest hnx
  · rw [hnx] at hchoice
    simp only [↓reduceIte, Option.map_eq_some_iff] at hchoice
    obtain ⟨z, hz, hbits⟩ := hchoice
    rw [hz]
    exact hbits

/--
The NaN branch of a two-operand operation on encodings: with a NaN operand the result is
`nanChoice`, and otherwise the word of the rest of the operation.
-/
theorem chooseNaN2_getD_bits {fmt : FloatFormat} (x y rest : Model fmt) (word : Nat)
    (hrest : Model.isNaN x = false → Model.isNaN y = false → rest.toNatBits = word) :
    ((Model.chooseNaN2 x y).getD rest).toNatBits =
      Bool.casesOn (motive := fun _ => Nat)
        (Nat.beq (Nat.add (if Model.isNaN x then 1 else 0) (if Model.isNaN y then 1 else 0)) 0)
        (nanChoice fmt x.toNatBits y.toNatBits
          (Nat.mul (if Model.isNaN x then 1 else 0) (signalingFlag fmt x.toNatBits))
          (Nat.mul (if Model.isNaN y then 1 else 0) (signalingFlag fmt y.toNatBits))
          (if Model.isNaN x then 1 else 0))
        word := by
  have hchoice := chooseNaN2_bits x y
  simp only [Nat.mul_eq, nanFlag_mul_signalingFlag]
  by_cases hnan : Model.isNaN x = true ∨ Model.isNaN y = true
  · rw [ite_eq_left hnan] at hchoice
    simp only [Option.map_eq_some_iff] at hchoice
    obtain ⟨z, hz, hbits⟩ := hchoice
    have hflags : Nat.beq (Nat.add (if Model.isNaN x then 1 else 0)
        (if Model.isNaN y then 1 else 0)) 0 = false := by
      rcases hnan with h | h <;> rw [h] <;> cases Model.isNaN x <;> cases Model.isNaN y <;> rfl
    rw [hz, hflags]
    exact hbits
  · have hnx : Model.isNaN x = false := by
      cases hx : Model.isNaN x
      · rfl
      · exact absurd (Or.inl hx) hnan
    have hny : Model.isNaN y = false := by
      cases hy : Model.isNaN y
      · rfl
      · exact absurd (Or.inr hy) hnan
    rw [ite_eq_right hnan] at hchoice
    simp only [Option.map_eq_none_iff] at hchoice
    rw [hchoice, hnx, hny]
    exact hrest hnx hny

/--
The NaN branch of a three-operand operation on encodings: with a NaN operand the result is
`nanChoice3`, and otherwise the word of the rest of the operation.
-/
theorem chooseNaN3_getD_bits {fmt : FloatFormat} (x y z rest : Model fmt) (word : Nat)
    (hrest : Model.isNaN x = false → Model.isNaN y = false → Model.isNaN z = false →
      rest.toNatBits = word) :
    ((Model.chooseNaN3 x y z).getD rest).toNatBits =
      Bool.casesOn (motive := fun _ => Nat)
        (Nat.beq
          (Nat.add (Nat.add (if Model.isNaN x then 1 else 0) (if Model.isNaN y then 1 else 0))
            (if Model.isNaN z then 1 else 0)) 0)
        (nanChoice3 fmt x.toNatBits y.toNatBits z.toNatBits
          (Nat.mul (if Model.isNaN x then 1 else 0) (signalingFlag fmt x.toNatBits))
          (Nat.mul (if Model.isNaN y then 1 else 0) (signalingFlag fmt y.toNatBits))
          (Nat.mul (if Model.isNaN z then 1 else 0) (signalingFlag fmt z.toNatBits))
          (if Model.isNaN x then 1 else 0) (if Model.isNaN y then 1 else 0))
        word := by
  have hchoice := chooseNaN3_bits x y z
  simp only [Nat.mul_eq, nanFlag_mul_signalingFlag]
  by_cases hnan : Model.isNaN x = true ∨ Model.isNaN y = true ∨ Model.isNaN z = true
  · rw [ite_eq_left hnan] at hchoice
    simp only [Option.map_eq_some_iff] at hchoice
    obtain ⟨w, hw, hbits⟩ := hchoice
    have hflags : Nat.beq (Nat.add (Nat.add (if Model.isNaN x then 1 else 0)
        (if Model.isNaN y then 1 else 0)) (if Model.isNaN z then 1 else 0)) 0 = false := by
      rcases hnan with h | h | h <;> rw [h] <;>
        cases Model.isNaN x <;> cases Model.isNaN y <;> cases Model.isNaN z <;> rfl
    rw [hw, hflags]
    exact hbits
  · have hnx : Model.isNaN x = false := by
      cases hx : Model.isNaN x
      · rfl
      · exact absurd (Or.inl hx) hnan
    have hny : Model.isNaN y = false := by
      cases hy : Model.isNaN y
      · rfl
      · exact absurd (Or.inr (Or.inl hy)) hnan
    have hnz : Model.isNaN z = false := by
      cases hz : Model.isNaN z
      · rfl
      · exact absurd (Or.inr (Or.inr hz)) hnan
    rw [ite_eq_right hnan] at hchoice
    simp only [Option.map_eq_none_iff] at hchoice
    rw [hchoice, hnx, hny, hnz]
    exact hrest hnx hny hnz

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
