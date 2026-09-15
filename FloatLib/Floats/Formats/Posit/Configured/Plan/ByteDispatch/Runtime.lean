/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Scoring
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Byte.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Backend.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.ByteTable.Construction
public import FloatLib.Floats.Formats.Posit.Configured.Plan.Core.Estimates
public import FloatLib.Floats.Formats.Posit.Configured.Core

/-!
# First-order runtime dispatch for byte-sized posits

Byte-sized posits have exhaustive tables, direct packed-word arithmetic, width-generic dyadic
arithmetic, and the reference specification. The general planner stores functions in candidate
records, but projecting the winner through that representation leaves an indirect closure call in
otherwise monomorphic `UInt8` arithmetic.

This module runs the same deterministic comparison over a compact tag and matches the result to a
named first-order kernel. Closed public formats hoist the tag and lazy-table resource as static
values, preserving shared memoization without closure dispatch. Correctness and planner-agreement
proofs live in `ByteDispatch.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan.ByteDispatch

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/-- The four certified implementation classes available to every byte-sized posit operation. -/
inductive Choice where
  | reference
  | table
  | word
  | dyadic
  deriving DecidableEq, Repr

/-- Planner metadata represented by one byte-kernel tag. -/
@[inline] def Choice.estimate
    (format : Format) (width_le : format.bits ≤ 8)
    (operation : Operation) : Choice → Candidate
  | .reference => genericEstimate (.byte width_le) operation
  | .table => tableEstimate format width_le operation
  | .word => storedNativeWordEstimate (.byte width_le) operation
  | .dyadic => dyadicEstimate (.byte width_le) operation

/-- Compare two byte-kernel tags using the shared planner ordering. -/
@[inline] def Choice.consider
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8)
    (operation : Operation) (incumbent candidate : Choice) : Choice :=
  if (candidate.estimate format width_le operation).admissible policy &&
      (candidate.estimate format width_le operation).better policy
        (incumbent.estimate format width_le operation) then
    candidate
  else
    incumbent

/--
Select a byte kernel without constructing a list or retaining executable closures.

The order is table, packed word, then width-generic dyadic arithmetic, seeded by the reference
baseline. This is the same ordering used by the certified candidate portfolios.
-/
@[noinline] def select
    (policy : Policy) (format : Format) (width_le : format.bits ≤ 8)
    (operation : Operation) : Choice :=
  let afterTable :=
    Choice.consider policy format width_le operation .reference .table
  let afterWord :=
    Choice.consider policy format width_le operation afterTable .word
  Choice.consider policy format width_le operation afterWord .dyadic

/-- Metadata-only candidates corresponding exactly to the tag selector. -/
def estimates
    (format : Format) (width_le : format.bits ≤ 8)
    (operation : Operation) : CandidateSet Candidate where
  alternatives :=
    [tableEstimate format width_le operation,
      storedNativeWordEstimate (.byte width_le) operation,
      dyadicEstimate (.byte width_le) operation]
  baseline := genericEstimate (.byte width_le) operation

variable {format : Format}

/-- Configured posit execution using the proved byte-sized storage plan. -/
abbrev ByteFloat (format : Format) (width_le : format.bits ≤ 8) :=
  FloatLib.Floats.ExecFloat
    (Family format (Code (.byte width_le)) (.byte width_le))

/-! ## Direct operation entry points -/

/-- Execute byte-sized posit addition from a first-order choice tag. -/
@[noinline] def addSelected
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedBinary
      (ByteTable.encoding format width_le) Model.Spec.add)
    (left right : ByteFloat format width_le) : ByteFloat format width_le :=
  match selection with
  | .reference => Spec.add left right
  | .table => ByteTable.runBinary width_le table left right
  | .word => Backend.Byte.add width_le left right
  | .dyadic => Backend.dyadicAdd left right

/-- Execute policy-selected byte-sized posit addition through a first-order kernel. -/
@[always_inline] def add
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right : ByteFloat format width_le) : ByteFloat format width_le :=
  addSelected (select policy format width_le .add)
    width_le (ByteTable.addTable width_le) left right

/-- Execute byte-sized posit subtraction from a first-order choice tag. -/
@[noinline] def subSelected
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedBinary
      (ByteTable.encoding format width_le) Model.Spec.sub)
    (left right : ByteFloat format width_le) : ByteFloat format width_le :=
  match selection with
  | .reference => Spec.sub left right
  | .table => ByteTable.runBinary width_le table left right
  | .word => Backend.Byte.sub width_le left right
  | .dyadic => Backend.dyadicSub left right

/-- Execute policy-selected byte-sized posit subtraction through a first-order kernel. -/
@[always_inline] def sub
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right : ByteFloat format width_le) : ByteFloat format width_le :=
  subSelected (select policy format width_le .sub)
    width_le (ByteTable.subTable width_le) left right

/-- Execute byte-sized posit multiplication from a first-order choice tag. -/
@[noinline] def mulSelected
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedBinary
      (ByteTable.encoding format width_le) Model.Spec.mul)
    (left right : ByteFloat format width_le) : ByteFloat format width_le :=
  match selection with
  | .reference => Spec.mul left right
  | .table => ByteTable.runBinary width_le table left right
  | .word => Backend.Byte.mul width_le left right
  | .dyadic => Backend.dyadicMul left right

/-- Execute policy-selected byte-sized posit multiplication through a first-order kernel. -/
@[always_inline] def mul
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right : ByteFloat format width_le) : ByteFloat format width_le :=
  mulSelected (select policy format width_le .mul)
    width_le (ByteTable.mulTable width_le) left right

/-- Execute byte-sized posit division from a first-order choice tag. -/
@[noinline] def divSelected
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedBinary
      (ByteTable.encoding format width_le) Model.Spec.div)
    (left right : ByteFloat format width_le) : ByteFloat format width_le :=
  match selection with
  | .reference => Spec.div left right
  | .table => ByteTable.runBinary width_le table left right
  | .word => Backend.Byte.div width_le left right
  | .dyadic => Backend.dyadicDiv left right

/-- Execute policy-selected byte-sized posit division through a first-order kernel. -/
@[always_inline] def div
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right : ByteFloat format width_le) : ByteFloat format width_le :=
  divSelected (select policy format width_le .div)
    width_le (ByteTable.divTable width_le) left right

/-- Execute byte-sized posit square root from a first-order choice tag. -/
@[noinline] def sqrtSelected
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedUnary
      (ByteTable.encoding format width_le) Model.Spec.sqrt)
    (value : ByteFloat format width_le) : ByteFloat format width_le :=
  match selection with
  | .reference => Spec.sqrt value
  | .table => ByteTable.runUnary width_le table value
  | .word => Backend.Byte.sqrt width_le value
  | .dyadic => Backend.dyadicSqrt value

/-- Execute policy-selected byte-sized posit square root through a first-order kernel. -/
@[always_inline] def sqrt
    (policy : Policy) (width_le : format.bits ≤ 8)
    (value : ByteFloat format width_le) : ByteFloat format width_le :=
  sqrtSelected (select policy format width_le .sqrt)
    width_le (ByteTable.sqrtTable width_le) value

/-- Execute byte-sized posit FMA from a first-order choice tag. -/
@[noinline] def fmaSelected
    (selection : Choice) (width_le : format.bits ≤ 8)
    (table : TinyTable.CertifiedTernary
      (ByteTable.encoding format width_le) Model.Spec.fma)
    (left right addend : ByteFloat format width_le) : ByteFloat format width_le :=
  match selection with
  | .reference => Spec.fma left right addend
  | .table => ByteTable.runTernary width_le table left right addend
  | .word => Backend.Byte.fma width_le left right addend
  | .dyadic => Backend.dyadicFma left right addend

/-- Execute policy-selected byte-sized posit FMA through a first-order kernel. -/
@[always_inline] def fma
    (policy : Policy) (width_le : format.bits ≤ 8)
    (left right addend : ByteFloat format width_le) : ByteFloat format width_le :=
  fmaSelected (select policy format width_le .fma)
    width_le (ByteTable.fmaTable width_le) left right addend

end FloatLib.Floats.Formats.Posit.Configured.Plan.ByteDispatch
