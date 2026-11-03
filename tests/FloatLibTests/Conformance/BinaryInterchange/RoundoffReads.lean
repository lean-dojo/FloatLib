/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured

/-!
# Reads that select stored entries

A registered read without a dictionary selects stored entries only with a checked selection
certificate (`Roundoff.Read.selection`): its read of an input container at its own arguments is then
exact, and otherwise the read is analyzed as the function it is. Registration rejects a certificate
that is about another read, holds at one universe only, or takes the entry from anything but the
container's fields and the read's designated observers, and a read through a dictionary that is not
Lean's own. A read rewrite whose premise a local hypothesis discharges tidies a read only in that
hypothesis's scope.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffReads

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- A container of `n` entries stored in an array. -/
structure Box (α : Type) (n : Nat) where
  /-- The stored entries. -/
  entries : Array α
  /-- There are `n` of them. -/
  size_eq : entries.size = n

/-- An index of a box is an index of its stored array. -/
theorem Box.lt_size {α : Type} {n : Nat} (b : Box α n) (i : Fin n) : i.val < b.entries.size := by
  rw [b.size_eq]
  exact i.isLt

/-- The entry `i` of a box. -/
def Box.get {α : Type} {n : Nat} (b : Box α n) (i : Fin n) : α :=
  b.entries[i.val]'(b.lt_size i)

/-- The entry `i` of a box is the entry `i` of its stored array. -/
theorem Box.get_eq {α : Type} {n : Nat} (b : Box α n) (i : Fin n) :
    b.get i = b.entries[i.val]'(b.lt_size i) :=
  rfl

/-- Twice the entry `i` of a box, a computation that is no read. -/
def Box.twice {α : Type} [Add α] {n : Nat} (b : Box α n) (i : Fin n) : α :=
  b.get i + b.get i

/-- `Box.twice` read off the doubled entries, an observation that computes. -/
theorem Box.twice_eq {α : Type} [Add α] {n : Nat} (b : Box α n) (i : Fin n) :
    b.twice i = (b.entries.map fun x => x + x)[i.val]'(by simpa using b.lt_size i) := by
  simp [Box.twice, Box.get]

/-- A view of a box's entries through a dictionary, with a designated observer and a method
that computes. -/
class Peek (α : Type) where
  /-- The stored entries, as an array. -/
  view : Array α → Array α
  /-- The stored entries, each doubled. -/
  doubled : Array α → Array α

/-- The entry `i` of a box through its doubled view. -/
def Box.peek {α : Type} [Peek α] {n : Nat} (b : Box α n) (i : Nat)
    (h : i < (Peek.doubled b.entries).size) : α :=
  (Peek.doubled b.entries)[i]'h

/-- `Box.peek` reads the doubled view. -/
theorem Box.peek_eq {α : Type} [Peek α] {n : Nat} (b : Box α n) (i : Nat)
    (h : i < (Peek.doubled b.entries).size) : b.peek i h = (Peek.doubled b.entries)[i]'h :=
  rfl

/-- The entry `i` of a box through its view. -/
def Box.look {α : Type} [Peek α] {n : Nat} (b : Box α n) (i : Nat)
    (h : i < (Peek.view b.entries).size) : α :=
  (Peek.view b.entries)[i]'h

/-- `Box.look` reads the view, a designated observer. -/
theorem Box.look_eq {α : Type} [Peek α] {n : Nat} (b : Box α n) (i : Nat)
    (h : i < (Peek.view b.entries).size) : b.look i h = (Peek.view b.entries)[i]'h :=
  rfl

/-- Twice an entry of an array, through Lean's own getter. -/
def doubledRead {α : Type} [GetElem (Array α) Nat α fun a i => i < a.size] [Add α]
    (a : Array α) (i : Nat) (h : i < a.size) : α :=
  a[i]'h + a[i]'h

universe u

/-- A read that applies `f` to the entry it selects. -/
def lifted {p : Sort u} (f : PLift p → PLift p) (a : Array (PLift p)) (i : Nat) (h : i < a.size) :
    PLift p :=
  f (a[i]'h)

/-- At a proposition every entry is the same, so `lifted` is the selected entry there. -/
theorem lifted_eq {p : Prop} (f : PLift p → PLift p) (a : Array (PLift p)) (i : Nat)
    (h : i < a.size) : lifted f a i h = a[i]'h :=
  Subsingleton.elim _ _

/-- A getter of boxes through a dictionary of this file. -/
instance Box.instGetElem {α : Type} {n : Nat} : GetElem (Box α n) Nat α fun _ i => i < n where
  getElem b i h := b.entries[i]'(by rw [b.size_eq]; exact h)

end FloatLibTests.Conformance.BinaryInterchange.RoundoffReads

public meta section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffReads

open Lean FloatLib.Floats.Formats.BinaryInterchange

/-- Boxes: the read `Box.get` with its certificate, and `Box.twice` registered as a read without
one. -/
def boxes : Roundoff.Extension where
  containers := #[``Box]
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], selection := some ``Box.get_eq }, {
    head := ``Box.twice, arity := 5, types := #[``Box] }]

/-- `Box.twice` with the certificate of `Box.get`, which is about another read. -/
def otherCertificate : Roundoff.Extension where
  reads := #[{
    head := ``Box.twice, arity := 5, types := #[``Box], selection := some ``Box.get_eq }]

/-- `Box.twice` with a certificate that reads a computed observation of the box. -/
def computedCertificate : Roundoff.Extension where
  reads := #[{
    head := ``Box.twice, arity := 5, types := #[``Box], selection := some ``Box.twice_eq }]

/-- `Box.peek` with a certificate that reads a method of a trusted class that is no observer. -/
def otherMethod : Roundoff.Extension where
  reads := #[{
    head := ``Box.peek, arity := 6, fromEnd := 3, types := #[``Box], trusts := #[``Peek],
    observers := #[``Peek.view], selection := some ``Box.peek_eq }]

/-- `Box.look` with a certificate through the designated observer. -/
def viewed : Roundoff.Extension where
  reads := #[{
    head := ``Box.look, arity := 6, fromEnd := 3, types := #[``Box], trusts := #[``Peek],
    observers := #[``Peek.view], selection := some ``Box.look_eq }]

/-- `doubledRead` as a read through Lean's own array getter. -/
def doubledReads : Roundoff.Extension where
  reads := #[{
    head := ``doubledRead, arity := 6, fromEnd := 3, types := #[``Array], dictionary := some 5,
    dictionaries := #[``Array.instGetElemNatLtSize] }]

/-- A getter through `Fin.instGetElemFinVal` as a dictionary, which passes the read on. -/
def forwardingDictionary : Roundoff.Extension where
  reads := #[{
    head := ``GetElem.getElem, arity := 8, fromEnd := 3, types := #[``Array], dictionary := some 4,
    dictionaries := #[``Fin.instGetElemFinVal] }]

/-- A getter through `GetElem?.toGetElem` as a dictionary, which passes the read on. -/
def parentDictionary : Roundoff.Extension where
  reads := #[{
    head := ``GetElem.getElem, arity := 8, fromEnd := 3, types := #[``Array], dictionary := some 4,
    dictionaries := #[``GetElem?.toGetElem] }]

/-- A getter forwarding through `ite`, which is no instance. -/
def iteForwarding : Roundoff.Extension where
  reads := #[{
    head := ``GetElem.getElem, arity := 8, fromEnd := 3, types := #[``Array], dictionary := some 4,
    dictionaries := #[``Array.instGetElemNatLtSize], forwarding := #[``ite] }]

/-- `lifted` with a certificate at propositions only. -/
def oneUniverse : Roundoff.Extension where
  reads := #[{ head := ``lifted, arity := 5, fromEnd := 3, selection := some ``lifted_eq }]

/-- Addition registered as a read through Lean's own dictionary of `Float`. -/
def additions : Roundoff.Extension where
  reads := #[{
    head := ``Add.add, arity := 4, fromEnd := 2, types := #[``Float], dictionary := some 3,
    dictionaries := #[``instAddFloat] }]

/-- Lean's array getter registered with its index as the container. -/
def indexAsContainer : Roundoff.Extension where
  reads := #[{
    head := ``GetElem.getElem, arity := 8, fromEnd := 2, types := #[``Nat], dictionary := some 4,
    dictionaries := #[``Array.instGetElemNatLtSize] }]

/-- A getter through a dictionary of this file. -/
def ownDictionary : Roundoff.Extension where
  reads := #[{
    head := ``GetElem.getElem, arity := 8, fromEnd := 3, types := #[``Box], dictionary := some 4,
    dictionaries := #[``Box.instGetElem] }]

end FloatLibTests.Conformance.BinaryInterchange.RoundoffReads

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffReads

open Lean FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

section Boxes

attribute [local roundoff_extension] boxes

/-- A certified read of an input box is exact. -/
roundoff theorem get_error :=
  fun {n : Nat} (b : Box Value n) (i : Fin n) => ExecFloat.Binary.toReal (b.get i)

/-- A read without a certificate is analyzed as the function it is: the addition it computes
rounds. -/
roundoff theorem twice_error :=
  fun {n : Nat} (b : Box Value n) (i : Fin n) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (b.twice i)

-- A box of functions: the read selects a function, and applying it to a box is no read.
/--
error: roundoff: no numerical rule for tensor producer b; expose its computation or supply an
explicit bound
-/
#guard_msgs (whitespace := lax) in
roundoff theorem apply_entry_error :=
  fun {m n : Nat} (fs : Box (Box Value m → Fin m → Value) n) (b : Box Value m) (i : Fin n)
      (j : Fin m) => ExecFloat.Binary.toReal ((fs.get i) b j)

/-- The reference of the certified read is the entry itself, with no budget. -/
example {n : Nat} (b : Box Value n) (i : Fin n) :=
  show |ExecFloat.Binary.toReal (b.get i) - ExecFloat.Binary.toReal (b.get i)| ≤ 0 from
    get_error b i

-- The read without a certificate has the rounding of its sum.
run_meta do
  unless (← getConstInfo ``twice_error).type.containsConst (· == ``Model.halfUlpAt) do
    throwError "the read without a certificate is taken as exact"

end Boxes

/--
error: roundoff_extension: `reads` of `otherCertificate`: `Box.get_eq` does not state the read
`Box.twice` of its own variables
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] otherCertificate

/--
error: roundoff_extension: `reads` of `computedCertificate`: `Box.twice_eq` reads
`Array.map (fun x => x + x) b.entries`, which is not an observation of the container through its
fields and the observers of the read
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] computedCertificate

/--
error: roundoff_extension: `reads` of `otherMethod`: `Box.peek_eq` reads `Peek.doubled b.entries`,
which is not an observation of the container through its fields and the observers of the read
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] otherMethod

/--
error: roundoff_extension: `reads` of `oneUniverse`: `lifted_eq` states the read `lifted` at fixed
universes
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] oneUniverse

/--
error: roundoff_extension: `reads` of `ownDictionary`: `Box.instGetElem` is not an instance of
Lean's own library
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] ownDictionary

section Viewed

attribute [local roundoff_extension] viewed

-- A certificate through a designated observer of a trusted class is accepted.
run_meta do
  unless (Roundoff.extensions.getState (← getEnv)).names.contains ``viewed do
    throwError "the read through a designated observer was not registered"

end Viewed

/--
error: roundoff_extension: `reads` of `doubledReads`: `doubledRead` is not a class method read at
its dictionary
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] doubledReads

/--
error: roundoff_extension: `reads` of `iteForwarding`: `ite` is not an instance of Lean's own
library
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] iteForwarding

/--
error: roundoff_extension: `reads` of `forwardingDictionary`: `Fin.instGetElemFinVal` passes the
read on to another dictionary; it belongs to `forwarding`
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] forwardingDictionary

/--
error: roundoff_extension: `reads` of `parentDictionary`: `GetElem?.toGetElem` passes the read on to
another dictionary; it belongs to `forwarding`
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] parentDictionary

/--
error: roundoff_extension: `reads` of `additions`: `Add.add` at these positions and dictionaries is
not Lean's getter of lists, arrays and vectors
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] additions

/--
error: roundoff_extension: `reads` of `indexAsContainer`: `getElem` at these positions and
dictionaries is not Lean's getter of lists, arrays and vectors
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] indexAsContainer

/-- A read law whose premise Lean's default discharger can take from a local hypothesis. -/
theorem headD_map_eq_zero {f : Nat → Nat} {xs : List Nat} (h : ∀ a t, xs = a :: t → False) :
    (xs.map f).headD 0 = 0 := by
  cases xs with
  | nil => rfl
  | cons a t => exact (h a t rfl).elim

-- Tidying keeps no result across local contexts: the law rewrites the read under its premise `h`,
-- and the same read after the scope of `h` stays as it is.
open Meta in
run_meta do
  let session ← Roundoff.Session.prepare
  let theorems ← ({} : SimpTheorems).addConst ``headD_map_eq_zero
  let nat := mkConst ``Nat
  withLocalDeclD `f (← mkArrow nat nat) fun f => do
    withLocalDeclD `xs (← mkAppM ``List #[nat]) fun xs => do
      let read ← mkAppM ``List.headD #[← mkAppM ``List.map #[f, xs], ← mkNumeral nat 0]
      let premise ← withLocalDeclD `a nat fun a => do
        withLocalDeclD `t (← mkAppM ``List #[nat]) fun t => do
          mkForallFVars #[a, t]
            (← mkArrow (← mkEq xs (← mkAppM ``List.cons #[a, t])) (mkConst ``False))
      withLocalDeclD `h premise fun _ => do
        let tidied ← session.tidyTerm read (← Simp.mkContext {} #[theorems])
        if tidied.expr == read then throwError "the law did not apply under its premise"
      let tidied ← session.tidyTerm read (← Simp.mkContext {} #[theorems])
      unless tidied.expr == read do
        throwError "a tidied read was reused outside the scope of its premise"

end FloatLibTests.Conformance.BinaryInterchange.RoundoffReads
