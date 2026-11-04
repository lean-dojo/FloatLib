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
Lean's own. A read that trusts a class (`Roundoff.Read.trusts`) pins each of the class's methods to
its observers by a law (`Roundoff.Read.laws`): registration rejects a method without one, a law with
a premise of its own, through itself, at fixed universes or under an observer that is not injective,
a class that holds another value, also as an observer, and a class whose proof field states its type
equal to another. Index data rejects a dictionary of a class whose law computes and one that a test
of computed values selects. A read rewrite whose premise a local hypothesis
discharges tidies a read only in that hypothesis's scope.
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

/-- A buffer of entries that a generic index computation may use: each method is pinned to the
observer `cells` by a law, `push` through the injectivity of `cells`. -/
class Shelf (α : Type) where
  /-- The buffer. -/
  Buffer : Type
  /-- The stored entries. -/
  cells : Buffer → Array α
  /-- The number of stored entries. -/
  size : Buffer → Nat
  /-- The entry at an index. -/
  get : (buffer : Buffer) → (i : Nat) → i < size buffer → α
  /-- The buffer with one more entry. -/
  push : Buffer → α → Buffer
  /-- An optional decision of the equality of entries. -/
  same? : Option (DecidableEq α) := none
  /-- The number of entries is that of the observation. -/
  size_eq (buffer : Buffer) : size buffer = (cells buffer).size
  /-- An entry is the observed entry. -/
  get_eq (buffer : Buffer) (i : Nat) (h : i < size buffer) :
    get buffer i h = (cells buffer)[i]'(by rw [← size_eq]; exact h)
  /-- Pushing an entry pushes it onto the observation. -/
  cells_push (buffer : Buffer) (value : α) : cells (push buffer value) = (cells buffer).push value
  /-- The observation determines the buffer. -/
  cells_injective : Function.Injective cells

/-- `n` entries in a shelf's buffer. -/
structure Rack (α : Type) [Shelf α] (n : Nat) where
  /-- The buffer. -/
  buffer : Shelf.Buffer α
  /-- It holds `n` entries. -/
  size_eq : Shelf.size buffer = n

/-- The entry `i` of a rack. -/
def Rack.get {α : Type} [Shelf α] {n : Nat} (r : Rack α n) (i : Fin n) : α :=
  Shelf.get r.buffer i.val (by rw [r.size_eq]; exact i.isLt)

/-- The entry `i` of a rack is the entry `i` of its observed buffer. -/
theorem Rack.get_eq_cells {α : Type} [Shelf α] {n : Nat} (r : Rack α n) (i : Fin n) :
    r.get i = (Shelf.cells r.buffer)[i.val]'(by rw [← Shelf.size_eq, r.size_eq]; exact i.isLt) :=
  Shelf.get_eq _ _ _

/-- The index of the larger of two entries of a rack, chosen by comparing them. -/
def Rack.larger {α : Type} [Shelf α] [LT α] [DecidableRel (α := α) (· < ·)] {n : Nat}
    (r : Rack α n) (i j : Fin n) : Fin n :=
  if r.get i < r.get j then j else i

/-- Whether a shelf decides the equality of its entries. -/
def Shelf.decides (α : Type) [Shelf α] : Bool :=
  (Shelf.same? (α := α)).isSome

/-- A read of a shelf's buffer with a premise of its own. -/
theorem Shelf.get_eq_of_pos {α : Type} [Shelf α] (buffer : Shelf.Buffer α) (i : Nat)
    (h : i < Shelf.size buffer) (_ : 0 < Shelf.size buffer) :
    Shelf.get buffer i h = (Shelf.cells buffer)[i]'(by rw [← Shelf.size_eq]; exact h) :=
  Shelf.get_eq _ _ _

/-- The size of a shelf's buffer read through itself. -/
theorem Shelf.size_eq_size {α : Type} [Shelf α] (buffer : Shelf.Buffer α) :
    Shelf.size buffer = Shelf.size buffer :=
  rfl

/-- A buffer with an observer that sees only part of what a method makes: `make` is pinned under
`view`, which is not injective. -/
class Pair (α : Type) where
  /-- The entries a pair shows. -/
  view : Array α × Nat → Array α
  /-- A pair from one entry. -/
  make : α → Array α × Nat
  /-- The made pair shows its entry. -/
  view_make (x : α) : view (make x) = #[x]

/-- A class whose type a proof field equates with a function type. -/
class Hidden (α : Type) where
  /-- The hidden type. -/
  Code : Type
  /-- It is a function type. -/
  reveal : Code = (α → Nat)

/-- A class whose proof field equates a type of its family with a function type. -/
class Family (α : Type) where
  /-- The family. -/
  Code : Unit → Type
  /-- Its type at `()` is a function type. -/
  reveal : Code () = (α → Nat)

/-- A class whose proof field relates its type to a function type by heterogeneous equality. -/
class Twin (α : Type) where
  /-- The type. -/
  Code : Type
  /-- Each of its values is heterogeneously equal to a function. -/
  reveal : ∀ c : Code, HEq c (fun _ : α => (0 : Nat))

/-- A buffer that also holds a callback on entries, a value that no law pins. -/
class Parcel (α : Type) where
  /-- The buffer. -/
  Buffer : Type
  /-- The stored entries. -/
  cells : Buffer → Array α
  /-- A callback. -/
  payload : Option (α → Nat)

/-- A class with a type and a decision of the equality of types, which can test that type. -/
class TypeBit (α : Type) where
  /-- The type. -/
  Code : Type
  /-- A decision of the equality of types. -/
  eqType : DecidableEq Type

/-- A universe polymorphic buffer of entries. -/
class Bin (α : Type u) where
  /-- The buffer. -/
  Buffer : Type u
  /-- The stored entries. -/
  cells : Buffer → Array α
  /-- The number of stored entries. -/
  size : Buffer → Nat
  /-- The number of entries is that of the observation. -/
  size_eq (buffer : Buffer) : size buffer = (cells buffer).size

/-- The size law of bins at the lowest universe only. -/
theorem Bin.size_eq_zero {α : Type} [Bin.{0} α] (buffer : Bin.Buffer α) :
    Bin.size buffer = (Bin.cells buffer).size :=
  Bin.size_eq buffer

/-- A buffer with a gauge whose law rounds in binary64: one and a half times the number of entries,
rounded. -/
class Meter (α : Type) where
  /-- The buffer. -/
  Buffer : Type
  /-- The stored entries. -/
  cells : Buffer → Array α
  /-- The gauge. -/
  gauge : Buffer → Nat
  /-- The gauge rounds `1.5` times the number of entries in binary64. -/
  gauge_eq (buffer : Buffer) :
    gauge buffer = (Float.ofNat (cells buffer).size * 1.5).toUInt64.toNat

/-- `n` entries in a meter's buffer. -/
structure Dial (α : Type) [Meter α] (n : Nat) where
  /-- The buffer. -/
  buffer : Meter.Buffer α
  /-- It holds `n` entries. -/
  size_eq : (Meter.cells buffer).size = n

/-- The entry `i` of a dial. -/
def Dial.get {α : Type} [Meter α] {n : Nat} (d : Dial α n) (i : Fin n) : α :=
  (Meter.cells d.buffer)[i.val]'(by rw [d.size_eq]; exact i.isLt)

/-- The entry `i` of a dial is the entry `i` of its observed buffer. -/
theorem Dial.get_eq {α : Type} [Meter α] {n : Nat} (d : Dial α n) (i : Fin n) :
    d.get i = (Meter.cells d.buffer)[i.val]'(by rw [d.size_eq]; exact i.isLt) :=
  rfl

section Factories

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Configured values in an array, with the optional decision of their equality `same?`. -/
@[instance_reducible] def arrayShelf (same? : Option (DecidableEq Value)) : Shelf Value where
  Buffer := Array Value
  cells := id
  size := Array.size
  get buffer i h := buffer[i]'h
  push := Array.push
  same? := same?
  size_eq _ := rfl
  get_eq _ _ _ := rfl
  cells_push _ _ := rfl
  cells_injective := Function.injective_id

/-- The shelf of configured values that decides their equality unless squaring `x` gives `x` back,
a test that rounds. -/
@[instance_reducible] def squaringShelf (x : Value) : Shelf Value :=
  arrayShelf (if x * x == x then none else some inferInstance)

/-- The shelf of configured values that decides their equality, whatever `x` is. -/
@[instance_reducible] def keptShelf (_ : Value) : Shelf Value :=
  arrayShelf (some inferInstance)

end Factories

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

/-- `Box.look` with a certificate through the designated observer of `Peek`, whose method
`doubled` has no law. -/
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

/-- Racks: the read `Rack.get` with its certificate, trusting the lawful class `Shelf`. -/
def racks : Roundoff.Extension where
  containers := #[``Rack]
  reads := #[{
    head := ``Rack.get, arity := 5, types := #[``Rack], trusts := #[``Shelf],
    observers := #[``Shelf.cells],
    laws := #[``Shelf.cells_injective, ``Shelf.size_eq, ``Shelf.get_eq, ``Shelf.cells_push],
    selection := some ``Rack.get_eq_cells }]

/-- `Rack.get` with the law of `Shelf.get` that takes a premise of its own. -/
def premiseLaw : Roundoff.Extension where
  reads := #[{
    head := ``Rack.get, arity := 5, types := #[``Rack], trusts := #[``Shelf],
    observers := #[``Shelf.cells],
    laws := #[``Shelf.cells_injective, ``Shelf.size_eq, ``Shelf.get_eq_of_pos, ``Shelf.cells_push],
    selection := some ``Rack.get_eq_cells }]

/-- `Rack.get` with a law that reads `Shelf.size` through itself. -/
def circularLaw : Roundoff.Extension where
  reads := #[{
    head := ``Rack.get, arity := 5, types := #[``Rack], trusts := #[``Shelf],
    observers := #[``Shelf.cells],
    laws := #[``Shelf.cells_injective, ``Shelf.size_eq_size, ``Shelf.get_eq, ``Shelf.cells_push],
    selection := some ``Rack.get_eq_cells }]

/-- `Box.get` trusting `Pair`, whose law states `Pair.make` under an observer that is not
injective. -/
def pairs : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Pair],
    observers := #[``Pair.view], laws := #[``Pair.view_make], selection := some ``Box.get_eq }]

/-- `Box.get` trusting `Hidden`, whose proof field equates its type with a function type. -/
def hidden : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Hidden],
    selection := some ``Box.get_eq }]

/-- `Box.get` trusting `Family`, whose proof field equates a type of its family with a function
type. -/
def families : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Family],
    selection := some ``Box.get_eq }]

/-- `Box.get` trusting `Twin`, whose proof field relates its type to a function type by
heterogeneous equality. -/
def twins : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Twin],
    selection := some ``Box.get_eq }]

/-- `Box.get` trusting `Family` with its family of types as an observer. -/
def familyObserver : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Family],
    observers := #[``Family.Code], selection := some ``Box.get_eq }]

/-- `Box.get` trusting `Twin` with its proof field as an observer. -/
def twinObserver : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Twin],
    observers := #[``Twin.reveal], selection := some ``Box.get_eq }]

/-- `Box.get` trusting `Parcel`, which holds a callback. -/
def parcels : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Parcel],
    observers := #[``Parcel.cells], selection := some ``Box.get_eq }]

/-- `Box.get` trusting `Parcel` with its callback as an observer, which is no function of the
container. -/
def payloadObserver : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Parcel],
    observers := #[``Parcel.cells, ``Parcel.payload], selection := some ``Box.get_eq }]

/-- `Box.get` trusting `TypeBit`, whose decision of the equality of types is no decision of
entries. -/
def typeBits : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``TypeBit],
    selection := some ``Box.get_eq }]

/-- `Box.get` trusting `Bin` with its size law at one universe. -/
def bins : Roundoff.Extension where
  reads := #[{
    head := ``Box.get, arity := 4, types := #[``Box], trusts := #[``Bin],
    observers := #[``Bin.cells], laws := #[``Bin.size_eq_zero], selection := some ``Box.get_eq }]

/-- Dials: the read `Dial.get` with its certificate, trusting `Meter`, whose law computes in
binary64. -/
def dials : Roundoff.Extension where
  containers := #[``Dial]
  reads := #[{
    head := ``Dial.get, arity := 5, types := #[``Dial], trusts := #[``Meter],
    observers := #[``Meter.cells], laws := #[``Meter.gauge_eq], selection := some ``Dial.get_eq }]

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

/--
error: roundoff_extension: `reads` of `viewed`: `Peek.doubled`, a method of the trusted class
`Peek`, has no law: `laws` needs one concluding `Peek.doubled x = t`, or `o (Peek.doubled x) = t`
for an observer `o` that another law states injective, where `x` are variables for all its
arguments in order, with no other premise
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] viewed

/--
error: roundoff_extension: `reads` of `premiseLaw`: `Shelf.get_eq_of_pos` does not state a method
of a trusted class of exactly its own variables, in order, alone or under an injective observer
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] premiseLaw

/--
error: roundoff_extension: `reads` of `circularLaw`: `Shelf.size_eq_size` reads `Shelf.size` through
itself
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] circularLaw

/--
error: roundoff_extension: `reads` of `pairs`: `Pair.view_make` does not state a method of a trusted
class of exactly its own variables, in order, alone or under an injective observer
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] pairs

/--
error: roundoff_extension: `reads` of `hidden`: `Hidden.reveal` relates a type of `Hidden` to
another type
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] hidden

/--
error: roundoff_extension: `reads` of `families`: `Family.reveal` relates a type of `Family` to
another type
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] families

/--
error: roundoff_extension: `reads` of `twins`: `Twin.reveal` relates a type of `Twin` to another
type
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] twins

/--
error: roundoff_extension: `reads` of `familyObserver`: `Family.Code`, an observer of the read,
holds a type, not a function of a container
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] familyObserver

/--
error: roundoff_extension: `reads` of `twinObserver`: `Twin.reveal`, an observer of the read, holds
a proof, not a function of a container
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] twinObserver

/--
error: roundoff_extension: `reads` of `parcels`: `Parcel.payload` of the trusted class `Parcel`
holds a value that no law pins
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] parcels

/--
error: roundoff_extension: `reads` of `payloadObserver`: `Parcel.payload` of the trusted class
`Parcel` holds a value that no law pins
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] payloadObserver

/--
error: roundoff_extension: `reads` of `typeBits`: `TypeBit.eqType`, a method of the trusted class
`TypeBit`, has no law: `laws` needs one concluding `TypeBit.eqType x = t`, or
`o (TypeBit.eqType x) = t` for an observer `o` that another law states injective, where `x` are
variables for all its arguments in order, with no other premise
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] typeBits

/--
error: roundoff_extension: `reads` of `bins`: `Bin.size_eq_zero` states `Bin.size` at fixed
universes
-/
#guard_msgs (whitespace := lax) in
attribute [local roundoff_extension] bins

/-- Configured values in an array, observed as they are. -/
instance valueShelf : Shelf Value where
  Buffer := Array Value
  cells := id
  size := Array.size
  get buffer i h := buffer[i]'h
  push := Array.push
  size_eq _ := rfl
  get_eq _ _ _ := rfl
  cells_push _ _ := rfl
  cells_injective := Function.injective_id

/-- Configured values in an array, with a gauge that rounds in binary64. -/
instance valueMeter : Meter Value where
  Buffer := Array Value
  cells := id
  gauge buffer := (Float.ofNat buffer.size * 1.5).toUInt64.toNat
  gauge_eq _ := rfl

/-- The shelf of configured values, whatever the flag. -/
@[instance_reducible] def shelfAt (_ : Bool) : Shelf Value := valueShelf

section Storage

attribute [local roundoff_extension] racks dials

/-- The index that comparing two entries of a rack selects is index data: the generic comparison
takes the dictionary of the lawful class `Shelf`. -/
roundoff theorem larger_error :=
  fun {n : Nat} (r : Rack Value n) (i j : Fin n) => (((r.larger i j : Fin n) : ℕ) : ℝ)

/-- The size of a buffer of a local dictionary of `Shelf` is index data. -/
roundoff theorem size_error :=
  fun [Shelf Value] (buffer : Shelf.Buffer Value) => ((Shelf.size buffer : ℕ) : ℝ)

-- A dictionary whose optional decision a test of computed values selects is neither an input nor
-- a constant, so the helper that reads the decision is not index data.
/--
error: roundoff: ↑(Shelf.decides Value).toNat casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem same_error :=
  fun (x : Value) =>
    (((@Shelf.decides Value
      { valueShelf with same? := if x * x == x then none else some inferInstance }).toNat : ℕ) :
        ℝ)

-- A constant dictionary applied to a computed value is no index data, even when it ignores it.
/--
error: roundoff: ↑(Shelf.decides Value).toNat casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem computed_shelf_error :=
  fun (x : Value) => (((@Shelf.decides Value (shelfAt (x * x == x))).toNat : ℕ) : ℝ)

-- A constant factory that receives a value and tests it to choose its optional decision is no
-- index data, although its argument is: the decision is neither `none` nor `some` for a generic
-- argument.
/--
error: roundoff: ↑(Shelf.decides Value).toNat casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem squaring_shelf_error :=
  fun (x : Value) => (((@Shelf.decides Value (squaringShelf x)).toNat : ℕ) : ℝ)

/-- A constant factory that receives a value and fixes its optional decision is index data. -/
roundoff theorem kept_shelf_error :=
  fun (x : Value) => (((@Shelf.decides Value (keptShelf x)).toNat : ℕ) : ℝ)

-- A class whose law rounds in binary64 is no storage of the read that trusts it.
/--
error: roundoff: ↑(Meter.gauge d.buffer) casts an integer computed from real or floating-point
values, so the reference would keep them; compute it from index data
-/
#guard_msgs (whitespace := lax) in
roundoff theorem gauge_error :=
  fun {n : Nat} (d : Dial Value n) => ((Meter.gauge d.buffer : ℕ) : ℝ)

end Storage

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
