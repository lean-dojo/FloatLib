/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.IEEEComparison
public meta import FloatLib.Util.Declaration
public meta import Lean.Elab.Command

/-!
# The operation names of IEEE 754-2019 for a family with a parameter

IEEE 754-2019 names each member of a family of operations separately: five
`roundToIntegral...` operations, ten `convertToInteger...` operations and 22 comparisons.
FloatLib defines each family once, with the rounding direction or the comparison predicate as an
argument. The commands of this module declare the members under the names of the standard,
each as the family at one argument:

* `ieee_by_direction "clause" family binders : type := fun mode => body` declares
  `family<Suffix>` for the five rounding-direction attributes of IEEE 754-2019 §4.3, with the
  suffixes of `directionSuffixes`: `TiesToEven`, `TiesToAway`, `TowardZero`, `TowardPositive`
  and `TowardNegative`. `family of source` is for a `body` that calls a declaration `source`
  of another name.
* `ieee_by_predicate "clause" family binders : type := fun predicate => body` declares
  `family<Predicate>` for every constructor of `IEEEComparison.Predicate`, with its name
  capitalized: `Equal`, `NotEqual`, `Greater` and so on. `without unordered ordered` leaves out
  the two predicates that have no signaling form in the standard.

* `ieee_extrema source binders : type := fun larger magnitude number => body` declares the
  eight minimum and maximum operations of §9.6 from one selection with three Boolean
  parameters.

* `ieee_recommended source binders : type := fun function => body` declares the functions of
  one argument of §9.2 (`exp2`, `sin`, `atanh`, ...), one for each entry of the table
  `recommendedFunctions`, which holds the names and the texts of the docstrings. With
  `certified` before `source` the docstrings are those of functions that return `none` when no
  enclosure settles the result.

* `ieee_tag_members [attributes] family by direction` (or `by predicate`, `by extremum`) adds
  attributes to the members that the first three commands declare, for a later module that
  registers them, for instance as selectors that `float_decide` unfolds.

Every declared operation is `body` with the direction, the predicate, the function or the
Booleans substituted, so it
unfolds to the family and the theorems of the family apply to it. Its docstring cites the
clause given to the command. The names are those of the operation table of ISO/IEC 9899:2024
(C23, working draft N3220) Annex F, Table F.2, which lists the operations of ISO/IEC 60559,
the same text as IEEE 754-2019. That table prints `roundToIntegralTiesAway` where the family
`convertToInteger` and IEEE 754-2008 have `TiesToAway`, which is the suffix used here.
-/

public meta section

namespace FloatLib.Numerics.IEEENames

open Lean Elab Command

/--
The rounding-direction attributes of IEEE 754-2019 §4.3: the constructor that names the
direction in FloatLib's direction types, the suffix of the operation names, and the name of the
attribute.
-/
def directionSuffixes : List (Name × String × String) :=
  [(`nearest, "TiesToEven", "roundTiesToEven"), (`nearestAway, "TiesToAway", "roundTiesToAway"),
    (`towardZero, "TowardZero", "roundTowardZero"), (`up, "TowardPositive", "roundTowardPositive"),
    (`down, "TowardNegative", "roundTowardNegative")]

/-- A documentation comment with the given text: the shared `ExecFloat.generatedDoc`. -/
def docComment (text : String) : TSyntax ``Lean.Parser.Command.docComment :=
  FloatLib.Floats.ExecFloat.generatedDoc text

/--
`body` with every occurrence of the identifier `parameter` replaced by `argument`. The name of
a named argument `(name := value)` is kept, so `(mode := mode)` becomes `(mode := argument)`.
-/
partial def substitute (parameter : Name) (argument : Syntax) : Syntax → Syntax
  | .node info kind arguments =>
      if kind == ``Lean.Parser.Term.namedArgument then
        .node info kind (arguments.modify 3 (substitute parameter argument))
      else
        .node info kind (arguments.map (substitute parameter argument))
  | body => if body.isIdent && body.getId == parameter then argument else body

/--
Declare one member of a family: `family<suffix>` is `body` at `argument`. `source` is the
declaration that `body` calls, which the docstring names.
-/
def declareMember (clause : String) (family source : Ident) (suffix description : String)
    (binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder) (type : Term)
    (parameter : Ident) (argument : Term) (body : Term) : CommandElabM Unit := do
  let name := mkIdentFrom family (family.getId.appendAfter suffix)
  let text := s!"{clause} `{family.getId.appendAfter suffix}`: `{source.getId}` {description}."
  let value : Term := ⟨substitute parameter.getId argument body⟩
  elabCommand (← `($(docComment text):docComment
    @[inline] def $name $binders* : $type := $value))

/--
`ieee_by_direction "clause" family binders : type := fun mode => body` declares the five
operations `family<Suffix>` of IEEE 754-2019, one for each rounding-direction attribute, as
`body` with `mode` replaced by the direction. `family of source` names the members after
`family` when `body` calls the declaration `source`.

Reference: ISO/IEC 9899:2024 (WG14 N3220), Annex F, Table F.2 (operation names bound to IEEE
754-2019).
-/
syntax (name := ieeeByDirection) "ieee_by_direction " str ident (" of " ident)?
  bracketedBinder* " : " term " := " "fun " ident " => " term : command

elab_rules : command
  | `(ieee_by_direction $clause:str $family:ident $[of $source:ident]? $binders* : $type :=
      fun $parameter:ident => $body) => do
    for (direction, suffix, attributeName) in directionSuffixes do
      let argument : Term := ⟨mkNode ``Lean.Parser.Term.dotIdent
        #[mkAtom ".", mkIdent direction]⟩
      declareMember clause.getString family (source.getD family) suffix
        s!"in the rounding direction {attributeName}" binders type parameter argument body

/--
`ieee_by_predicate "clause" family binders : type := fun predicate => body` declares the
operations `family<Predicate>` of IEEE 754-2019, one for each constructor of
`IEEEComparison.Predicate` that is not listed after `without`, as `body` with `predicate`
replaced by the constructor.

Reference: ISO/IEC 9899:2024 (WG14 N3220), Annex F, Table F.2 (operation names bound to IEEE
754-2019).
-/
syntax (name := ieeeByPredicate) "ieee_by_predicate " str ident bracketedBinder* " : " term
  " := " "fun " ident " => " term (" without " ident+)? : command

elab_rules : command
  | `(ieee_by_predicate $clause:str $family:ident $binders* : $type :=
      fun $parameter:ident => $body $[without $excluded*]?) => do
    let excluded := (excluded.getD #[]).map (·.getId)
    let info ← getConstInfoInduct ``FloatLib.Numerics.IEEEComparison.Predicate
    for predicate in info.ctors do
      let .str _ short := predicate | continue
      unless excluded.contains (Name.mkSimple short) do
        let argument : Term := ⟨mkNode ``Lean.Parser.Term.dotIdent
          #[mkAtom ".", mkIdent (Name.mkSimple short)]⟩
        declareMember clause.getString family family short.capitalize
          s!"with the predicate `.{short}`" binders type parameter argument body

/--
The name of a minimum or maximum operation of IEEE 754-2019 §9.6 from what selects it: whether
the larger operand is selected, whether the operands are compared by magnitude, and whether a
number is preferred to a NaN.
-/
def extremumName (selectLarger byMagnitude byNumber : Bool) : String :=
  (if selectLarger then "maximum" else "minimum") ++ (if byMagnitude then "Magnitude" else "") ++
    (if byNumber then "Number" else "")

/--
`ieee_extrema source binders : type := fun larger magnitude number => body` declares the eight
minimum and maximum operations of IEEE 754-2019 §9.6: `minimum`, `maximum`,
`minimumMagnitude`, `maximumMagnitude`, `minimumNumber`, `maximumNumber`,
`minimumMagnitudeNumber` and `maximumMagnitudeNumber`. Each is `body` with the three Boolean
parameters replaced by `true` or `false`: whether the larger operand is selected, whether the
operands are compared by magnitude, and whether a number is preferred to a NaN. `source` is the
declaration that `body` calls. The docstrings cite the C23 functions that Table F.2 of
ISO/IEC 9899:2024 (N3220) binds to the operations.
-/
syntax (name := ieeeExtrema) "ieee_extrema " ident bracketedBinder* " : " term
  " := " "fun " ident ident ident " => " term : command

elab_rules : command
  | `(ieee_extrema $source:ident$binders* : $type :=
      fun $larger:ident$magnitude:ident$number:ident => $body) => do
    for byNumber in [false, true] do
      for byMagnitude in [false, true] do
        for selectLarger in [true, false] do
          let base := if selectLarger then "maximum" else "minimum"
          let name := extremumName selectLarger byMagnitude byNumber
          let function := "f" ++ base ++ (if byMagnitude then "_mag" else "") ++
            (if byNumber then "_num" else "")
          let clause := 4 + (if byNumber then 4 else 0) + (if byMagnitude then 2 else 0) +
            (if selectLarger then 0 else 1)
          let text := s!"IEEE 754-2019 §9.6 `{name}` (C23 `{function}`, \
            N3220 7.12.12.{clause}): " ++
            s!"`{source.getId}` for the {if selectLarger then "larger" else "smaller"} operand" ++
            (if byMagnitude then ", compared by magnitude" else "") ++
            (if byNumber then ", with a number preferred to a NaN" else "") ++ "."
          let literal (value : Bool) : CommandElabM Term :=
            if value then `(true) else `(false)
          let value := substitute larger.getId (← literal selectLarger) body
          let value := substitute magnitude.getId (← literal byMagnitude) value
          let value : Term := ⟨substitute number.getId (← literal byNumber) value⟩
          elabCommand (← `($(docComment text):docComment
            @[inline] def $(mkIdentFrom source (Name.mkSimple name)) $binders* : $type := $value))

/--
`ieee_tag_members [attributes] family by direction` adds the attributes to the five members
`family<Suffix>` that `ieee_by_direction` declares; `... by predicate` to the members
`family<Predicate>` that `ieee_by_predicate` declares, except the predicates listed after
`without`; and `... by extremum` to the eight operations of §9.6 in the namespace `family`.
A later module uses it to register the members with an attribute that is not yet available
where they are declared.
-/
syntax (name := ieeeTagMembers) "ieee_tag_members " "[" Lean.Parser.Term.attrInstance,* "] "
  ident " by " ident (" without " ident+)? : command

elab_rules : command
  | `(ieee_tag_members [$attributes,*] $family:ident by $kind:ident
      $[without $excluded*]?) => do
    let excluded := (excluded.getD #[]).map (·.getId)
    let members : List Name ←
      match kind.getId with
      | `direction =>
          pure (directionSuffixes.map fun (_, suffix, _) => family.getId.appendAfter suffix)
      | `predicate => do
          let info ← getConstInfoInduct ``FloatLib.Numerics.IEEEComparison.Predicate
          pure (info.ctors.filterMap fun
            | .str _ short =>
                if excluded.contains (Name.mkSimple short) then none
                else some (family.getId.appendAfter short.capitalize)
            | _ => none)
      | `extremum =>
          pure ([false, true].flatMap fun byNumber => [false, true].flatMap fun byMagnitude =>
            [true, false].map fun selectLarger =>
              family.getId ++ Name.mkSimple (extremumName selectLarger byMagnitude byNumber))
      | _ => throwErrorAt kind "expected `direction`, `predicate` or `extremum`"
    for member in members do
      elabCommand (← `(attribute [$attributes,*] $(mkIdentFrom family member)))

/--
The functions of one argument that IEEE 754-2019 §9.2 recommends, under their names in
ISO/IEC 9899:2024 Table F.2, each with what its docstring says: the function, the clauses of
ISO/IEC 9899:2024 that specify it, and its special cases.
-/
def recommendedFunctions : List (Name × String) :=
  [
    (`exp2,
      "`2 ^ x` (ISO/IEC 9899:2024 7.12.6.4, F.10.3.4). `exp2 (±0)` is 1, `exp2 (-∞)` is " ++
      "`+0` and `exp2 (+∞)` is `+∞`."),
    (`exp2m1,
      "`2 ^ x - 1` with one rounding (ISO/IEC 9899:2024 7.12.6.5, F.10.3.5). `exp2m1 (±0)` " ++
      "is `±0`, `exp2m1 (-∞)` is -1 and `exp2m1 (+∞)` is `+∞`."),
    (`exp10,
      "`10 ^ x` (ISO/IEC 9899:2024 7.12.6.2, F.10.3.2). `exp10 (±0)` is 1, `exp10 (-∞)` is " ++
      "`+0` and `exp10 (+∞)` is `+∞`."),
    (`exp10m1,
      "`10 ^ x - 1` with one rounding (ISO/IEC 9899:2024 7.12.6.3, F.10.3.3). `exp10m1 " ++
      "(±0)` is `±0`, `exp10m1 (-∞)` is -1 and `exp10m1 (+∞)` is `+∞`."),
    (`log2,
      "the logarithm to base 2 (ISO/IEC 9899:2024 7.12.6.15, F.10.3.15). `log2 (±0)` is " ++
      "`-∞` with `divideByZero`, `log2 1` is `+0`, a negative operand is invalid and `log2 " ++
      "(+∞)` is `+∞`."),
    (`log10,
      "the logarithm to base 10 (ISO/IEC 9899:2024 7.12.6.12, F.10.3.12). `log10 (±0)` is " ++
      "`-∞` with `divideByZero`, `log10 1` is `+0`, a negative operand is invalid and " ++
      "`log10 (+∞)` is `+∞`."),
    (`log2p1,
      "the logarithm to base 2 of the exact `1 + x` (ISO/IEC 9899:2024 7.12.6.16, " ++
      "F.10.3.16). `log2p1 (±0)` is `±0`, `log2p1 (-1)` is `-∞` with `divideByZero`, an " ++
      "operand below -1 is invalid and `log2p1 (+∞)` is `+∞`."),
    (`log10p1,
      "the logarithm to base 10 of the exact `1 + x` (ISO/IEC 9899:2024 7.12.6.13, " ++
      "F.10.3.13). `log10p1 (±0)` is `±0`, `log10p1 (-1)` is `-∞` with `divideByZero`, an " ++
      "operand below -1 is invalid and `log10p1 (+∞)` is `+∞`."),
    (`sin,
      "the sine of a radian argument (ISO/IEC 9899:2024 7.12.4.6, F.10.1.6). `sin (±0)` is " ++
      "`±0` and `sin (±∞)` is invalid."),
    (`cos,
      "the cosine of a radian argument (ISO/IEC 9899:2024 7.12.4.5, F.10.1.5). `cos (±0)` " ++
      "is 1 and `cos (±∞)` is invalid."),
    (`tan,
      "the tangent of a radian argument (ISO/IEC 9899:2024 7.12.4.7, F.10.1.7). `tan (±0)` " ++
      "is `±0` and `tan (±∞)` is invalid. A finite operand is rational and so never a pole."),
    (`sinPi,
      "`sin (π x)` (ISO/IEC 9899:2024 7.12.4.13, F.10.1.13). `sinPi` of an integer, zero " ++
      "included, is the zero of the operand's sign, and `sinPi (±∞)` is invalid."),
    (`cosPi,
      "`cos (π x)` (ISO/IEC 9899:2024 7.12.4.12, F.10.1.12). `cosPi (±0)` is 1, `cosPi (n + " ++
      "1/2)` is `+0` for an integer `n`, and `cosPi (±∞)` is invalid."),
    (`tanPi,
      "`tan (π x)` (ISO/IEC 9899:2024 7.12.4.14, F.10.1.14). `tanPi (±0)` is `±0`; at a " ++
      "positive even or negative odd integer it is `+0`, and at a positive odd or negative " ++
      "even integer `-0`; `tanPi (n + 1/2)` is `+∞` for even `n` and `-∞` for odd `n`, with " ++
      "`divideByZero`; `tanPi (±∞)` is invalid."),
    (`asin,
      "the inverse sine in `[-π/2, π/2]` (ISO/IEC 9899:2024 7.12.4.2, F.10.1.2). `asin " ++
      "(±0)` is `±0` and an operand of magnitude above 1 is invalid."),
    (`acos,
      "the inverse cosine in `[0, π]` (ISO/IEC 9899:2024 7.12.4.1, F.10.1.1). `acos 1` is " ++
      "`+0` and an operand of magnitude above 1 is invalid."),
    (`atan,
      "the inverse tangent in `[-π/2, π/2]` (ISO/IEC 9899:2024 7.12.4.3, F.10.1.3). `atan " ++
      "(±0)` is `±0` and `atan (±∞)` is `±π/2` rounded."),
    (`asinPi,
      "`asin x / π` (ISO/IEC 9899:2024 7.12.4.9, F.10.1.9). `asinPi (±0)` is `±0` and an " ++
      "operand of magnitude above 1 is invalid."),
    (`acosPi,
      "`acos x / π` (ISO/IEC 9899:2024 7.12.4.8, F.10.1.8). `acosPi 1` is `+0` and an " ++
      "operand of magnitude above 1 is invalid."),
    (`atanPi,
      "`atan x / π` (ISO/IEC 9899:2024 7.12.4.10, F.10.1.10). `atanPi (±0)` is `±0` and " ++
      "`atanPi (±∞)` is `±1/2`."),
    (`sinh,
      "the hyperbolic sine (ISO/IEC 9899:2024 7.12.5.5, F.10.2.5). `sinh (±0)` is `±0` and " ++
      "`sinh (±∞)` is `±∞`."),
    (`cosh,
      "the hyperbolic cosine (ISO/IEC 9899:2024 7.12.5.4, F.10.2.4). `cosh (±0)` is 1 and " ++
      "`cosh (±∞)` is `+∞`."),
    (`tanh,
      "the hyperbolic tangent (ISO/IEC 9899:2024 7.12.5.6, F.10.2.6). `tanh (±0)` is `±0` " ++
      "and `tanh (±∞)` is `±1`."),
    (`asinh,
      "the inverse hyperbolic sine (ISO/IEC 9899:2024 7.12.5.2, F.10.2.2). `asinh (±0)` is " ++
      "`±0` and `asinh (±∞)` is `±∞`."),
    (`acosh,
      "the inverse hyperbolic cosine (ISO/IEC 9899:2024 7.12.5.1, F.10.2.1). `acosh 1` is " ++
      "`+0`, an operand below 1 is invalid and `acosh (+∞)` is `+∞`."),
    (`atanh,
      "the inverse hyperbolic tangent (ISO/IEC 9899:2024 7.12.5.3, F.10.2.3). `atanh (±0)` " ++
      "is `±0`, `atanh (±1)` is `±∞` with `divideByZero` and an operand of magnitude above " ++
      "1 is invalid.")]

/--
`ieee_recommended source binders : type := fun function => body` declares the functions of one
argument of IEEE 754-2019 §9.2, one for each entry of `recommendedFunctions`, as `body` with
`function` replaced by the member of that name of the enumeration that `source` applies. The
docstring of a member is its entry of the table. `ieee_recommended certified source ...` is for
functions that return a result only when an enclosure settles it: the docstring then keeps the
first sentence of the entry, which names the function and its clauses, and says so.
-/
syntax (name := ieeeRecommended) "ieee_recommended " (&"certified ")? ident bracketedBinder*
  " : " term " := " "fun " ident " => " term : command

/-- The first sentence of a text of `recommendedFunctions`: the function and its clauses. -/
def definitionSentence (text : String) : String :=
  match text.splitOn "). " with
  | first :: _ :: _ => first ++ ")."
  | _ => text

/-- Declare the member of every entry of `recommendedFunctions`, for `ieee_recommended`. -/
def declareRecommended (settles : Bool) (source : Ident)
    (binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder) (type : Term) (parameter : Ident)
    (body : Term) : CommandElabM Unit := do
  for (member, text) in recommendedFunctions do
    let argument : Term := ⟨mkNode ``Lean.Parser.Term.dotIdent #[mkAtom ".", mkIdent member]⟩
    let description :=
      if settles then
        s!"IEEE 754-2019 §9.2 `{member}`, certified: {definitionSentence text} " ++
          s!"It is `{source.getId}` at the member `.{member}`: the nearest-even rounding of " ++
          "the real function when an enclosure settles it, and `none` otherwise."
      else
        s!"IEEE 754-2019 §9.2 `{member}`: {text} " ++
          s!"It is `{source.getId}` at the member `.{member}`: the value with its flags."
    let value : Term := ⟨substitute parameter.getId argument body⟩
    elabCommand (← `($(docComment description):docComment
      @[inline] def $(mkIdentFrom source member) $binders* : $type := $value))

elab_rules : command
  | `(ieee_recommended $source:ident $binders* : $type := fun $parameter:ident => $body) =>
    declareRecommended false source binders type parameter body
  | `(ieee_recommended certified $source:ident $binders* : $type :=
      fun $parameter:ident => $body) =>
    declareRecommended true source binders type parameter body

end FloatLib.Numerics.IEEENames
