/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Representation -- shake: keep
public meta import Lean.Elab.Command
import Lean.Exception

/-!
# Static format declarations

`float_format` declares a format identity, code type, scalar domain, and denotation:

```lean
float_format MyFormat where
  Code := UInt8
  Scalar := Rat
  denote := fun bits => ...
```

The tag has no constructors and occupies no runtime field; values store `Code`.
The generated semantic instance is `noncomputable` to allow real-valued denotations, while the
code type and `ExecFloat` carrier remain executable. Define operation capabilities, exact
observations, and conformance theorems separately.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- An assignment to `Code`, `Scalar`, or `denote` in a `float_format` declaration. -/
syntax floatFormatField := ident " := " term
/-- Parsed body of a `float_format` declaration. -/
syntax floatFormatBody :=
  " where " structInstFields(sepByIndentSemicolon(floatFormatField))
/-- Declare a static encoded numerical format and its denotation. -/
syntax (name := floatFormatDecl) "float_format " ident floatFormatBody : command

open Lean Elab Command in
elab_rules : command
  | `(float_format $formatName:ident where $[$fields:floatFormatField];*) => do
      unless fields.size == 3 do
        throwError "expected exactly the fields `Code`, `Scalar`, and `denote`"
      let `(floatFormatField| $codeName:ident := $codeType:term) := fields[0]!
        | throwUnsupportedSyntax
      let `(floatFormatField| $scalarName:ident := $scalarType:term) := fields[1]!
        | throwUnsupportedSyntax
      let `(floatFormatField| $denoteName:ident := $denotation:term) := fields[2]!
        | throwUnsupportedSyntax
      unless codeName.getId == `Code do
        throwErrorAt codeName "expected `Code` as the first field"
      unless scalarName.getId == `Scalar do
        throwErrorAt scalarName "expected `Scalar` as the second field"
      unless denoteName.getId == `denote do
        throwErrorAt denoteName "expected `denote` as the third field"
      let formatType ← `(term| $(mkIdent formatName.getId))
      elabCommand <| ← `(command|
        inductive $(mkIdent formatName.getId) : Type)
      elabCommand <| ← `(command|
        instance : EncodedFormat $formatType :=
          ⟨$codeType, $scalarType⟩)
      elabCommand <| ← `(command|
        noncomputable instance : FormatSemantics $formatType :=
          ⟨$denotation⟩)

end FloatLib.Numerics
