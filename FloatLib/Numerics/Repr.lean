/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Printing status records and outcomes

`#eval` shows a status record with only its raised flags, as `{ inexact := true }`, and `{}` when
none is raised. Every flag defaults to `false`, so the omitted fields are exactly the clear ones.
Outcomes and failure reasons print their constructors with a leading dot, as in
`.failure (.infinity .source (negative := false))`, naming a Boolean argument instead of leaving a
bare `true` or `false`.

The text is meant to be read. The value inside an outcome prints as its format displays it, so
`inf`, `nan` and `NaR` appear as text, and the default display of a NaN omits its sign and payload.
A printed outcome is therefore not a serialization format, even where it happens to be valid Lean.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
A record written as `{ name := value, ... }`, laid out the way a derived `Repr` lays out a
structure, or `{}` when there are no fields.
-/
def reprRecord (fields : List (String × Std.Format)) : Std.Format :=
  match fields with
  | [] => "{}"
  | _ =>
      Std.Format.bracket "{ "
        (Std.Format.joinSep
          (fields.map fun (name, value) =>
            Std.Format.text (name ++ " := ") ++
              Std.Format.group (Std.Format.nest (name.length + 4) value))
          ("," ++ Std.Format.line))
        " }"

/-- The raised flags of a record of Boolean flags, as `{ inexact := true }`, or `{}` for none. -/
def reprFlags (flags : List (String × Bool)) : Std.Format :=
  reprRecord (flags.filterMap fun (name, raised) => if raised then some (name, "true") else none)

/--
A constructor applied to its printed arguments, written with a leading dot as `.name arg ...`.
An application is parenthesized at argument precedence. A constructor without arguments never is.
-/
def reprConstructor (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  match args with
  | [] => Std.Format.text ("." ++ name)
  | _ =>
      Repr.addAppParen
        (Std.Format.group (Std.Format.nest (if prec >= max_prec then 1 else 2)
          (Std.Format.joinSep (Std.Format.text ("." ++ name) :: args) Std.Format.line)))
        prec

/-- A named argument, `(name := value)`. -/
def reprNamedArg (name : String) (value : Std.Format) : Std.Format :=
  "(" ++ Std.Format.text name ++ " := " ++ value ++ ")"

end FloatLib.Numerics
