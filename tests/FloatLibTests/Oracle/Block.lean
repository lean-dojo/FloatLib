/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.OCP.MX.Standard.Compiled

import FloatLib.Floats.Formats.Block.Stored
import FloatLib.Floats.Formats.Block.Working
import FloatLib.Floats.Formats.Block.CodedDot
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
import FloatLibTests.Oracle.Parsing

/-!
# Block-format vectors for external comparison

`oracle block CASE` reads tensors of binary32 words from standard input, one tensor per line in
hexadecimal, and writes FloatLib's stored codes and decoded values. `tests/oracles/block_formats.py`
compares them bit for bit with torchao's MX and NVFP4 reference quantizers, Microsoft's
`microxcaling`, and PyTorch's float8 casts.

The cases are:

* `mx PROFILE POLICY`: one OCP MX block per line. `PROFILE` is one of the six element profiles and
  `POLICY` is `floor` (the rule of §6.3 with FloatLib's all-zero convention), `floor0` (an all-zero
  block gets `2 ^ -127`), `ceil` (scale rounded up), or `rceil` (the least power-of-two scale
  without saturation).
* `dot LEFT RIGHT`: MX blocks with independent operand profiles. Each block is 66 words:
  two scale codes followed by 32 pairs of element codes. Returns the binary32 words of
  `Dot` and `DotGeneral`, each with exact intermediates and one final rounding.
* `finite-dot LEFT RIGHT PRODUCT ACCUMULATOR OUTPUT`: the same stored blocks, with
  independently selected binary16, binary32 or binary64 product, accumulator and output
  formats. Each product is rounded, cast to the accumulator, and added in order.
* `nvfp4 single VARIANT`: blocks of 16 without an outer scale. `VARIANT` is `exact` or `clamp`,
  which keeps the ideal scale at least `2 ^ -6` as torchao does.
* `nvfp4 two VARIANT`: the first word of a line is the outer scale and the rest are blocks of 16.
* `nvfp4f32 single` and `nvfp4f32 two`: the same tensors through `Block.nvfp4Working`, the
  library's quantizer on binary32 encodings in the order of torchao's `nvfp4_quantize`.
* `cast FORMAT MODE`: element conversion of each word, with `MODE` `native` or `saturate`.

An output line has the scale codes, a bar, the element codes, a bar, and the decoded values as
binary32 words, each rounded once from the exact rational. A word that is not finite gives `x`.
-/

namespace FloatLibTests.Oracle.Block

open FloatLib.Numerics
open FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.OCP.MX
open FloatLibTests.Oracle.Parsing

/-- A binary32 word. -/
abbrev F32 := Model FloatFormat.binary32

/-- Exact signed rational of a finite binary32 word. -/
def inputValue (bits : Nat) : Option SignedRat :=
  match Block.Codec.decodeModel (Model.ofNatBits (fmt := FloatFormat.binary32) bits) with
  | .finite value => some value
  | _ => none

/-- Binary32 word of an exact signed rational, rounded once. -/
def wordOfSigned (value : SignedRat) : Nat :=
  (Model.roundRat FloatFormat.binary32 value.negative value.value.num.natAbs
    value.value.den).toNatBits

/-- Text of a decoded position: its binary32 word, or `x` when it is not finite. -/
def valueText (value : NumericalValue SignedRat) : String :=
  match value with
  | .finite exact => toString (wordOfSigned exact)
  | _ => "x"

def joinNat (values : List Nat) : String :=
  " ".intercalate (values.map toString)

/-- The policies of the `mx` case. -/
def mxPolicy {n : Nat} (profile : Standard.Profile) (name : String) :
    Option (Block.Policy (Fin n) Unit) :=
  let group : Fin n → Unit := fun _ => ()
  let target : ℚ := 2 ^ profile.maxPowerExponent
  let largest : ℚ :=
    match profile with
    | .e5m2 => 57344
    | .e4m3 => 448
    | .e3m2 => 28
    | .e2m3 => 15 / 2
    | .e2m1 => 6
    | .int8 => 127 / 64
  match name with
  | "floor" => some (Standard.policy group profile)
  | "floor0" => some [Block.Selection.ofMax group target (2 ^ (-127 : ℤ))]
  | "ceil" => some (Block.mxCeil group profile.maxPowerExponent)
  | "rceil" => some (Block.mxMaxCeil group largest)
  | _ => none

def profile? : String → Option Standard.Profile
  | "e5m2" => some .e5m2
  | "e4m3" => some .e4m3
  | "e3m2" => some .e3m2
  | "e2m3" => some .e2m3
  | "e2m1" => some .e2m1
  | "int8" => some .int8
  | _ => none

/-- IEEE descriptors accepted by the finite-intermediate comparison protocol. -/
def binaryFormat? : String → Option FloatFormat
  | "16" => some .binary16
  | "32" => some .binary32
  | "64" => some .binary64
  | _ => none

/-- Finite compiled element conversion, with no scale selection. -/
def runElement (profile : Standard.Profile) (words : Array Nat) :
    Option String := do
  let inputs ← words.mapM inputValue
  let codes := inputs.toList.map fun input => (Standard.Element.quantizeFinite profile input).toNat
  pure s!" | {joinNat codes} | "

/-- One OCP MX block: scale code, element codes, decoded values. -/
def runMx (profile : Standard.Profile) (policyName : String) (words : Array Nat) :
    Option String := do
  let inputs ← words.mapM inputValue
  let n := inputs.size
  let policy ← mxPolicy (n := n) profile policyName
  let format := Standard.format (fun _ : Fin n => ()) profile
  let tensor := format.quantize policy fun i => inputs.getD i.val 0
  let codes := (List.finRange n).map fun i => (tensor.elements i).toNat
  let values := (List.finRange n).map fun i => valueText (tensor.decode i)
  pure s!"{(tensor.scales.1 ()).toNat} | {joinNat codes} | {" ".intercalate values}"

/-- Stored MX dot observations, using the same decoded words in both standard operations. -/
def runDot (left right : Standard.Profile) (output : FloatFormat)
    (reduction : Block.Reduction) (words : Array Nat) : Option String := do
  if words.size % 66 != 0 then failure
  let count := words.size / 66
  let group : Fin (32 * count) → Nat := fun i => i.val / 32
  let tensor (profile : Standard.Profile) (side : Nat) :
      Block.Tensor (Standard.format group profile) :=
    { scales := (fun block => E8M0.ofNatBits (words.getD (66 * block + side) 0), ())
      elements := fun i =>
        BitVec.ofNat profile.width
          (words.getD (66 * (i.val / 32) + 2 + 2 * (i.val % 32) + side) 0) }
  let a := tensor left 0
  let b := tensor right 1
  let order := List.finRange (32 * count)
  let blocks := (List.range count).map fun block => order.filter fun i => group i == block
  let dot := (OCP.MX.Dot output a b order reduction).toNatBits
  let general := (OCP.MX.DotGeneral output a b blocks reduction).toNatBits
  pure s!" | {dot} {general} | "

/-- The block rule of NVFP4, and the variant that keeps the ideal scale at least `2 ^ -6`. -/
def blockRule (n : Nat) (variant : String) : Option (Block.Selection (Fin n) Nat) :=
  let rule : Block.Selection (Fin n) Nat := Block.Selection.ofMax (fun i => i.val / 16) 6 0
  match variant with
  | "exact" => some rule
  | "clamp" => some (rule.map fun scale => max scale (1 / 64))
  | _ => none

/-- NVFP4 blocks of 16 under the outer scale `outer`: block scale codes, element codes, decoded
values. -/
def runNvfp4 (variant : String) (outer : ℚ) (inputs : Array SignedRat) :
    Option String := do
  let n := inputs.size
  let rule ← blockRule n variant
  let format : Block.CodedFormat (Fin n) Nat :=
    Block.nvfp4Stored (fun _ => 0) (fun i => i.val / 16)
  let policy : Block.Policy (Fin n) Nat :=
    if variant == "exact" then Block.nvfp4Supplied (fun i => i.val / 16) fun _ => outer
    else [Block.Selection.supplied fun _ => outer, rule]
  let tensor := format.quantize policy fun i => inputs.getD i.val 0
  let scales := (List.range (n / 16)).map fun block => (tensor.scales.2.1 block).toNat
  let codes := (List.finRange n).map fun i => (tensor.elements i).toNat
  let values := (List.finRange n).map fun i => valueText (tensor.decode i)
  pure s!"{joinNat scales} | {joinNat codes} | {" ".intercalate values}"

/-- Without an outer scale: the outer scale `1`, which binary32 stores exactly. -/
def runNvfp4Single (variant : String) (words : Array Nat) : Option String := do
  runNvfp4 variant 1 (← words.mapM inputValue)

/-- The first word of a line is the outer scale. -/
def runNvfp4Two (variant : String) (words : Array Nat) : Option String := do
  let outer ← inputValue (← words[0]?)
  runNvfp4 variant outer.value (← (words.extract 1 words.size).mapM inputValue)

/-! ## NVFP4 in binary32: the library's working quantizer -/

def word (bits : Nat) : F32 :=
  Model.ofNatBits bits

/-- Blocks of 16 through `Block.nvfp4Working`, the quantizer on binary32 encodings in the order
of torchao's `nvfp4_quantize`. Without an outer scale the outer scale is one. -/
def runNvfp4F32 (twoLevel : Bool) (words : Array Nat) : Option String := do
  let outer : F32 := if twoLevel then word (words.getD 0 0) else Model.posOne _
  let data := (if twoLevel then words.extract 1 words.size else words).map word
  let blocks := (List.range (data.size / 16)).map fun block =>
    (data.extract (16 * block) (16 * block + 16)).toList
  let results := blocks.map (Block.nvfp4Working.block outer)
  let scales := results.map (·.1.toNatBits)
  let codes := results.flatMap fun result => result.2.map (·.toNatBits)
  pure s!"{joinNat scales} | {joinNat codes} |"

/-! ## Element conversion -/

def format? : String → Option FloatFormat
  | "e4m3" => some .e4m3
  | "e5m2" => some .e5m2
  | "e2m1" => some .e2m1
  | "e2m3" => some .e2m3
  | "e3m2" => some .e3m2
  | _ => none

def runCast (format : FloatFormat) (saturate : Bool) (words : Array Nat) :
    Option String := do
  let inputs ← words.mapM inputValue
  let codec := Block.Codec.ofFormat format (saturate := saturate)
  let codes := inputs.toList.map fun value => (codec.encode value).toNatBits
  let values := inputs.toList.map fun value => valueText (codec.decode (codec.encode value))
  pure s!" | {joinNat codes} | {" ".intercalate values}"

/-- Process standard input line by line with `handle`. -/
partial def eachLine (handle : Array Nat → Option String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let rec loop (failures : UInt32) : IO UInt32 := do
    let line ← stdin.getLine
    if line.isEmpty then
      return failures
    match (fields line).toArray.mapM parseHex? with
    | none =>
        IO.println "error: malformed line"
        loop (failures + 1)
    | some words =>
        match handle words with
        | some text =>
            IO.println text
            loop failures
        | none =>
            IO.println "error: unsupported input"
            loop (failures + 1)
  loop 0

/-- Dispatch the block cases. -/
public def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["element", profileName] =>
      match profile? profileName with
      | some profile => eachLine (runElement profile)
      | none => IO.eprintln "unknown profile"; return 2
  | ["mx", profileName, policyName] =>
      match profile? profileName with
      | some profile => eachLine (runMx profile policyName)
      | none => IO.eprintln "unknown profile"; return 2
  | ["dot", leftName, rightName] =>
      match profile? leftName, profile? rightName with
      | some left, some right => eachLine (runDot left right .binary32 .exact)
      | _, _ => IO.eprintln "unknown dot profile"; return 2
  | ["finite-dot", leftName, rightName, productName, accumulatorName, outputName] =>
      match profile? leftName, profile? rightName, binaryFormat? productName,
          binaryFormat? accumulatorName, binaryFormat? outputName with
      | some left, some right, some product, some accumulator, some output =>
          let project value :=
            Model.cast product accumulator (Block.Extended.round product value)
          eachLine (runDot left right output (.binary accumulator project))
      | _, _, _, _, _ => IO.eprintln "unknown finite-dot profile or binary width"; return 2
  | ["nvfp4", "single", variant] => eachLine (runNvfp4Single variant)
  | ["nvfp4", "two", variant] => eachLine (runNvfp4Two variant)
  | ["nvfp4f32", "single"] => eachLine (runNvfp4F32 false)
  | ["nvfp4f32", "two"] => eachLine (runNvfp4F32 true)
  | ["cast", formatName, mode] =>
      match format? formatName with
      | some format => eachLine (runCast format (mode == "saturate"))
      | none => IO.eprintln "unknown format"; return 2
  | _ =>
      IO.eprintln "usage: oracle block {element PROFILE | mx PROFILE POLICY | dot LEFT RIGHT | \
          finite-dot LEFT RIGHT PRODUCT ACCUMULATOR OUTPUT | nvfp4 {single|two} VARIANT | nvfp4f32 \
          {single|two} | cast FORMAT MODE}"
      return 2

end FloatLibTests.Oracle.Block
