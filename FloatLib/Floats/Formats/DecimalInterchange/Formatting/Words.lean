/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Basic
public import FloatLib.Floats.Formats.DecimalInterchange.Formatting.PrecisionProof

/-!
# Decimal character conversion for BID and DPD words

The encoding and width select only the source/destination codec. Parsing,
precision rounding, and status handling use the shared datum operations.
Exact output followed by input recovers the canonical word: redundant encodings
are not character-level representation information.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Formatting

/-- An encoded decimal result and the five conversion flags. -/
structure WordOutcome (f : Format) where
  /-- The result encoded in the selected BID or DPD layout. -/
  word : BitVec f.bitWidth
  /-- IEEE exception indicators raised by character conversion. -/
  status : Status := {}
  deriving DecidableEq, Repr

/-- Parse and round once, then encode the valid result as BID or DPD. -/
def parseWord (encoding : Encoding) (f : Format) (mode : RoundingMode) (text : String) :
    WordOutcome f :=
  let result := parse f mode text
  { word := encoding.codec.encode f result.value, status := result.status }

/-- Decode a word and apply the requested decimal output precision. -/
def formatWord (encoding : Encoding) (f : Format) (mode : RoundingMode)
    (precision : Precision) (word : BitVec f.bitWidth) : TextOutcome :=
  format mode precision (encoding.decode f word)

/-- The word parser encodes precisely the datum parser's result, including special fields. -/
theorem decode_parseWord (encoding : Encoding) (f : Format) (mode : RoundingMode)
    (text : String) :
    encoding.decode f (parseWord encoding f mode text).word = (parse f mode text).value :=
  encoding.codec.decode_encode encoding.lawful f _ (parse_valid f mode text)

/-- Encoding introduces no additional flags. -/
@[simp] theorem parseWord_status (encoding : Encoding) (f : Format) (mode : RoundingMode)
    (text : String) :
    (parseWord encoding f mode text).status = (parse f mode text).status := rfl

/-- Exact text roundtrips every word to its canonical representative, in any pair of modes. -/
theorem parseWord_formatWord_exact (encoding : Encoding) (f : Format)
    (outputMode inputMode : RoundingMode) (word : BitVec f.bitWidth) :
    parseWord encoding f inputMode (formatWord encoding f outputMode .exact word).text =
      { word := encoding.canonicalize f word } := by
  simp only [formatWord, format_exact, parseWord,
    parse_formatExact f inputMode _ (encoding.decode_valid f word)]
  rfl

end FloatLib.Floats.Formats.DecimalInterchange.Formatting
