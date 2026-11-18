"""Generate a minimal extension of the maintained stream checker; never edit tests."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def generate():
    source = ROOT / "tests/FloatLibTests/Oracle/TestFloat.lean"
    text = source.read_text()
    needle = '  | "near_even" => some .nearest\n'
    if text.count(needle) != 1:
        raise ValueError("Maintained TestFloat rounding parser changed; review the adapter")
    # Keep every arithmetic, comparison, parser and status check byte-for-byte.
    text = text.replace(needle, needle + '  | "near_maxMag" => some .nearestAway\n')
    text = text.replace("FloatLibTests.Oracle.TestFloat", "FloatLibBenchmarks.TestFloatAdapter")
    text = text.replace("open Parsing", "open FloatLibTests.Oracle.Parsing")
    text += ("\npublic def main (args : List String) : IO UInt32 :=\n"
             "  FloatLibBenchmarks.TestFloatAdapter.run args\n")
    output = HERE.parent / "suites/generated"
    output.mkdir(exist_ok=True)
    target = output / "TestFloatAdapter.lean"
    if not target.exists() or target.read_text() != text:
        target.write_text(text)
    (output / "adapter.json").write_text(json.dumps({
        "source": str(source.relative_to(ROOT)),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "generated_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "semantic_change": "Add parser spelling near_maxMag for Model.IEEERoundingMode.nearestAway",
        "other_changes": "Rename namespace, qualify the existing Parsing namespace, add main",
    }, indent=2) + "\n")
    return target


if __name__ == "__main__":
    print(generate())
