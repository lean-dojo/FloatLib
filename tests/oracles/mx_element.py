"""Strict gfloat comparison of the proved compiled MX finite converter."""

import argparse
import importlib.metadata
import json
import math
from pathlib import Path
import struct

from gfloat import decode_float, encode_float, formats, round_float

from block_formats import run_oracle
from ofp8 import boundary_words, binary32, word32


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    corpus = {word32(struct.unpack(">e", struct.pack(">H", word))[0])
              for word in range(65536) if word & 0x7C00 != 0x7C00}
    corpus.update(word for word in boundary_words()
                  if math.isfinite(binary32(word)))
    descriptors = {name: getattr(formats, "format_info_ocp_" + name)
                   for name in ("e5m2", "e4m3", "e3m2", "e2m3", "e2m1", "int8")}
    for descriptor in descriptors.values():
        values = sorted({float(decode_float(descriptor, word).fval)
                         for word in range(2**descriptor.bits)
                         if math.isfinite(decode_float(descriptor, word).fval)})
        for value in values + [(a + b) / 2 for a, b in zip(values, values[1:])]:
            code = word32(value)
            corpus.update(word for word in (code - 1, code, code + 1)
                          if 0 <= word < 2**32 and math.isfinite(binary32(word)))
    words = sorted(corpus)
    rows = [words[i:i + 256] for i in range(0, len(words), 256)]
    results = []
    differences = []
    total_bad = 0
    for name, descriptor in descriptors.items():
        actual = run_oracle(args.oracle, ["element", name], rows)
        bad = 0
        for inputs, output in zip(rows, actual, strict=True):
            if output is None or output[0] or output[2] or len(output[1]) != len(inputs):
                raise RuntimeError(f"Malformed element response: {output}")
            for word, code in zip(inputs, output[1], strict=True):
                value = binary32(word)
                expected = encode_float(descriptor, round_float(descriptor, value, sat=True))
                if code != expected:
                    bad += 1
                    if len(differences) < 20:
                        differences.append({"profile": name, "input": word,
                                            "actual": code, "expected": expected})
        results.append({"profile": name, "comparisons": len(words), "mismatches": bad})
        total_bad += bad
    report = {
        "document": "OCP MX v1.0", "clause": "5.3",
        "reference": f"gfloat {importlib.metadata.version('gfloat')}",
        "implementation": "Element.quantizeFinite compiled through its proved csimp bisection",
        "corpus": "Every finite binary16 word plus binary32 exponent strata, every finite "
                  "destination value, every midpoint and adjacent binary32 values",
        "cases": results, "comparisons": len(words) * len(descriptors),
        "mismatches": total_bad, "first_mismatches": differences,
        "status": "pass" if total_bad == 0 else "fail",
        "limitations": ["Finite SAT conversion only; shared-scale selection is not measured.",
                        "Binary32 and rational inputs are not exhaustive."]}
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if total_bad:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
