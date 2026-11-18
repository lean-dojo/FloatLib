"""Independent OFP8 conversion checks using pinned microxcaling and PyTorch.

microxcaling is called only for finite SAT conversion, which its
saturate_normals option implements. Torch tensors are CPU tensors. No custom
extension is imported or compiled. Binary64 intermediate arithmetic preserves
every source value and avoids unrelated binary32 log2 approximation effects.
"""

import argparse
import csv
import hashlib
import json
from pathlib import Path
import sys
import types

import numpy as np
import torch

from ofp8 import FORMATS, source_value
from gfloat import decode_float


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("observations", type=Path)
    parser.add_argument("microxcaling", type=Path)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    torch.set_num_threads(8)
    torch.set_num_interop_threads(1)
    # Load the two upstream reference modules without importing unrelated layers.
    package = types.ModuleType("mx")
    package.__path__ = [str(args.microxcaling / "mx")]
    sys.modules["mx"] = package
    from mx.elemwise_ops import _quantize_elemwise

    rows = []
    with args.observations.open(newline="") as stream:
        for row in csv.reader(stream):
            if row[0] != "decode":
                rows.append(row)
    inputs = np.array([source_value(row[0], int(row[1])) for row in rows], dtype=np.float64)
    codes = np.array([[int(word) for word in row[2:]] for row in rows], dtype=np.uint8)
    finite = np.isfinite(inputs)
    summaries = []
    first = []
    unexplained = 0
    for destination, (name, fmt) in enumerate(FORMATS.items()):
        table = np.array([decode_float(fmt, code).fval for code in range(256)])
        actual = table[codes[:, 2 * destination]]
        reference = _quantize_elemwise(torch.tensor(inputs[finite], dtype=torch.float64, device="cpu"),
                                       "fp8_" + name, round="even", custom_cuda=False,
                                       saturate_normals=True, allow_denorm=True).numpy()
        expected = actual[finite]
        equal = (expected == reference) & ((expected != 0) | (np.signbit(expected) == np.signbit(reference)))
        indices = np.flatnonzero(finite)
        differences = indices[~equal]
        known = 0
        for idx in differences:
            # The known difference: an input negative zero, whose sign OFP8 keeps.
            position = np.searchsorted(indices, idx)
            known_difference = (inputs[idx] == 0 and np.signbit(inputs[idx]) and
                                expected[position] == 0 and np.signbit(expected[position]) and
                                reference[position] == 0 and not np.signbit(reference[position]) and
                                int(codes[idx, 2 * destination]) == 128)
            known += int(known_difference)
            unexplained += int(not known_difference)
            if len(first) < 20:
                first.append({"reference": "microxcaling", "destination": name,
                              "input": rows[idx][:2], "actual_code": int(codes[idx, 2 * destination]),
                              "reference_value": repr(float(reference[np.searchsorted(indices, idx)])),
                              "known_negative_zero_difference": bool(known_difference)})
        summaries.append({"reference": "microxcaling", "destination": name,
                          "mode": "SAT, finite inputs only", "comparisons": int(finite.sum()),
                          "mismatches": len(differences), "known_negative_zero_differences": known})

        dtype = torch.float8_e4m3fn if name == "e4m3" else torch.float8_e5m2
        # The installed header implements SAT for E4M3 and NONSAT for E5M2.
        # The header identity is recorded below; source values are unchanged.
        column = 2 * destination + (0 if name == "e4m3" else 1)
        mode = "SAT" if name == "e4m3" else "NONSAT"
        torch_codes = torch.tensor(inputs, dtype=torch.float32, device="cpu").to(dtype).view(torch.uint8).numpy()
        got = table[codes[:, column]]
        ref_values = table[torch_codes]
        equal = ((np.isnan(got) & np.isnan(ref_values)) |
                 ((got == ref_values) & ((got != 0) | (np.signbit(got) == np.signbit(ref_values)))))
        differences = np.flatnonzero(~equal)
        unexplained += len(differences)
        for idx in differences[:max(0, 20 - len(first))]:
            first.append({"reference": "PyTorch", "destination": name, "input": rows[idx][:2],
                          "actual_code": int(codes[idx, column]),
                          "reference_code": int(torch_codes[idx])})
        summaries.append({"reference": "PyTorch", "destination": name, "mode": mode,
                          "comparisons": len(inputs), "mismatches": len(differences)})
    source = json.loads((args.microxcaling.parent / "microxcaling-source.json").read_text())
    source["elemwise_ops_sha256"] = hashlib.sha256((args.microxcaling / "mx/elemwise_ops.py").read_bytes()).hexdigest()
    header = Path(torch.__file__).parent / "include/torch/headeronly/util/Float8_e4m3fn.h"
    report = {"torch_e4m3_conversion_header_sha256": hashlib.sha256(header.read_bytes()).hexdigest(),
              "torch_git_version": torch.version.git_version,
              "initial_policy_mismatches": {"E4M3_cast_compared_to_NONSAT": 46940,
                  "resolution": "Installed fp8e4m3fn_from_fp32_value explicitly saturates finite overflow and infinity; compare against SAT.",
                  "raw_report": "secondary-initial.json"},
              "document": "OCP OFP8 revision 1.0 (2023-12-01), 5.2.1",
              "torch_version": torch.__version__, "microxcaling": source,
              "summaries": summaries, "first_mismatches": first,
              "unexplained_mismatches": unexplained,
              "status": "pass-with-known-difference" if unexplained == 0 else "fail",
              "known_difference": "An input negative zero in the finite saturating conversion: OFP8 requires sign preservation, and FloatLib returns negative zero. Lean's signed-zero regressions cover both destination formats.",
              "limitations": ["microxcaling is checked only for finite SAT inputs; its generic element routine is not an OFP8 special-value conversion API.",
                              "microxcaling uses CPU binary64 intermediate tensors; every source value is exact.",
                              "PyTorch NaN signs and payloads are compared by class."]}
    args.result.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    if unexplained:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
