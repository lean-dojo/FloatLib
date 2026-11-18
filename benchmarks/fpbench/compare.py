"""Join local suite rows into one figure-ready record per FPCore specialization."""
from __future__ import annotations

import argparse
import csv
import json
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import write_csv

METHODS = ("forward", "closed", "backward")
TOOLS = ("fptaylor", "gappa", "daisy", "satire", "sollya", "smtlib")


def read(path):
    with path.open() as stream:
        return list(csv.DictReader(stream))


def key(row):
    return row["source_file"], row["index"], row["default_precision"]


def compare(proofs, tools, audits=()):
    lean = {(key(row), row["method"]): row for row in proofs}
    external = {(key(row), row["tool"]): row for row in tools}
    keys = list(dict.fromkeys([key(row) for row in proofs] + [key(row) for row in tools]))
    results = []
    for identity in keys:
        row = dict(zip(("source_file", "index", "default_precision"), identity))
        first = next((lean[identity, method] for method in METHODS
                      if (identity, method) in lean), {})
        row["program"] = first.get("program", "")
        row["source_sha256"] = first.get("source_sha256", "")
        row["effective_precision"] = first.get("effective_precision", "")
        for method in METHODS:
            result = lean.get((identity, method), {})
            for field in ("status", "reason", "numeric_status", "numeric_bound",
                          "numeric_bound_reason", "elapsed_ns", "numeric_elapsed_ns",
                          "process_elapsed_seconds", "numeric_process_elapsed_seconds",
                          "floatlib_commit", "tracked_diff_sha256", "measurement_utc"):
                row[method + "_" + field] = result.get(field, "")
        candidates = [record for record in audits if key(record) == identity]
        row["fptaylor_published_contracts"] = json.dumps(candidates, sort_keys=True)
        for method in METHODS:
            ratios = []
            proof = lean.get((identity, method), {})
            if proof.get("numeric_status") == "proved":
                for record in candidates:
                    if (record.get("status") != "compatible_stored_inputs"
                            or not proof.get("source_sha256")
                            or record.get("source_sha256") != proof["source_sha256"]):
                        continue
                    denominator = Fraction(record["reference_bound"])
                    if denominator > 0:
                        ratios.append({
                            "reference_input": record["reference_input"],
                            "reference_revision": record["reference_revision"],
                            "reference_bound": record["reference_bound"],
                            "bound_ratio": str(Fraction(proof["numeric_bound"]) / denominator),
                            "reference_elapsed_seconds": record["reference_elapsed_seconds"],
                            "time_policy": record["reference_time_policy"],
                        })
            row[method + "_fptaylor_published_ratios"] = json.dumps(ratios, sort_keys=True)
        lean_bound = any(row[method + "_numeric_status"] == "proved" for method in METHODS)
        local_bound = False
        for tool in TOOLS:
            result = external.get((identity, tool), {})
            for field in ("status", "reason", "numeric_bound", "bound_kind", "elapsed_seconds",
                          "export_seconds", "comparison_contract", "comparison_reason",
                          "tool_version", "tool_revision", "floatlib_commit",
                          "tracked_diff_sha256", "source_sha256", "input_sha256", "export_sha256"):
                row[tool + "_" + field] = result.get(field, "")
            bounded = result.get("status") == "bounded"
            local_bound |= bounded
            for method in METHODS:
                ratio, reason = "", ""
                if row[method + "_numeric_status"] != "proved":
                    reason = "No source-domain numerical Lean bound"
                elif not bounded:
                    reason = "No local tool bound"
                elif (not lean.get((identity, method), {}).get("source_sha256")
                      or result.get("source_sha256") !=
                      lean[identity, method]["source_sha256"]):
                    reason = "Source hashes are absent or differ"
                elif result.get("comparison_contract") != "compatible_stored_inputs":
                    reason = result.get("comparison_reason", "Contract not audited")
                else:
                    denominator = Fraction(result["numeric_bound"])
                    if denominator <= 0:
                        reason = "Reference bound is nonpositive"
                    else:
                        ratio = str(Fraction(row[method + "_numeric_bound"]) / denominator)
                        reason = "Lean bound / local tool bound; lower is tighter"
                row[f"{method}_{tool}_bound_ratio"] = ratio
                row[f"{method}_{tool}_ratio_reason"] = reason
            if tool in ("fptaylor", "gappa", "daisy", "satire"):
                for field in ("published_candidates", "published_ratio", "published_comparison"):
                    row[tool + "_" + field] = first.get(tool + "_" + field, "")
        row["numerical_coverage"] = (
            "both" if lean_bound and local_bound else
            "lean_only" if lean_bound else "other_tool_only" if local_bound else "neither")
        row["timing_policy"] = (
            "Lean elapsed_ns excludes process startup; numeric closure is an additional proof. "
            "Tool elapsed_seconds includes process startup; export_seconds is separate.")
        results.append(row)
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proof_results", type=Path)
    parser.add_argument("tool_results", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    audit_path = args.proof_results.parent / "published-contracts.csv"
    audits = read(audit_path) if audit_path.is_file() else []
    write_csv(args.output, compare(read(args.proof_results), read(args.tool_results), audits))
