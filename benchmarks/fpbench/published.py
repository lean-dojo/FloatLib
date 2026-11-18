"""Transcribe pinned reference artifacts without equating benchmark names with contracts."""
from __future__ import annotations

import csv
import json
import re
from fractions import Fraction
from pathlib import Path

from common import digest


def normalized(name):
    return re.sub(r"[^a-z0-9]", "", name.lower())


def references(root: Path):
    """Return historical bounds with their precise artifact and configuration."""
    artifact = root / "published-papers.json"
    rows = json.loads(artifact.read_text())["rows"] if artifact.exists() else []
    for row in rows:
        row["transcription_sha256"] = digest(artifact)
    project = root / "upstream/fptaylor"
    artifact = project / "tests/core/_tests.yml"
    manifest = json.loads((root / "fptaylor-source.json").read_text())
    current = None
    # This deliberately accepts only the flat, one-expression records in this
    # pinned artifact. A changed schema requires an explicit parser update.
    for line in artifact.read_text().splitlines():
        if line.startswith("- name: "):
            current = {"input_file": line.split(": ", 1)[1].strip(), "expressions": []}
        elif current is not None and line.startswith("  - name: "):
            if current["expressions"]:
                raise ValueError("Multiple expressions in FPTaylor reference record")
            current["expressions"].append(line.split(": ", 1)[1].strip())
        elif current is not None and re.match(r"    (upper-bound|exact-value|time):", line):
            key, value = line.strip().split(": ", 1)
            current[key] = value.strip("'\"")
            if key != "time":
                continue
            source = project / "tests/core" / current["input_file"]
            rows.append({
                "tool": "fptaylor", "program": current["expressions"][0],
                "tool_revision": manifest["revision"],
                "artifact": "tests/core/_tests.yml", "artifact_sha256": digest(artifact),
                "input_file": "tests/core/" + current["input_file"],
                "input_sha256": digest(source),
                "configuration": "tests/core/_tests.cfg",
                "configuration_sha256": digest(project / "tests/core/_tests.cfg"),
                "numeric_bound": str(Fraction.from_float(float.fromhex(current["exact-value"]))),
                "displayed_bound": current["upper-bound"],
                "exact_hex_bound": current["exact-value"],
                "elapsed_seconds": current["time"],
                "precision": "binary64", "rounding": "nearestEven",
                "provenance_kind": "published project regression artifact",
                "time_policy": "Historical artifact time; hardware and run date unspecified",
                "contract_status": "Source formulas and domains require comparison before ratios",
            })
    project = root / "upstream/daisy"
    artifact = project / "regression/reference/dataflow_IA_AA_results.csv"
    manifest = json.loads((root / "daisy-source.json").read_text())
    with artifact.open() as stream:
        for record in csv.DictReader(stream, delimiter=";"):
            record = {key.strip(): value.strip() for key, value in record.items()}
            if not record["Absolute error"]:
                continue
            rows.append({
                "tool": "daisy", "program": record["Function name"],
                "tool_revision": manifest["revision"],
                "artifact": "regression/reference/dataflow_IA_AA_results.csv",
                "artifact_sha256": digest(artifact),
                "input_file": "regression/testcases/allTests_dataflow.scala",
                "input_sha256": digest(project / "regression/testcases/allTests_dataflow.scala"),
                "configuration": "dataflow; interval ranges; affine errors",
                "numeric_bound": str(Fraction(record["Absolute error"])),
                "displayed_bound": record["Absolute error"],
                "elapsed_seconds": str(Fraction(record["Time"]) / 1000),
                "original_time": record["Time"], "original_time_unit": "milliseconds",
                "time_unit_evidence": "src/main/scala/daisy/utils/Timer.scala",
                "time_unit_evidence_sha256": digest(project / "src/main/scala/daisy/utils/Timer.scala"),
                "precision": "binary64", "rounding": "nearestEven",
                "provenance_kind": "published project regression artifact",
                "time_policy": "Historical artifact time; hardware and run date unspecified",
                "contract_status": "Source formulas, input errors and domains require comparison before ratios",
            })
    return rows


ALIASES = {
    "introexample": ("tdivt1", "introexample"),
    "carthesiantopolarradius": ("carthesiantopolarradius",),
}


def attach(row, references_):
    """Attach candidate references, explicitly withholding unaudited ratios."""
    key = normalized(row["program"])
    keys = ALIASES.get(key, (key,))
    result = {}
    for tool in ("fptaylor", "daisy", "satire", "gappa"):
        candidates = [reference for reference in references_
                      if reference["tool"] == tool and normalized(reference["program"]) in keys]
        result[tool + "_published_candidates"] = candidates
        result[tool + "_published_ratio"] = ""
        result[tool + "_published_comparison"] = (
            "Named candidate; no ratio without matching the formula, domain, precision and input convention"
            if candidates else "No matching per-program bound found in the audited pinned artifacts")
    return result
