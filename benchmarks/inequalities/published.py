"""Read historical results from the pinned projects' own documents.

These timings are transcriptions of the identified artifacts, not measurements
on the current host. Matching a name is recorded separately from a formula audit.
"""
from pathlib import Path
import json
import re

from common import digest


def references(root: Path):
    rows = []
    source = root / "upstream/flyspeck/formal_ineqs/docs/FormalVerifier.tex"
    text = source.read_text()
    section = text.split("Flyspeck inequalities", 1)[1]
    example = root / "upstream/flyspeck/formal_ineqs/examples_flyspeck.hl"
    pattern = re.compile(
        r"^([^&\n]+?)\s*&\s*(\d+)\s*&\s*([\d.]+)\s*&\s*([\d.]+)\s*\\\\",
        re.MULTILINE)
    for match in pattern.finditer(section):
        name = re.sub(r"\\footnotemark\[\d+\]", "", match[1]).strip()
        reduced = name == "TSKAJXY-TADIAMB"
        rows.append({
            "suite": "flyspeck", "program": name,
            "source_file": "formal_ineqs/examples_flyspeck.hl",
            "source_sha256": digest(example),
            "published_system": "HOL Light formal nonlinear verifier",
            "published_document": "Alexey Solovyev, A Tool for Formal Verification of Nonlinear Inequalities",
            "published_artifact": "formal_ineqs/docs/FormalVerifier.tex",
            "published_artifact_sha256": digest(source),
            "published_precision": match[2],
            "published_total_seconds": match[3],
            "published_verification_seconds": match[4],
            "published_match": ("Related polynomial reduction; not an identical input" if reduced else
                                "Named example in the same pinned artifact; no cross-version claim"),
            "published_environment": (
                "Intel Core i5 2.67 GHz; Ubuntu 9.10 in VirtualBox 4.2.0 on Windows 7; "
                "OCaml 3.09.3; arithmetic base 200; caching enabled"),
            "published_time_policy": "Historical artifact timing; no host-normalized speedup",
        })
    source = root / "upstream/metitarski/doc/MetiTarski_User_Guide.tex"
    text = source.read_text()
    pattern = re.compile(r"^%%\{\\tt ([^}]+)\}\s+([\d.]+) seconds;", re.MULTILINE)
    for match in pattern.finditer(text):
        problem = root / "upstream/metitarski/tptp/Problems" / (match[1] + ".tptp")
        if not problem.exists():
            continue
        rows.append({
            "suite": "metitarski", "source_file": "Problems/" + problem.name,
            "source_sha256": digest(problem),
            "published_system": "MetiTarski",
            "published_document": "MetiTarski User Guide (source comments)",
            "published_artifact": "doc/MetiTarski_User_Guide.tex",
            "published_artifact_sha256": digest(source),
            "published_total_seconds": match[2],
            "published_match": "Problem named in the guide's source comment; historical version unspecified",
            "published_environment": "Not identified alongside the source-comment timing",
            "published_time_policy": "Historical source comment, absent from rendered guide; no speedup",
        })
    rows.extend(json.loads((root / "dreal-published.json").read_text())["rows"])
    return rows


def attach(row, references_):
    matches = [reference for reference in references_
               if reference["suite"] == row["suite"]
               and reference.get("source_file") == row["source_file"]
               and reference.get("source_sha256") == row["source_sha256"]
               and reference.get("program", row.get("program")) == row.get("program")]
    if len(matches) > 1:
        raise ValueError("Ambiguous published comparison")
    if matches:
        return {key: value for key, value in matches[0].items() if key.startswith("published_")}
    return {
        "published_match": "No matched per-problem result in the audited pinned artifacts",
        "published_total_seconds": "",
    }


def attach_dreal(row, references_):
    candidates = [reference for reference in references_
                  if reference["published_system"] == "dReal"
                  and reference.get("program") == row.get("program")
                  and reference["suite"] == row["suite"]]
    return {
        "dreal_candidates": candidates,
        "dreal_comparison": (
            "Related named formula only; the paper substitutes 3.14159265 for pi"
            if candidates else
            "No matching per-problem dReal result verified; paper numeric IDs are unmapped"),
        "dreal_speedup": "",
    }
