"""Conservative real interpretations of MetiTarski and Flyspeck source formulas."""
from __future__ import annotations
import hashlib
import json
import os
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "suites"))
from common import digest, merge_csv, prove, provenance, selected, write_csv, write_json
from fetch import fetch
from sexpr import Refusal
import tptp
import hol
import published
from capabilities import evidence, probe


def metitarski():
    manifest = json.loads((HERE / "metitarski-source.json").read_text())
    root = HERE / "upstream/metitarski/tptp"
    for path in sorted((root / "Problems").rglob("*")):
        if path.suffix not in (".tptp", ".p"):
            continue
        row = {"suite": "metitarski", "source_file": str(path.relative_to(root)),
               "source_revision": manifest["revision"], "source_sha256": digest(path),
               "input_scope": "conjecture under standard real interpretation",
               "id": "metitarski:" + str(path.relative_to(root))}
        try:
            forms, includes = tptp.Parser(path.read_text()).file()
            targets = [item for item in forms if item[1] == "conjecture"]
            if not targets:
                raise Refusal("No FOF conjecture; clause sets are not reinterpreted as goals")
            row["included_axiom_files"] = includes
            row["nonconjecture_forms"] = sum(item[1] != "conjecture" for item in forms)
            row["premise_policy"] = (
                "Prove the conjecture directly; do not assume supplied analytic axioms")
            for name, _, node in targets:
                result = {**row, "id": row["id"] + ":" + name, "program": name}
                try:
                    result["goal"] = tptp.goal(node)
                except Refusal as error:
                    result.update(status="translation_refusal", reason=str(error))
                yield result
        except (Refusal, UnicodeError, ValueError, RecursionError) as error:
            row.update(status="translation_refusal", reason=str(error))
            yield row


def flyspeck():
    manifest = json.loads((HERE / "flyspeck-source.json").read_text())
    root = HERE / "upstream/flyspeck/text_formalization"
    paths = [root / "general/sphere.hl", root / "general/definitions.hl",
             root / "nonlinear/nonlin_def.hl", root / "nonlinear/ineq.hl"]
    defs = hol.definitions(paths)
    path = root / "nonlinear/ineq.hl"
    for name, term, source_status, offset in hol.records(path):
        row = {
            "id": f"flyspeck:{offset}:{name}", "suite": "flyspeck", "program": name,
            "source_file": str(path.relative_to(root)), "source_revision": manifest["revision"],
            "source_sha256": digest(path), "source_record_status": source_status,
            "input_scope": "quoted inequality record; OCaml generation is not executed",
            "source_offset": offset,
        }
        try:
            if term is None:
                raise Refusal("OCaml-generated inequality has no single quoted source term")
            if source_status in ("skipped", "deprecated"):
                raise Refusal(f"Source marks this record {source_status}")
            translator = hol.Translator(defs)
            row["goal"] = translator.goal(term)
            row["unfolded_definitions"] = sorted(translator.used)
        except (Refusal, RecursionError) as error:
            row.update(status="translation_refusal", reason=str(error))
        yield row


def flyspeck_examples():
    manifest = json.loads((HERE / "flyspeck-source.json").read_text())
    root = HERE / "upstream/flyspeck"
    path = root / "formal_ineqs/examples_flyspeck.hl"
    definitions = hol.definitions([path])
    for name, term, source_status, offset in hol.examples(path):
        row = {
            "id": f"flyspeck-example:{offset}:{name}", "suite": "flyspeck",
            "program": name, "source_file": str(path.relative_to(root)),
            "source_revision": manifest["revision"], "source_sha256": digest(path),
            "source_record_status": source_status, "source_offset": offset,
            "input_scope": "official formal verifier example, using its local definitions",
        }
        try:
            if term is None:
                raise Refusal("Example is not a single quoted source term")
            translator = hol.Translator(definitions)
            row["goal"] = translator.goal(term)
            row["unfolded_definitions"] = sorted(translator.used)
        except (Refusal, RecursionError) as error:
            row.update(status="translation_refusal", reason=str(error))
        yield row


CONSTRAINTS = "FloatLib.Tactic.Interval.Constraints"


def run(output):
    fetch(HERE / "metitarski-source.json")
    fetch(HERE / "flyspeck-source.json")
    source_rows = [*metitarski(), *flyspeck(), *flyspeck_examples()]
    references = published.references(HERE)
    write_json(output / "published.json", references)
    constraint = probe(output / "capabilities", ["interval-constraint-route"])[
        "interval-constraint-route"]
    cases, metadata = [], []
    for row in source_rows:
        row.update(published.attach(row, references))
        row.update(published.attach_dreal(row, references))
        for method in ("interval", "constraint"):
            entry = {**row, "id": row["id"] + ":" + method, "method": method}
            if method == "constraint":
                entry.update(evidence(constraint))
            if method == "constraint" and constraint["status"] != "proved":
                entry.update(
                    status="capability_refusal" if constraint["status"] == "refused"
                    else "capability_probe_failure",
                    reason=f"`interval` with {CONSTRAINTS} imported did not pass "
                    "its compiler probe; see capability_probe_reason")
            elif "goal" in row:
                declaration = "case_" + hashlib.sha256(entry["id"].encode()).hexdigest()[:20]
                cases.append({
                    "id": entry["id"], "declaration": declaration, "method": method,
                    "commands": [
                        "set_option maxHeartbeats 400000 in\n"
                        f"theorem {declaration} : {row['goal']} := by\n"
                        "  intros\n"
                        "  interval"
                    ],
                })
            metadata.append(entry)
    write_json(output / "provenance.json", {
        **provenance(),
        "routes": {
            "interval": "`interval` with the imports of Proofs.lean: boxes and coefficients",
            "constraint": f"the same goals and tactic with {CONSTRAINTS} imported as well, "
                          "which is `interval` as `import FloatLib` provides it",
        }})
    write_json(output / "inventory.json", metadata)
    write_json(output / "plan.json", cases)
    chosen = selected(cases)
    batch = int(os.environ.get("FLOATLIB_SUITE_BATCH", "8"))
    timeout = int(os.environ.get("FLOATLIB_SUITE_TIMEOUT", "45"))
    results = prove([case for case in chosen if case["method"] == "interval"],
                    output / "proofs", batch_size=batch, timeout=timeout)
    results += prove([case for case in chosen if case["method"] == "constraint"],
                     output / "constraint-proofs", batch_size=batch, timeout=timeout,
                     imports=(CONSTRAINTS,))
    by_id = {row["id"]: row for row in results}
    for row in metadata:
        row.update(by_id.get(row["id"], {}))
        row.setdefault("status", "not_run")
        row.setdefault("reason", "" if row["status"] == "proved" else "Outside the selected proof range")
    merge_csv(output / "results.csv", metadata)
    return metadata


if __name__ == "__main__":
    run(Path(sys.argv[1]).resolve())
