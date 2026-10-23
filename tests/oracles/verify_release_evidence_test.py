#!/usr/bin/env python3
"""Check the evidence verifier on historical and current summary layouts."""

from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from dataclasses import asdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import verify_release_evidence as evidence
import transcendental_report as report


class SMTNamingTests(unittest.TestCase):
    def summary(self, missing_key: str) -> dict:
        counts = dict.fromkeys(evidence.SMT_COUNT_KEYS, 0)
        counts["generated"] = counts["exact_bit_cases"] = 1
        counts[missing_key] = counts.pop("missing_floatlib")
        return {"counts": counts, "status": "pass", "mismatch_samples": []}

    def test_current_and_historical_counts_normalize_without_mutation(self) -> None:
        expected = self.summary("missing_floatlib")["counts"]
        for key in ("missing_floatlib", "missing_floatlean"):
            with self.subTest(key=key):
                summary = self.summary(key)
                original = copy.deepcopy(summary)
                self.assertEqual(evidence.smt_counts(summary, "fixture"), expected)
                self.assertEqual(summary, original)

    def test_ambiguous_or_unknown_count_keys_fail(self) -> None:
        for key in ("missing_floatlean", "unexpected"):
            with self.subTest(key=key):
                summary = self.summary("missing_floatlib")
                summary["counts"][key] = 0
                with self.assertRaisesRegex(ValueError, "unexpected SMT count keys"):
                    evidence.smt_counts(summary, "fixture")

    def test_historical_missing_result_still_fails(self) -> None:
        summary = self.summary("missing_floatlean")
        summary["counts"]["missing_floatlean"] = 1
        with self.assertRaisesRegex(ValueError, "missing_floatlib is nonzero"):
            evidence.smt_counts(summary, "fixture")

    def check_rows(self, bits_column: str, match: str = "true") -> None:
        text = (
            "id\toperation\tsource\tdestination\trounding\toperands\t"
            f"solver_kind\tsolver_bits\t{bits_column}\tmatch\n"
            f"0\tadd\tf16\tf16\trne\t0000,0000\tzero\t0000\t0000\t{match}\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "results.tsv"
            path.write_text(text)
            evidence.verify_smt_results(path, 1)
            self.assertEqual(path.read_text(), text)

    def test_current_and_historical_result_headers_pass(self) -> None:
        for key in ("floatlib_bits", "floatlean_bits"):
            with self.subTest(key=key):
                self.check_rows(key)

    def test_unknown_header_fails(self) -> None:
        with self.assertRaisesRegex(ValueError, "header"):
            self.check_rows("unexpected_bits")

    def test_historical_mismatch_still_fails(self) -> None:
        with self.assertRaisesRegex(ValueError, "SMT mismatch retained"):
            self.check_rows("floatlean_bits", match="false")


def transcendental_row(
    candidate: str,
    format_name: str,
    operation: str,
    cases: int,
    mode: str | None = "RNDN",
) -> dict:
    """A possible row: one nonfinite mismatch, one pair one ulp apart, the rest exact.
    Without a mode it has the retained campaign's layout, with no zero-sign count."""

    row = {
        "candidate": candidate,
        "format_name": format_name,
        "operation": operation,
        "cases": cases,
        "value_exact": cases - 2,
        "bit_exact": cases - 2,
        "finite_pairs": cases - 1,
        "nonfinite_mismatch": 1,
        "ulp_0": cases - 2,
        "ulp_1": 1,
        "ulp_2_3": 0,
        "ulp_4_15": 0,
        "ulp_16_255": 0,
        "ulp_256_plus": 0,
        "ulp_max": 1,
        "ulp_p50": 0,
        "ulp_p90": 1,
        "ulp_p99": 1,
    }
    if mode is not None:
        row["mode"] = mode
        row["zero_sign_mismatch"] = 0
    return row


OPERATIONS = ("exp", "log", "sin", "cos", "sinh", "cosh", "tanh")
RLIBM_OPERATIONS = ("exp", "log", "sinh", "cosh")


def provider_coverage(rows: list[dict]) -> list[dict]:
    """Complete coverage for the three providers, counted from their rows."""

    coverage = []
    for name in ("CORE-MATH", "OpenLibm", "RLIBM"):
        cases = sum(row["cases"] for row in rows if row["candidate"] == name)
        coverage.append(
            {"name": name, "expected_evaluations": cases, "actual_evaluations": cases}
        )
    return coverage


def observational_summary() -> dict:
    """The layout of the retained campaign: 4,109 cases in 46 rows without modes."""

    groups = [
        (candidate, format_name, operation)
        for candidate in ("FloatLean", "CORE-MATH", "OpenLibm")
        for format_name in ("binary32", "binary64")
        for operation in OPERATIONS
    ] + [("RLIBM", "binary32", operation) for operation in RLIBM_OPERATIONS]
    rows = [transcendental_row(*group, 10, None) for group in groups]
    return {
        "adapter": "transcendental_compare",
        "status": "observational_complete",
        "comparison_kind": "observational",
        "conformance": False,
        "cases": 4109,
        "provider_coverage": provider_coverage(rows),
        "summaries": rows,
    }


GATE_MANIFEST = {
    "emitter": ["transcendentalEmitter"],
    "exhaustive16": ["false"],
    "hard": ["tests/oracles/data/transcendental-hard-cases.tsv"],
    "random-count": ["256"],
    "seed": ["binary32 1"],
    "tier": ["default"],
}

# Cases of the gate fixture: (format, operation, arguments, MPFR, FloatLib, CORE-MATH,
# OpenLibm, RLIBM), with None where a provider has no function. Two FloatLib results
# are wrong.
GATE_CASES = [
    ("binary32", "exp", [0x3F800000], 0x402DF854, 0x402DF854, 0x402DF854, 0x402DF854,
     0x402DF854),
    ("binary32", "exp", [0x40000000], 0x40EC7326, 0x40EC7327, 0x40EC7326, 0x40EC7326,
     0x40EC7326),
    ("binary32", "sin", [0x3F800000], 0x3F576AA4, 0x3F576AA4, 0x3F576AA4, 0x3F576AA5,
     None),
    ("binary32", "sin", [0x40000000], 0x3F68C7B7, 0x3F68C7B7, 0x3F68C7B7, 0x3F68C7B7,
     None),
    ("binary16", "exp", [0x3C00], 0x4170, 0x4170, None, None, None),
    ("binary32", "pow", [0x40400000, 0x3FC00000], 0x40A646E1, 0x40A646E2, None, None,
     None),
]


def gate_fixture() -> tuple[dict, str, dict]:
    """A gate summary, its details file and its census entry, written by the report."""

    cases = []
    results: dict[str, list] = {
        name: [] for name in ("FloatLib", *report.PROVIDER_SYMBOLS)
    }
    for format_name, operation, arguments, mpfr, *outputs in GATE_CASES:
        fmt = report.CATALOG[format_name]
        identity = report.case_id(operation, "RNDN", fmt, arguments)
        cases.append(report.Case(identity, operation, "RNDN", fmt, tuple(arguments),
                                 outputs[0], None, mpfr, 1))
        for name, output in zip(results, outputs, strict=True):
            results[name].append(output)
    with tempfile.TemporaryDirectory() as directory:
        details = Path(directory) / "details.tsv"
        report.write_details(details, cases, results)
        details_text = details.read_text(encoding="utf-8")
    requests, counts, digest = report.census_counts(cases)
    entry = {
        "case_ids_sha256": digest,
        "corpus_sha256": "0" * 64,
        "manifest": sorted(
            f"{key} {value}"
            for key, values in GATE_MANIFEST.items()
            for value in values
        ),
        "requests": requests,
        "requests_by_operation": counts,
    }
    summary = {
        "adapter": "transcendental_compare",
        "status": "gate_pass",
        "comparison_kind": "known-failure gate",
        "conformance": False,
        "cases": requests,
        "manifest": copy.deepcopy(GATE_MANIFEST),
        "gate": {
            "new_mismatches": 0,
            "changed_known_failures": 0,
            "correctly_rounded_mismatches": 0,
            "stale_known_failures": 0,
            "known_failures_matched": 2,
            "known_failures_not_exercised": 5,
        },
        "coverage": {
            "status": "checked",
            "census": "release",
            "entry": copy.deepcopy(entry),
            "differences": [],
        },
        "rounding_environment": "FE_TONEAREST",
        "providers": [
            {"name": name, "library": f"{name}.so", "sha256": "2" * 64}
            for name in report.PROVIDER_SYMBOLS
        ],
        "provider_coverage": [
            report.provider_coverage(name, set(symbols()), cases, results[name])
            for name, symbols in report.PROVIDER_SYMBOLS.items()
        ],
        "summaries": [asdict(row) for row in report.summarize(cases, results)],
    }
    return json.loads(json.dumps(summary)), details_text, entry


class TranscendentalEvidenceTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.directory = Path(directory.name)
        self.summary, self.details, self.entry = gate_fixture()
        self.census = self.directory / "census.json"
        self.write_census({"release": self.entry})

    def write_census(self, invocations: dict) -> None:
        self.census.write_text(
            json.dumps({"invocations": invocations}), encoding="utf-8"
        )

    def verify(self, summary: dict, details: str | None = None) -> None:
        root = self.directory / "run"
        root.mkdir(exist_ok=True)
        (root / "summary.json").write_text(json.dumps(summary), encoding="utf-8")
        if details is not None:
            (root / "details.tsv").write_text(details, encoding="utf-8")
        elif (root / "details.tsv").exists():
            (root / "details.tsv").unlink()
        evidence.verify_transcendental(root, self.census)

    def check_rejections(self, summary: dict, changes: list[dict],
                         details: str | None = None) -> None:
        self.verify(summary, details)
        for change in changes:
            with self.subTest(change=change):
                with self.assertRaises(ValueError):
                    self.verify({**summary, **change}, details)

    def test_observational_campaign(self) -> None:
        summary = observational_summary()
        rows, providers = summary["summaries"], summary["provider_coverage"]
        self.check_rejections(summary, [
            {"cases": 4108},
            {"status": "gate_pass"},
            {"conformance": True},
            {"summaries": rows[:-1]},
            {"summaries": rows[:-1] + rows[:1]},
            {"comparison_kind": "observation"},
            {"provider_coverage": providers[:-1]},
        ])

    def test_gate_counts_and_coverage(self) -> None:
        summary = self.summary
        gate, coverage = summary["gate"], summary["coverage"]
        unchecked = {**coverage, "status": "unchecked", "census": None, "entry": None}
        counts = self.entry["requests_by_operation"]
        floats = {key: float(count) for key, count in counts.items()}
        floating = {**self.entry, "requests_by_operation": floats}
        self.check_rejections(summary, [
            {"status": "gate_fail"},
            {"conformance": True},
            {"gate": {**gate, "new_mismatches": 1}},
            {"gate": {**gate, "changed_known_failures": 1}},
            {"gate": {**gate, "correctly_rounded_mismatches": 1}},
            {"gate": {**gate, "stale_known_failures": 1}},
            {"gate": {**gate, "stale_known_failures": "0"}},
            {"gate": {**gate, "known_failures_matched": 1}},
            {"gate": {**gate, "known_failures_matched": 7}},
            {"gate": {**gate, "known_failures_matched": "2"}},
            {"gate": {key: value for key, value in gate.items()
                      if key != "known_failures_not_exercised"}},
            {"coverage": unchecked},
            {"coverage": {**coverage, "census": "default"}},
            {"coverage": {**coverage, "differences": ["6 requests, census 7"]}},
            {"coverage": {**coverage, "entry": None}},
            {"coverage": {**coverage, "entry": floating}},
            {"coverage": {**coverage, "entry": {**self.entry, "manifest": []}},
             "manifest": {}},
            {"manifest": {**summary["manifest"], "random-count": ["255"]}},
            {"cases": 5},
        ], self.details)
        self.write_census({"default": self.entry})
        with self.assertRaisesRegex(ValueError, "no entry 'release'"):
            self.verify(summary, self.details)

    def test_rows_and_providers_are_recomputed_from_the_details(self) -> None:
        summary = self.summary
        rows, coverage = summary["summaries"], summary["provider_coverage"]
        floatlib_sin = next(
            index
            for index, row in enumerate(rows)
            if (row["candidate"], row["operation"]) == ("FloatLib", "sin")
        )

        def row_changed(index: int, **fields: object) -> list[dict]:
            return rows[:index] + [{**rows[index], **fields}] + rows[index + 1:]

        # Relabel FloatLib's sin row and drop the provider sin rows and their totals.
        relabeled = [row for row in row_changed(floatlib_sin, mode="RNDU")
                     if row["candidate"] == "FloatLib" or row["operation"] != "sin"]
        lowered = [
            {**record, "expected_evaluations": record["expected_evaluations"] - 2,
             "actual_evaluations": record["actual_evaluations"] - 2}
            if record["name"] in ("CORE-MATH", "OpenLibm") else record
            for record in coverage
        ]
        ghost = {**rows[0], "candidate": "Ghost"}
        core_math_exp = next(
            index
            for index, row in enumerate(rows)
            if (row["candidate"], row["operation"]) == ("CORE-MATH", "exp")
        )
        # CORE-MATH's exp row claiming only nonfinite references, unlike FloatLib's.
        nonfinite = {
            "finite_pairs": 0, "nonfinite_mismatch": 0, "zero_sign_mismatch": 0,
            "ulp_0": 0, "ulp_1": 0, "ulp_max": None, "ulp_p50": None, "ulp_p90": None,
            "ulp_p99": None,
        }
        self.check_rejections(summary, [
            {"summaries": relabeled, "provider_coverage": lowered},
            {"summaries": row_changed(0, ulp_p50=1)},
            {"summaries": row_changed(0, bit_exact=0)},
            {"summaries": row_changed(core_math_exp, **nonfinite)},
            {"summaries": row_changed(0, ulp_1=0, ulp_256_plus=1, ulp_p90=2**32,
                                      ulp_p99=2**32, ulp_max=2**32)},
            {"summaries": rows + [ghost]},
            {"summaries": rows[1:]},
            {"provider_coverage": [{**record, "supported_groups": []}
                                   for record in coverage]},
            {"provider_coverage": coverage[:-1]},
            {"providers": []},
            {"rounding_environment": "not applicable"},
        ], self.details)

    def test_details_must_reproduce_the_census_entry(self) -> None:
        lines = self.details.splitlines(keepends=True)
        header, body = lines[0], lines[1:]
        self.verify(self.summary, self.details)
        # OpenLibm's sin(1), value and distance, as if it had not been evaluated.
        blank_provider = body[2].split("\t")
        blank_provider[5] = blank_provider[9] = ""
        changed_ulp = body[1].split("\t")
        changed_ulp[-4] = "2"
        for details in (
            None,
            header + "".join(body[1:]),
            header + "".join(body[:2]) + "\t".join(blank_provider) + "".join(body[3:]),
            header + body[0] + "\t".join(changed_ulp) + "".join(body[2:]),
            header.replace("RLIBM", "Ghost") + "".join(body),
        ):
            with self.subTest(details=details and details[:60]):
                with self.assertRaises(ValueError):
                    self.verify(self.summary, details)

    def regenerated(self, details: str) -> dict:
        """The summary the report would write for these details."""
        path = self.directory / "regenerated.tsv"
        path.write_text(details, encoding="utf-8")
        cases, results = report.read_details(path)
        return {
            **self.summary,
            "provider_coverage": [
                report.provider_coverage(name, set(symbols()), cases, results[name])
                for name, symbols in report.PROVIDER_SYMBOLS.items()
            ],
            "summaries": [asdict(row) for row in report.summarize(cases, results)],
        }

    def edited(self, edits: dict[tuple[int, int], str]) -> str:
        """The fixture details with cells replaced, `(row, column) -> text`; rows count
        from the first case."""
        lines = self.details.splitlines()
        rows = [line.split("\t") for line in lines[1:]]
        for (row, column), text in edits.items():
            rows[row][column] = text
        return "\n".join([lines[0], *("\t".join(row) for row in rows)]) + "\n"

    def test_details_cannot_misplace_results(self) -> None:
        # Columns: case, MPFR, ternary, FloatLib, CORE-MATH, OpenLibm, RLIBM, then the
        # ULP distances in the same order. Rows: exp(1), exp(2), sin(1), sin(2),
        # binary16 exp(1), pow(3, 1.5).
        no_floatlib = self.edited(
            {(row, column): "" for row in range(6) for column in (3, 7)}
        )
        with self.assertRaisesRegex(ValueError, "no FloatLib result"):
            self.verify(self.summary, no_floatlib)
        # CORE-MATH's sin(1) moved to a binary16 case it does not support; totals agree.
        moved = self.edited({(2, 4): "", (2, 8): "", (4, 4): "0x4170", (4, 8): "0"})
        with self.assertRaisesRegex(ValueError, "exactly when it does not support"):
            self.verify(self.regenerated(moved), moved)
        wide = self.edited({(0, 4): "0x1402df854"})
        with self.assertRaisesRegex(ValueError, "not a binary32 encoding"):
            self.verify(self.summary, wide)
        header = self.details.splitlines()[0].split("\t")
        duplicated = "\t".join(header[:7] + ["RLIBM_bits"] + header[7:] + ["RLIBM_ulp"])
        rows = [line.split("\t") for line in self.details.splitlines()[1:]]
        doubled = "\n".join(
            [duplicated] + ["\t".join(row[:7] + [""] + row[7:] + [""]) for row in rows]
        ) + "\n"
        with self.assertRaisesRegex(ValueError, "unexpected details header"):
            self.verify(self.summary, doubled)

    def test_summary_json_and_manifest_shape(self) -> None:
        summary = self.summary
        self.check_rejections(summary, [
            {"manifest": {**summary["manifest"], "random-count": [256]}},
            {"manifest": {**summary["manifest"], "extra": []}},
            {"manifest": {**summary["manifest"], "random-count 256": ["x"]}},
        ], self.details)
        root = self.directory / "run"
        text = json.dumps(summary).replace(
            '"new_mismatches": 0', '"new_mismatches": 99, "new_mismatches": 0'
        )
        self.assertIn('"new_mismatches": 99', text)
        (root / "summary.json").write_text(text, encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "repeats a key"):
            evidence.verify_transcendental(root, self.census)

    def test_release_status_follows_the_summary_kind(self) -> None:
        for summary, status in (
            (observational_summary(), "observational-complete"),
            (self.summary, "qualified-pass"),
        ):
            with self.subTest(status=status):
                release = self.directory / status
                (release / "12-transcendentals").mkdir(parents=True)
                (release / "12-transcendentals" / "summary.json").write_text(
                    json.dumps(summary), encoding="utf-8"
                )
                expected = evidence.expected_release_statuses(release)
                self.assertEqual(expected["12-transcendentals"], status)
                self.assertEqual(
                    {key: value for key, value in expected.items()
                     if key != "12-transcendentals"},
                    evidence.RELEASE_STATUSES,
                )


if __name__ == "__main__":
    unittest.main()
