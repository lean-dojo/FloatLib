"""Semantic regression tests for the untrusted translators and proof-result gate."""
import io
import json
import sys
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parent / name)
               for name in ("fpbench", "inequalities", "correct-rounding")]
from sexpr import Refusal, number, parse
from translate import Context, Translator, Value, translate
from numeric import RealExpression, source_box
from tools import bound, tool_selection
from contracts import local_contract
from polynomial import polynomial_guard
from compare import compare
from tptp import Parser, goal
from common import prove, write_json
import hol
import lefevre
import historical


class TranslationTests(unittest.TestCase):
    def test_gappa_polynomial_contract(self):
        attrs = {":pre": parse("(<= 0 x 10)")[0]}
        body = parse("(let ([a (* x x)] [b (- x 1)]) (- a b))")[0]
        self.assertEqual(local_contract("gappa", ["x"], attrs, body, "binary32")
                         ["comparison_contract"], "compatible_stored_inputs")
        # The parallel binding y must see the original x, not the new x = 1.
        parallel = parse("(let ([x 1] [y x]) (* y y))")[0]
        self.assertEqual(polynomial_guard(["x"], attrs, parallel, "binary32"), 400)
        for bad in (
                ["+", "x", "0.1"],
                ["let*", [["y", "x"]], "y"],
                ["let", [["y", "1"], ["y", "2"]], "y"],
                ["*", "x", str((1 << 24) + 1)]):
            self.assertEqual(local_contract("gappa", ["x"], attrs, bad, "binary32")
                             ["comparison_contract"], "unmatched")
        fractional_box = {":pre": parse("(<= 0.1 x 10)")[0]}
        self.assertEqual(local_contract("gappa", ["x"], fractional_box, body, "binary32")
                         ["comparison_contract"], "unmatched")
        large = "x"
        for _ in range(6):
            large = ["*", large, large]
        self.assertEqual(local_contract("gappa", ["x"], attrs, large, "binary32")
                         ["comparison_contract"], "unmatched")
        self.assertEqual(local_contract("gappa", ["x"], attrs, large, "binary64")
                         ["comparison_contract"], "compatible_stored_inputs")

    def test_cli_tool_selection(self):
        self.assertEqual(tool_selection("gappa,daisy"), {"gappa", "daisy"})
        self.assertEqual(len(tool_selection("")), 6)
        with self.assertRaises(ValueError):
            tool_selection("gapa")

    def test_published_canonical_contract(self):
        historical.tests()

    def test_published_comparison_requires_source_hash_and_proof(self):
        identity = {"source_file": "test.fpcore", "index": "0",
                    "default_precision": "binary64"}
        proofs = [{**identity, "method": "forward", "numeric_status": "proved",
                   "numeric_bound": "1/8", "source_sha256": "source-hash"}]
        audits = [{**identity, "status": "compatible_stored_inputs",
                   "source_sha256": "source-hash", "reference_bound": "1/16",
                   "reference_input": "test.txt", "reference_revision": "revision",
                   "reference_elapsed_seconds": "1", "reference_time_policy": "historical"}]
        result = compare(proofs, [], audits)[0]
        self.assertEqual(json.loads(result["forward_fptaylor_published_ratios"])[0]
                         ["bound_ratio"], "2")
        audits[0]["source_sha256"] = "different"
        self.assertEqual(compare(proofs, [], audits)[0]["forward_fptaylor_published_ratios"], "[]")
        audits[0]["source_sha256"] = "source-hash"
        proofs[0]["numeric_status"] = "refused"
        self.assertEqual(compare(proofs, [], audits)[0]["forward_fptaylor_published_ratios"], "[]")

    def test_comparison_requires_proof_and_contract(self):
        identity = {"source_file": "test.fpcore", "index": "0",
                    "default_precision": "binary64"}
        proofs = [{**identity, "method": "forward", "numeric_status": "proved",
                   "numeric_bound": "1/8", "source_sha256": "source-hash"}]
        tools = [{**identity, "tool": "fptaylor", "status": "bounded",
                  "numeric_bound": "1/16", "source_sha256": "source-hash",
                  "comparison_contract": "compatible_stored_inputs"}]
        result = compare(proofs, tools)[0]
        self.assertEqual(result["forward_fptaylor_bound_ratio"], "2")
        self.assertEqual(result["closed_fptaylor_bound_ratio"], "")
        tools[0]["source_sha256"] = "different"
        self.assertEqual(compare(proofs, tools)[0]["forward_fptaylor_bound_ratio"], "")
        tools[0]["source_sha256"] = "source-hash"
        tools[0]["comparison_contract"] = "unmatched"
        self.assertEqual(compare(proofs, tools)[0]["forward_fptaylor_bound_ratio"], "")
        proofs[0]["numeric_status"] = "refused"
        self.assertEqual(compare(proofs, tools)[0]["numerical_coverage"], "other_tool_only")

    def test_comparison_contracts(self):
        closed = {":pre": parse("(<= 0 x 10)")[0]}
        term = parse("(/ x (+ x 1))")[0]
        self.assertEqual(local_contract("fptaylor", ["x"], closed, term, "binary64")
                         ["comparison_contract"], "compatible_stored_inputs")
        for properties in [
                {":pre": parse("(< 0 x 10)")[0]},
                {":pre": closed[":pre"], ":round": "nearestAway"},
                {":pre": parse("(and (<= 0 x 10) (<= (* x x) 5))")[0]}]:
            self.assertEqual(local_contract("fptaylor", ["x"], properties, term, "binary64")
                             ["comparison_contract"], "unmatched")
        self.assertEqual(local_contract("fptaylor", ["x"], closed, ["+", "x", "-0.0"],
                                        "binary64")["comparison_contract"], "unmatched")
        self.assertEqual(local_contract("gappa", ["x"], closed, term, "binary64")
                         ["comparison_contract"], "unmatched")

    def test_cli_bounds(self):
        value, kind = bound("gappa",
                            "Results:\n |x - Mx| in [0, 231283890598702579b-73 {2.44882e-05}]")
        self.assertEqual(Fraction(value), Fraction(231283890598702579) * Fraction(2) ** -73)
        self.assertEqual(kind, "absolute_error")
        value, _ = bound("fptaylor", "Absolute error (exact): 2.0e-3 (0x1p-9)")
        self.assertEqual(Fraction(value), Fraction(1, 512))
        self.assertEqual(bound("gappa", "no proved enclosure"), ("", ""))

    def test_exact_literals(self):
        self.assertEqual(number("0.1"), Fraction(1, 10))
        self.assertEqual(number("-0x1.8p-2"), Fraction(-3, 8))
        self.assertEqual(number("2e-30"), Fraction(2, 10**30))
        with self.assertRaises(Refusal):
            parse("(+ 1 2]")

    def test_scoped_rounding(self):
        translated = translate(["x"], {}, parse("(! :round toPositive (+ x 0.1))")[0],
                               "binary32", "forward", "directed")
        command = translated["commands"][0]
        self.assertIn("Model.add", command)
        self.assertEqual(command.count(".up"), 2)
        self.assertIn("(1 / 10 : ℚ)", command)

    def test_parallel_let(self):
        t = Translator()
        expr = parse("(let ([x 1] [y x]) (+ x y))")[0]
        output = t.expr(expr, {"x": Value("outer", "binary32")}, Context("binary32"))
        self.assertIn("let v2 := outer", output.lean)
        t = Translator()
        expr = parse("(let* ([x 1] [y x]) (+ x y))")[0]
        output = t.expr(expr, {"x": Value("outer", "binary32")}, Context("binary32"))
        self.assertIn("let v2 := v1", output.lean)

    def test_no_implicit_narrowing(self):
        with self.assertRaises(Refusal):
            Translator().expr(parse("(! :precision binary32 (+ x 1))")[0],
                              {"x": Value("wide", "binary64")}, Context("binary64"))
        with self.assertRaises(Refusal):
            Context("binary64").annotated({":precision": ["float", "8", "32"]})

    def test_annotation_overrides_default(self):
        row = translate(["x"], {":precision": "binary64"}, ["+", "x", "1"],
                        "binary32", "forward", "annotation")
        self.assertEqual(row["effective_precision"], "binary64")

    def test_signed_zero(self):
        zero = Translator().expr("-0.0", {}, Context("binary32"))
        self.assertIn("zero true", zero.lean)
        ordinary = Translator().expr("0.0", {}, Context("binary32"))
        self.assertNotIn("zero ", ordinary.lean)

    def test_chained_comparison(self):
        condition = Translator().boolean(
            ["<", "x", "y", "z"],
            {name: Value(name, "binary64") for name in ["x", "y", "z"]},
            Context("binary64"))
        self.assertEqual(condition.count("Model.compare"), 2)
        self.assertIn(" ∧ ", condition)

    def test_source_domain(self):
        box = source_box(parse("(and (< -1 x 2) (<= 0 y 3))")[0], ["x", "y"])
        self.assertEqual(box, {"x": [Fraction(-1), Fraction(2)],
                               "y": [Fraction(0), Fraction(3)]})
        with self.assertRaises(Refusal):
            source_box(parse("(or (< -1 x 2) (< 5 x 6))")[0], ["x"])
        text = RealExpression().expr(parse("(let ([x 1] [y x]) (+ x y))")[0],
                                     {"x": "outer"})
        self.assertIn("let r1 : ℝ := outer", text)

    def test_tptp_structure(self):
        forms, includes = Parser(
            "fof(test,conjecture, ![X] : ((X > 0 & X < 1) => exp(X) > 1))."
        ).file()
        text = goal(forms[0][2])
        self.assertIn("∀", text)
        self.assertIn("→", text)
        self.assertIn("Real.exp", text)
        self.assertEqual(includes, [])
        with self.assertRaises(Refusal):
            goal(Parser("fof(test,conjecture,mystery(1)>0).").file()[0][0][2])

    def test_hol_domains_and_shadowing(self):
        text = hol.Translator({}).goal("ineq [(&0,x,&1)] (x pow 2 <= &1)")
        self.assertIn("0 / 1 : ℝ) ≤ x", text)
        self.assertIn("x ≤ (1 / 1 : ℝ)", text)
        self.assertIn("∀ (x : ℝ)", text)
        defs = {"x": ([], ("atom", "7"), "test", 0)}
        text = hol.Translator(defs).goal("!x. ?x. x > &0")
        self.assertIn("∀ (v0 : ℝ)", text)
        self.assertIn("∃ (v1 : ℝ)", text)
        self.assertIn("v1 >", text)
        with self.assertRaises(Refusal):
            hol.Translator({"c": None}).goal("c > &0")

    def test_hol_capture(self):
        with self.assertRaises(Refusal):
            hol.substitute(("!", ["x"], ("atom", "y")), {"y": ("atom", "x")})
        with self.assertRaises(Refusal):
            hol.Translator({}).goal("(@x. x pow 2 = &2) > &0")

    def test_hol_natural_coercions(self):
        # 1 - 2 is zero in the naturals; interpreting it over the reals is unsound.
        for source in ("&(1 - 2) = &0", "!x. &x >= &0", "&(1 / 2) = &0"):
            with self.assertRaises(Refusal):
                hol.Translator({}).goal(source)
        self.assertIn("(12 / 1 : ℝ)", hol.Translator({}).goal("&12 > &0"))

    def test_hol_tuple_let(self):
        text = hol.Translator({}).goal(
            "ineq [&0,x,&1] (let (a,b) = (x,&2) in a + b > &0)")
        self.assertIn("let v0 : ℝ := x", text)
        self.assertIn("let v1 : ℝ := (2 / 1 : ℝ)", text)
        self.assertIn("(v0 + v1)", text)
        with self.assertRaises(Refusal):
            hol.bind_pattern(("tuple", [("atom", "x"), ("atom", "x")]),
                             ("tuple", [("atom", "1"), ("atom", "2")]))

    def test_published_binary_inputs(self):
        self.assertEqual(lefevre.binary_bits("1." + "0" * 52 + "E0", 64),
                         0x3ff0000000000000)
        self.assertEqual(lefevre.binary_bits("-0." + "0" * 23 + "E0", 32), 0x80000000)
        with self.assertRaises(ValueError):
            lefevre.binary_bits("1." + "0" * 52 + "1E0", 64)

    def test_unrepresentable_published_output_refuses_whole_case(self):
        argument = "1." + "0" * 52 + "E0"
        expected = "1." + "0" * 52 + "E-1075"
        record = f"N exp {argument} {expected} 0\n"
        with patch.object(lefevre, "fetch", return_value=Path(".")), \
                patch.object(lefevre.lzma, "open",
                             side_effect=lambda *args, **kwargs: io.StringIO(record)):
            _, rows = lefevre.cases(1)
        self.assertEqual(len(rows), 2)
        for row in rows:
            self.assertEqual(row["status"], "translation_refusal")
            self.assertNotIn("bits", row)
            self.assertNotIn("published_expected", row)


def main():
    tests = unittest.defaultTestLoader.loadTestsFromTestCase(TranslationTests)
    result = unittest.TextTestRunner(verbosity=2).run(tests)
    if not result.wasSuccessful():
        raise SystemExit(1)
    output = Path(sys.argv[1])
    cases = [
        {"id": "valid", "declaration": "gate_valid", "commands": [
            "theorem gate_valid : (1 : ℝ) < 2 := by interval"]},
        {"id": "invalid", "declaration": "gate_invalid", "commands": [
            "theorem gate_invalid : (1 : ℝ) = 2 := by interval"]},
        {"id": "isolated", "declaration": "gate_valid", "commands": [
            "theorem gate_valid : (2 : ℝ) < 3 := by interval"]},
    ]
    rows = prove(cases, output / "proofs")
    write_json(output / "gate.json", rows)
    assert [r["status"] for r in rows] == ["proved", "refused", "proved"], rows
    expressions = [
        ("add", ["+", "x", "1"], {}),
        ("directed", parse("(! :round toPositive (+ x 0.1))")[0], {}),
        ("mixed", parse(
            "(cast (! :precision binary64 (/ x (! :precision binary32 (+ x 1)))))"
        )[0], {":precision": "binary32"}),
    ]
    cases = []
    for name, body, attrs in expressions:
        generated = translate(["x"], attrs, body, "binary32", "forward", name)
        term = generated["commands"][0].split(" := ", 1)[1]
        declaration = "elaborated_" + name
        cases.append({
            "id": name, "declaration": declaration,
            "commands": [
                f"noncomputable def expression_{name} := {term}",
                f"theorem {declaration} : True := True.intro",
            ],
        })
    rows = prove(cases, output / "expressions", batch_size=1)
    write_json(output / "expressions.json", rows)
    assert all(row["status"] == "proved" for row in rows), rows


if __name__ == "__main__":
    main()
