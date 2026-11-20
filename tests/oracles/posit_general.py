"""Posit operations with zero and one exponent bits against SoftPosit.

The Posit Standard (2022) fixes two exponent bits. The kernel operations of FloatLib take the
number of exponent bits as a parameter, and `Posit.General` proves them for every number. This
script compares them, bit for bit, with an implementation that was written for other numbers of
exponent bits: SoftPosit's 8-bit posits have none and its 16-bit posits have one (the 2018
draft of the standard). Its 32-bit posits have two, and they are the source and the destination
of conversions between formats here.

Compared: `add`, `sub`, `mul`, `div`, `lt` and `le` on every pair of 8-bit encodings and on a
seeded sample of pairs of 16-bit encodings with the special encodings among them, `fma` on
samples of triples, `sqrt`, `neg` and `abs` on every encoding of both formats, the conversions
8 to 16, 16 to 8, 16 to 32 and 32 to 16 bits, and the conversions to signed and unsigned
integers of 32 and 64 bits on the encodings where the 2018 draft that SoftPosit follows and
the 2022 standard agree (every encoding but NaR, and for an unsigned integer the encodings
below the sign bit).

It needs the `softposit` package and the `oracle` executable of the test workspace.
"""

import argparse
import json
from pathlib import Path
import random
import subprocess

import softposit as sp


FORMATS = {
    8: (7, 0, sp.posit8, "p8"),
    16: (15, 1, sp.posit16, "p16"),
    32: (31, 2, sp.posit32, "p32"),
}


def call(width, name, *words):
    """The encoding that SoftPosit returns for an operation on encodings."""
    _, _, make, prefix = FORMATS[width]
    operands = [make(bits=word).v for word in words]
    result = getattr(sp, f"{prefix}_{name}")(*operands)
    return int(result) if isinstance(result, bool) else result.v


def reference(width, operation, words):
    make = FORMATS[width][2]
    if operation in ("add", "sub", "mul", "div", "sqrt"):
        return call(width, operation, *words)
    if operation == "fma":
        return call(width, "mulAdd", *words)
    if operation in ("lt", "le"):
        return call(width, operation, *words)
    if operation == "neg":
        return (-make(bits=words[0])).v.v
    if operation == "abs":
        value = make(bits=words[0])
        return (-value).v.v if words[0] >> (width - 1) and not value.isNaR() else words[0]
    raise ValueError(operation)


def convert(source, target, word):
    prefix = FORMATS[source][3]
    make = FORMATS[source][2]
    return getattr(sp, f"{prefix}_to_{FORMATS[target][3]}")(make(bits=word).v).v


def run(oracle, width, lines):
    payload, exponent_bits = FORMATS[width][:2]
    done = subprocess.run([oracle, "posit-general", str(payload), str(exponent_bits)],
                          input="\n".join(lines) + "\n", capture_output=True, text=True)
    if done.returncode:
        raise RuntimeError(f"oracle exited {done.returncode}: {done.stderr[:500]}")
    answers = done.stdout.split()
    if len(answers) != len(lines):
        raise RuntimeError(f"{len(answers)} answers for {len(lines)} requests")
    return [int(answer) for answer in answers]


def special(width):
    top = 1 << (width - 1)
    return [0, 1, 2, top - 2, top - 1, top, top + 1, top + 2, (1 << width) - 2, (1 << width) - 1,
            1 << (width - 2), (1 << (width - 2)) + 1, (1 << (width - 2)) - 1,
            top + (1 << (width - 2)), top + (1 << (width - 2)) + 1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--oracle", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=60000)
    parser.add_argument("--seed", type=int, default=20261119)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    # mulAdd is a * b + c: checked on 2 * 3 + 4, which is 10 and not 14.
    probe = [sp.posit16(value).v.v for value in (2.0, 3.0, 4.0)]
    if call(16, "mulAdd", *probe) != sp.posit16(10.0).v.v:
        raise RuntimeError("Unexpected operand order of SoftPosit's mulAdd")
    cases = []
    for width in (8, 16):
        size = 1 << width
        if width == 8:
            pairs = [(a, b) for a in range(size) for b in range(size)]
        else:
            extremes = special(width)
            pairs = [(a, b) for a in extremes for b in extremes]
            pairs += [(rng.randrange(size), rng.randrange(size)) for _ in range(args.samples)]
            pairs += [(a, rng.randrange(size)) for a in extremes for _ in range(64)]
            pairs += [(rng.randrange(size), b) for b in extremes for _ in range(64)]
        triples = [(a, b, c) for a in special(width) for b in special(width)
                   for c in special(width)]
        triples += [(rng.randrange(size), rng.randrange(size), rng.randrange(size))
                    for _ in range(args.samples)]
        requests = []
        for operation in ("add", "sub", "mul", "div", "lt", "le"):
            requests += [(operation, pair) for pair in pairs]
        requests += [("fma", triple) for triple in triples]
        for operation in ("sqrt", "neg", "abs"):
            requests += [(operation, (word,)) for word in range(size)]
        lines = [f"{operation} " + " ".join(format(word, "x") for word in words)
                 for operation, words in requests]
        answers = run(args.oracle, width, lines)
        counts = {}
        for (operation, words), got in zip(requests, answers, strict=True):
            want = reference(width, operation, words)
            count = counts.setdefault(operation, {"comparisons": 0, "mismatches": 0, "first": []})
            count["comparisons"] += 1
            if want != got:
                count["mismatches"] += 1
                if len(count["first"]) < 10:
                    count["first"].append({"operands": words, "expected": want, "actual": got})
        for operation, count in counts.items():
            cases.append({"format": f"{width} bits, {FORMATS[width][1]} exponent bits",
                          "operation": operation, **count})
    conversions = [(8, 16, list(range(1 << 8))), (16, 8, list(range(1 << 16))),
                   (16, 32, list(range(1 << 16))),
                   (32, 16, special(32) + [rng.randrange(1 << 32) for _ in range(args.samples)])]
    for source, target, words in conversions:
        target_payload, target_exponent = FORMATS[target][:2]
        lines = [f"cast {target_payload:x} {target_exponent:x} {word:x}" for word in words]
        answers = run(args.oracle, source, lines)
        count = {"comparisons": 0, "mismatches": 0, "first": []}
        for word, got in zip(words, answers, strict=True):
            want = convert(source, target, word)
            count["comparisons"] += 1
            if want != got:
                count["mismatches"] += 1
                if len(count["first"]) < 10:
                    count["first"].append({"operands": [word], "expected": want, "actual": got})
        cases.append({"format": f"{source} bits to {target} bits", "operation": "cast", **count})
    # Conversions to integers. SoftPosit follows the 2018 draft, in which NaR and a negative
    # value converted to an unsigned integer give zero. The Posit Standard (2022), which
    # FloatLib follows, gives the word with only its most significant bit set. So NaR is left
    # out, and the unsigned conversions are compared on the encodings below the sign bit.
    for width in (8, 16):
        top = 1 << (width - 1)
        for bits in (32, 64):
            for signed in (True, False):
                words = [word for word in range(1 << width)
                         if word != top and (signed or word < top)]
                name = ("tosigned" if signed else "tounsigned")
                lines = [f"{name} {bits:x} {word:x}" for word in words]
                answers = run(args.oracle, width, lines)
                convert_name = f"{FORMATS[width][3]}_to_{'i' if signed else 'ui'}{bits}"
                count = {"comparisons": 0, "mismatches": 0, "first": []}
                for word, got in zip(words, answers, strict=True):
                    value = getattr(sp, convert_name)(FORMATS[width][2](bits=word).v)
                    want = int(value) % (1 << bits)
                    count["comparisons"] += 1
                    if want != got:
                        count["mismatches"] += 1
                        if len(count["first"]) < 10:
                            count["first"].append({"operands": [word], "expected": want,
                                                   "actual": got})
                cases.append({"format": f"{width} bits, {FORMATS[width][1]} exponent bits",
                              "operation": f"{name} {bits}", **count})
    mismatches = sum(case["mismatches"] for case in cases)
    result = {
        "reference": "SoftPosit (Python package softposit): posit8 with no exponent bit, "
                     "posit16 with one, posit32 with two",
        "seed": args.seed, "samples": args.samples, "cases": cases,
        "comparisons": sum(case["comparisons"] for case in cases),
        "mismatches": mismatches, "status": "pass" if mismatches == 0 else "fail",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    summary = {key: value for key, value in result.items() if key != "cases"}
    summary["cases"] = [{key: value for key, value in case.items() if key != "first"}
                        for case in cases]
    print(json.dumps(summary, indent=2))
    for case in cases:
        if case["mismatches"]:
            print(case["format"], case["operation"], case["first"][:3])
    if mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
