# Contributing to FloatLib

Thanks for your interest in FloatLib! We welcome new mathematics, faster algorithms,
clearer explanations, and useful examples. A simpler proof or a careful explanation of
rounding can be just as helpful as a new format. If something is confusing, we'd like
to hear about that too.

## Getting started

Use the Lean version in [lean-toolchain](lean-toolchain) and the pinned dependencies in
[lake-manifest.json](lake-manifest.json). From the repository root:

```bash
source tests/lib/lake.sh
floatlib_lake exe cache get
floatlib_lake build
```

You can build a single module by adding its name to the last command. The helper keeps
build products outside the checkout; set `FLOATLIB_BUILD_DIR` to choose the location.
The [first guide chapter](site/content/chapters/01-using-the-library.md) has examples to
start from, and the [source map](README.md#source-files) shows where things belong.

## Code and proofs

We build on mathlib and follow its [style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html), and
[documentation conventions](https://leanprover-community.github.io/contribute/doc.html).
Look for existing definitions and lemmas before adding new ones. Keep related results
together, explain the mathematical idea, and state the hypotheses a caller needs.
Finished proofs should have no `sorry`, `admit`, or new project-local axioms.

An optimized backend needs a proof that it agrees with the reference specification,
including the rounding and exceptional-value behavior of the operation. The
[backend guide](FloatLib/Floats/ExecFloat/Backends/README.md) explains how to connect a
kernel to execution. For a speedup, include measurements of the affected public calls;
the [benchmark guide](benchmarks/README.md) has the commands.

## Sending a change

Keep the change focused and explain the problem, what you changed, and which checks you
ran. For an arithmetic bug, include an input that shows it. Update examples and docs
when the public API changes, and remove temporary checks and generated files.

```bash
bash tests/verify.sh     # library checks
bash site/build.sh       # guide and its Lean examples
```

The [testing guide](tests/README.md) and [website tooling guide](site/tooling/README.md)
cover the details. If a proof or design needs discussion, open an issue with the relevant
statement or example so we can work through it together.
