---
lede: FloatLib is a Lean 4 library for arbitrary precision floating-point arithmetic and verified numerical computation.
authors:
  - Robert Joseph George (Caltech)
  - Will Adkisson (Washington University in St. Louis)
  - Anima Anandkumar (Caltech)
---

FloatLib supports IEEE binary and decimal formats, posits with exact quire accumulation, and low precision formats for machine learning. Its arithmetic implementations share integer kernels and rounding theory, with proofs connecting executable operations to their numerical specifications.

The library provides:

- **Custom formats.** [Define a format](#/chapter/using-the-library/which-formats-can-you-use) with your own field widths, encodings and rounding rules through the shared numerical interfaces.
- **Rounding and error bounds.** Apply [correct-rounding theorems, half-ulp bounds and Sterbenz's lemma](#/chapter/the-mathematics-of-rounding) to executable arithmetic under their stated hypotheses.
- **Certified numerical bounds.** Use [`interval`](#/chapter/proving-numerical-bounds) to prove real inequalities involving arithmetic and elementary functions, or polynomial bounds over a whole domain from coefficients.
- **Roundoff analysis.** Use [`roundoff`](#/chapter/proving-numerical-bounds/how-to-get-an-error-bound-for-floating-point-code) to derive error bounds for configured binary programs.
- **IEEE behavior.** Reason about [signed zeros, infinities, NaNs and exception flags](#/chapter/ieee-binary-formats), including their encodings and propagation rules.

The [guide](#/chapter/using-the-library) introduces the library and develops its algorithms and proofs through checked Lean examples. The [performance chapter](#/chapter/performance) compares the implementations with other numerical libraries, and the [validation chapter](#/chapter/external-validation) describes independent tests against MPFR, SoftFloat, posit libraries and published format tables.

We'd love to see what you build with FloatLib :) If you try it, have questions or want to contribute a format, proof or example, please [reach out](https://github.com/lean-dojo/FloatLib/issues). The [contributing guide](https://github.com/lean-dojo/FloatLib/blob/main/CONTRIBUTING.md) explains how to get started.
