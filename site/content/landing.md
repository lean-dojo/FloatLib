---
lede: FloatLib is a Lean 4 library for executable floating point arithmetic with machine-checked proofs of its numerical behavior.
authors:
  - Robert Joseph George (Caltech)
  - Will Adkisson (Washington University in St. Louis)
  - Anima Anandkumar (Caltech)
---

The `x + y` in a FloatLib program is the same operation covered by the theorem, down to rounding and the meaning of the result bits.

The library provides:

- **Your formats and rounding rules.** You can [define your own format](#/chapter/using-the-library/choosing-a-format) within the same framework. For binary layouts, choose the exponent and fraction widths, bias, and encoding policy for zeros, infinities, and NaNs. For a new representation or rounding rule, our shared interfaces connect your executable operations to their numerical specification through Lean proofs.
- **The classical results, connected to code.** Correct rounding, half-ulp error bounds, and Sterbenz's lemma for exact subtraction are part of the [rounding theory](#/chapter/the-mathematics-of-rounding). We can use them to reason about the arithmetic in a program.
- **Numerical bounds that close proofs.** The [`interval` tactic](#/chapter/proving-numerical-bounds) proves real inequalities from rational input bounds, including elementary functions and adaptive subdivision. Its evaluator supports exact rational endpoints, an integer binary grid, and custom endpoint formats through the same containment contract.
- **NaNs, infinities, and both zeros have a place in the proofs.** The [IEEE model](#/chapter/ieee-binary-formats) keeps their encodings and behavior explicit, including comparisons and exception flags. A theorem about the complete result word can distinguish things that equality over the reals cannot.
- **Many formats, shared foundations.** IEEE binary and decimal, [small ML formats](#/chapter/low-precision-formats-for-machine-learning), [posits](#/chapter/posits-and-the-quire), and [P3109](#/chapter/p3109) sit alongside fixed point, logarithmic, codebook, and block-scaled representations. Posits also have exact quire accumulation within its capacity and real-rounding proofs for roots, powers, exponentials, and logarithms.
- **Speed is a major part of the work.** We have put substantial effort into [backend kernels](#/chapter/backends-and-the-planner): small lookup tables, machine-word algorithms, and limb arithmetic for wider values. The planner selects an implementation for each operation, and every certified choice proves agreement with the same specification. Lean erases proof terms when compiling, so arithmetic does not check its theorem again at runtime [@leanReference]. Our goal is to approach MPFR's speed while keeping that connection to the proofs. The [performance chapter](#/chapter/performance) shows the measurements from 2 to 4,096 bits and where the gap remains.
- **Independent implementations give us another useful check.** FloatLib matched Berkeley TestFloat on more than **102 million cases** for the IEEE formats and operations we checked. We also compare with MPFR, posit libraries, and published small-format tables. There are some subtle differences with SoftPosit, which we [explain in the posits chapter](#/chapter/posits-and-the-quire/cross-checks-against-universal-and-softposit); the [external validation chapter](#/chapter/external-validation) gives the inputs and results.

The [first chapter](#/chapter/using-the-library) gives you a small calculation to work with, starting from a familiar format.

We follow the numerical-analysis literature and link to the specifications behind the named formats. If an argument catches your interest, the [references](#/references) will take you back to the original work.

We'd love to see what you build with FloatLib. If you'd like to add a format, improve a proof, or help explain something better, have a look at the [contributing guide](https://github.com/lean-dojo/FloatLib/blob/main/CONTRIBUTING.md).
