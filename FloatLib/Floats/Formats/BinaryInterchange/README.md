# Binary interchange

We describe a binary format by its field widths, exponent bias, and encoding policy. `ExecFloat`
provides the common executable interface, and `Model fmt` stores the exact `BitVec fmt.bitWidth`
that the arithmetic specifications and proofs work with.

Importing `FloatLib.Floats.Formats.BinaryInterchange` gives you executable arithmetic, and
`.Semantics` adds the connection to rounded real operations. Our
[theorem index](../../THEOREMS.md) collects the results. To see which implementation runs each
operation, read the [backend guide](../../ExecFloat/Backends/README.md).

Custom field widths use the same interface. Here's a 71-bit format:

```lean
abbrev X71 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 59)
```

| Name | Exp | Frac | Bits |
| --- | ---: | ---: | ---: |
| `binary16` | 5 | 10 | 16 |
| `bfloat16` | 8 | 7 | 16 |
| `binary32` | 8 | 23 | 32 |
| `binary64` | 11 | 52 | 64 |
| `binary128` | 15 | 112 | 128 |
| `binary256` | 19 | 236 | 256 |

Shared algorithms take a `FloatFormat` descriptor. Besides IEEE, the encoding policies are
`finiteMaxNaN`, `finiteUnsignedZero`, and `finite`, and `FloatFormat.custom` also lets you set
the exponent bias yourself.

## Operations and proof scope

| Family | Status |
| --- | --- |
| `Proof.*_eq_spec` | every `FloatFormat` |
| Field decode, classification, exact dyadics | every `FloatFormat` |
| Real-number / Lean-model arithmetic refinement | IEEE (`fmt.isIEEE = true`); finite values |
| Remainder, `roundToIntegral`, `scale`, `binaryExponent` | implemented with theorems |
| Integer conversion | `DType`; IEEE needed for the real nearest-even theorem |
| Quiet and signaling comparison predicates | shared IEEE truth tables; exact-order and invalid-flag theorems |
| `totalOrder` / `totalOrderMag` | implemented with complete-representation order laws and configured bridges |
| Decimal quantum operations | belong to the separate `DecimalInterchange` family |
| Decimal interchange | proved BID/DPD codecs, arithmetic, comparisons, and explicit exception state in `DecimalInterchange` |
| Text round trips | exact decimal and hexadecimal formatting/parsing theorems for finite conventional IEEE values; `nan` formatting drops sign/payload |
| Elementary approximation kernels (`exp`, `log`, trig) | named import `Configured.Transcendentals` (or the model barrel); representation bridges, with no general real-error bound |
| Certified `exp`, `log`, `pow`, `expMinus1`, `logPlus1` | the same import, with `certify := true` for the first three; each `.ok` result is finite and correctly rounded, and a failure names its reason |

For an IEEE descriptor, `Model.pow` is correctly rounded for a finite nonzero base and a finite
integral exponent whenever its result is finite (`Model.Power.toReal_pow_of_eq_intCast`). A
finite positive base with any other finite exponent goes to the certified enclosure search
`Model.Transcendentals.Certified.pow`, and the result is correctly rounded whenever that search
settles (`Model.Power.pow_spec_of_certified`). Overflow, most exact results on a rounding
boundary, and an exhausted search fall back to `exp (y * log x)`.

## Overflow by encoding

In the table below, `maxFinite` takes the sign of the exact result and `Model.invalidResult`
selects the format's invalid-result encoding. "Away from zero" is IEEE 754-2019 §7.4. With
`overflow := .saturate` you always get signed `maxFinite`, and `underflow := .flushToZero`
replaces a subnormal by zero, keeping its sign when the encoding has a signed zero.

| Encoding | Overflow, nearest | Toward zero | Toward ±∞ | `x / 0` (finite nonzero) | Invalid |
| --- | --- | --- | --- | --- | --- |
| `.ieee` | signed ∞ | signed `maxFinite` | ∞ if away from zero, else `maxFinite` | signed ∞ | canonical qNaN |
| `.finiteMaxNaN` | NaN word | signed `maxFinite` | NaN if away from zero, else `maxFinite` | NaN word | NaN word |
| `.finiteUnsignedZero` | NaN word (negative-zero pattern) | signed `maxFinite` | same as `.finiteMaxNaN` | NaN word | NaN word |
| `.finite` | signed `maxFinite` | signed `maxFinite` | signed `maxFinite` | signed `maxFinite` | `+0` |

`.finite` has no NaN at all, so if the invalid flag matters, use the status-bearing operations.
The other two finite-only policies reserve a NaN encoding, as the table shows.

Ordinary notation rounds to nearest-even. For another direction, every operation takes
`(mode := ...)`, and `(status := true)` returns the value with its flags and ternary value.
`Model.Interval fmt` uses directed kernels. If a denominator contains zero, or the endpoints are
NaN or unordered, the result is `whole fmt`.
