# Binary interchange

We describe binary formats by their field widths, exponent bias, and encoding policy.
`ExecFloat` provides the common executable interface; `Model fmt` stores the exact
`BitVec fmt.bitWidth` used by the arithmetic specifications and proofs.

The `FloatLib.Floats.Formats.BinaryInterchange` import provides executable arithmetic;
`.Semantics` adds the connection to rounded real operations. The [theorem index](../../THEOREMS.md)
collects the results, and the [backend guide](../../ExecFloat/Backends/README.md) explains
which implementation runs each operation.

The same interface works for custom field widths. For example, we can define a 71-bit format:

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

The shared algorithms take a `FloatFormat` descriptor. Non-IEEE encoding policies are
`finiteMaxNaN`, `finiteUnsignedZero`, and `finite`; `FloatFormat.custom` also accepts an explicit
exponent bias.

## Operations and proof scope

| Family | Status |
| --- | --- |
| `Proof.*_eq_spec` | every `FloatFormat` |
| Field decode, classification, exact dyadics | every `FloatFormat` |
| Real-number / Lean-model arithmetic refinement | IEEE (`fmt.isIEEE = true`); finite values |
| Remainder, `roundToIntegral*`, `scale`, `binaryExponent` | implemented with theorems |
| Integer conversion | `DType`; IEEE needed for the real nearest-even theorem |
| Quiet and signaling comparison predicates | shared IEEE truth tables; exact-order and invalid-flag theorems |
| `totalOrder` / `totalOrderMag` | implemented with complete-representation order laws and configured bridges |
| Decimal quantum operations | belong to the separate `DecimalInterchange` family |
| Decimal interchange | proved BID/DPD codecs, arithmetic, comparisons, and explicit exception state in `DecimalInterchange` |
| Text round trips | exact decimal and hexadecimal formatting/parsing theorems for finite conventional IEEE values; `nan` formatting drops sign/payload |
| Elementary approximation kernels (`exp`, `log`, trig) | named import `Configured.Transcendentals` (or the model barrel); representation bridges, with no general real-error bound |
| Certified `exp`, `log`, `expMinus1`, `logPlus1` | named import `Configured.Transcendentals.Certified`; each `some` result is finite and correctly rounded |

For an IEEE descriptor, `Model.pow` is correctly rounded for a finite nonzero base and a finite
integral exponent whenever its result is finite (`Model.Power.toReal_pow_of_eq_intCast`).

## Overflow by encoding

`maxFinite` takes the sign of the exact result. `Model.invalidResult` selects the format's
invalid-result encoding.
"Away from zero" is IEEE 754-2019 §7.4. `overflow := .saturate` always returns signed `maxFinite`.
`underflow := .flushToZero` replaces a subnormal by zero, preserving its sign when the encoding
supports signed zero.

| Encoding | Overflow, nearest | Toward zero | Toward ±∞ | `x / 0` (finite nonzero) | Invalid |
| --- | --- | --- | --- | --- | --- |
| `.ieee` | signed ∞ | signed `maxFinite` | ∞ if away from zero, else `maxFinite` | signed ∞ | canonical qNaN |
| `.finiteMaxNaN` | NaN word | signed `maxFinite` | NaN if away from zero, else `maxFinite` | NaN word | NaN word |
| `.finiteUnsignedZero` | NaN word (negative-zero pattern) | signed `maxFinite` | same as `.finiteMaxNaN` | NaN word | NaN word |
| `.finite` | signed `maxFinite` | signed `maxFinite` | signed `maxFinite` | signed `maxFinite` | `+0` |

The `.finite` encoding has no NaN; use status-bearing operations when the invalid flag matters.
The other two finite-only policies reserve a NaN encoding, as shown above.

Ordinary notation is nearest-even. Status-bearing operations take an explicit `rounding :=` and
return the value with its flags.
`Model.Interval fmt` uses directed kernels; a denominator containing zero, or NaN/unordered
endpoints, becomes `whole fmt`.
