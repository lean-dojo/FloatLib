# Understanding the SoftPosit differences

Our adapter compared 23,718,760 cases at
SoftPosit revision `17d5628185b31828b10c1f910c9bf65737e83640`. It reported
7,562 differences. We checked the disputed values by exact evaluation and read
the relevant SoftPosit code. Two defects in that implementation account for
every difference; FloatLib's executable agrees with its exact specification.

## The 32-bit pX2 boundary

The generic pX2 functions disagree with SoftPosit's own named p32 functions at
the maximum supported pX2 width:

| Operation and operands | pX2 result | named p32 | FloatLib exact specification |
| --- | ---: | ---: | ---: |
| `0xfffffffd + 0xfffffffe` | `0xfffffffe` | `0xfffffffd` | `0xfffffffd` |
| `0xbfffffff * 0xfffffffd` | `0x00000002` | `0x00000003` | `0x00000003` |
| `0xbfffffff / 0xfffffffd` | `0x7ffffffc` | `0x7ffffffd` | `0x7ffffffd` |

Those three pX2 rows account for 7,560 repeated sampled differences. The named
p32 add, multiply, and divide campaigns all agree with FloatLib.

## Two 16-bit fused multiply-add boundaries

The remaining cases sit immediately to one side of an exact rounding midpoint:

| Expression | SoftPosit pX2 | FloatLib executable | FloatLib exact specification |
| --- | ---: | ---: | ---: |
| `0x80ae * 0x3a00 + 0xfffd` | `0x80c2` | `0x80c1` | `0x80c1` |
| `0x7680 * 0x6128 + 0x0001` | `0x7b9c` | `0x7b9d` | `0x7b9d` |

For the first case the exact value is `-65536000 - 2^-50`; for the second it is
`52800 + 2^-56`. SoftPosit records the tiny discarded addend and later
overwrites that sticky state in its pX2 fused multiply-add implementation. That
chooses the wrong neighboring posit in both cases.

The permanent Lean regressions are
`FloatLibTests.Conformance.Posit.ExecutionBoundaries.posit16_softposit_fma_boundaries`
and
`FloatLibTests.Conformance.Posit.ExecutionBoundaries.posit32_softposit_px2_boundaries`.
They evaluate the executable kernel and the exact rational specification
together.

## Release classification

- FloatLib specification mismatches in these rows: **0**
- SoftPosit pX2 32-bit endpoint inconsistencies: **7,560**
- SoftPosit pX2 lost-sticky FMA cases: **2**
- Retained suite status: **external-limitation**

The CSV and logs retain the comparison failures. The `external-limitation` status
records our analysis of their cause.
