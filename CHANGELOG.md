# Changelog

## 2026-10-06

The explicitly rounded `ExecFloat.Binary` operations `add`, `sub`, `mul`, `div`,
`fma`, and `sqrt` were renamed to `addWithRounding`, `subWithRounding`,
`mulWithRounding`, `divWithRounding`, `fmaWithRounding`, and `sqrtWithRounding`.
Their arguments and rounding behavior are unchanged. The corresponding `toModel_*`
packing theorems now use `toModel_*WithRounding`; deprecated theorem aliases preserve
existing proofs. The operation names remain distinct so `value.sqrt` resolves to the
ordinary nearest-even operation.

E4M3FN and MX E4M3 native overflow now retain the result sign. Non-IEEE NaNs expose
payload zero to numerical observations and casts; exact views and character output still
preserve their stored encoding fields. `ExactValue.toNumericalValue` accepts the encoding
as an optional second argument, defaulting to IEEE; generic callers should supply their
format's encoding. `AtExact.toValue` selects that encoding automatically.

Decimal degree-zero roots now return an invalid result for NaN inputs as well as numeric
inputs. Algebraic interval goals first try exact rational endpoints, and unsuccessful
binary-grid checks receive an executable preflight before kernel verification. New
IEEE-destination cast corollaries accept finite sources from every binary encoding.
