# Changelog

## 2026-10-06

The explicitly rounded `ExecFloat.Binary` operations `add`, `sub`, `mul`, `div`,
`fma`, and `sqrt` were renamed to `addWithRounding`, `subWithRounding`,
`mulWithRounding`, `divWithRounding`, `fmaWithRounding`, and `sqrtWithRounding`.
Their arguments and rounding behavior are unchanged. The corresponding `toModel_*`
packing theorems now use `toModel_*WithRounding`; deprecated theorem aliases preserve
existing proofs. The operation names remain distinct so `value.sqrt` resolves to the
ordinary nearest-even operation.
