/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
public import FloatLib.Numerics.Reduction

/-!
# Mixed-precision multiply-accumulate

`SitePolicy` assigns a format to each of four roles: input storage, multiplication, the running
accumulator, and final output. For example, inputs and products can use bf16 while accumulation
and output use binary32. The product is rounded before it reaches the accumulator.

`mulAcc` performs one unfused step:

```text
storage inputs → cast each to product → multiply in product
                                     → cast to accumulator → add to accumulator
```

Each step has five possible rounding errors: two input casts, multiplication, the product cast,
and addition. Finite casts between identical formats are exact. The result stays in the
accumulator format; the output format is used only when a reduction finishes.

`dotSequential` starts at positive zero, applies `mulAcc` from left to right, then casts once to
the output format. Different reduction orders can produce different bits. Unequal input lengths
return an error; empty inputs return positive zero cast to the output format.

`Matmul` applies the same dot kernel to rows and columns. `Proof` and `MatmulProof` give error
bounds for IEEE encodings when the inputs, intermediate values, and results are finite.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Formats used by input storage, an unfused multiply-accumulate step, and the final output cast.
-/
structure SitePolicy where
  /-- Format of input operands. -/
  storage : FloatFormat
  /-- Format in which the product is formed. -/
  product : FloatFormat
  /-- Format holding the running sum. -/
  accumulator : FloatFormat
  /-- Format of the final write after a reduction (`dotSequential` ends with a cast here). -/
  output : FloatFormat
  deriving DecidableEq, Repr

namespace SitePolicy

/-- Every role uses the same format (classic single-dtype path). -/
@[inline] def uniform (fmt : FloatFormat) : SitePolicy where
  storage := fmt
  product := fmt
  accumulator := fmt
  output := fmt

/--
Store and multiply in `storeProd`, then accumulate and write the reduction result in `accOut`.
-/
@[inline] def mixedStoreProductAcc (storeProd accOut : FloatFormat) : SitePolicy where
  storage := storeProd
  product := storeProd
  accumulator := accOut
  output := accOut

end SitePolicy

/--
One unfused mixed-precision step: `acc ← cast(mul(cast a, cast b)) + acc`.

- Inputs `a`, `b` are in `p.storage`.
- Product is computed in `p.product` (after casting inputs into that format).
- Product is cast into `p.accumulator` and added to `acc`.
- Returns the new accumulator value (still `p.accumulator`).

To produce an output value, apply `cast p.accumulator p.output` to the result.
-/
@[inline] def mulAcc (p : SitePolicy)
    (a b : Model p.storage)
    (acc : Model p.accumulator) :
    Model p.accumulator :=
  let aP : Model p.product := cast p.storage p.product a
  let bP : Model p.product := cast p.storage p.product b
  let prod : Model p.product := mul aP bP
  let prodA : Model p.accumulator := cast p.product p.accumulator prod
  add prodA acc

/--
Sequential mixed-precision dot product under site policy `p`.

Each product-add uses `mulAcc` (storage → product → accumulator), and the completed accumulator
is cast once into `p.output`. The reduction visits indices from left to right; rounded addition
is not associative, so another parenthesization can change the result.

The inputs must have equal lengths. A mismatch returns `ReductionError.lengthMismatch`; empty
inputs return `+0` cast from the accumulator format into `p.output`.
-/
def dotSequential (p : SitePolicy)
    (xs ys : Array (Model p.storage)) :
    Except Numerics.ReductionError (Model p.output) :=
  if xs.size != ys.size then
    .error (.lengthMismatch xs.size ys.size)
  else
    let acc0 : Model p.accumulator := posZero p.accumulator
    let acc : Model p.accumulator :=
      Id.run do
        let mut acc := acc0
        for i in [:xs.size] do
          acc := mulAcc p xs[i]! ys[i]! acc
        pure acc
    .ok (cast p.accumulator p.output acc)

/-- Sequential dot product with a single format in every arithmetic role. -/
@[inline] def dotSequentialUniform (fmt : FloatFormat)
    (xs ys : Array (Model fmt)) :
    Except Numerics.ReductionError (Model fmt) :=
  dotSequential (SitePolicy.uniform fmt) xs ys

end Model
end FloatLib.Floats.Formats.BinaryInterchange
