---
number: "13"
slug: proof-by-computation
title: "Speeding up computation in Lean's kernel"
summary: "How proved rewrites speed up floating-point proofs, how Lean's kernel compares with Rocq's VM, and how to write a faster checker for exact arithmetic."
phases: [kernel-arithmetic, kernels, backends, trust]
---

<a id="computing-in-the-kernel"></a>

We wanted to prove the result of a floating-point loop by running it in Lean's kernel. Take a binary64 dot product. Every multiplication rounds, and so does every addition to the running sum. Checking 1,000 terms with `decide +kernel` on our public operations took 8.25 seconds.

With `float_decide`, we give the kernel a shorter calculation to check. The tactic rewrites each supported operation using a proved equation on the operand bits. Lean checks the rewrite, then evaluates the loop with its built-in arithmetic on natural numbers. That brought the dot product down to 152 milliseconds. For comparison, Flocq checked the same result in 730 milliseconds with Rocq's bytecode evaluator, `vm_compute`.

| Calculation (1,000 terms) | Lean, public operations | Lean, `float_decide` | Flocq, `vm_compute` |
| --- | ---: | ---: | ---: |
| Add binary32 `0.1` repeatedly | 4.33 s | 0.053 s | 0.058 s |
| Sum binary64 values | 4.46 s | 0.100 s | 0.327 s |
| Binary64 dot product | 8.25 s | 0.152 s | 0.730 s |

These are times for checking the loop. The [benchmark record](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/kernel/README.md#three-theorems-about-loops-of-1000-steps) gives the commands and setup. The Rocq measurements used Coq 8.20.1 with Flocq 4.2.2.

## Checking a loop with `float_decide`

In the first row we start from zero and add binary32 `0.1` a thousand times. Rounding at each addition gives a final value just below 100. Give `float_decide` the definition of the loop so it can rewrite the addition inside the fold.

```lean standalone
import FloatLib

open FloatLib.Floats

def sumTenth (n : Nat) : Binary32 :=
  (List.range n).foldl (fun s _ => s + (0.1 : Binary32)) 0

set_option maxRecDepth 100000 in
example : ExecFloat.Binary.toRat? (sumTenth 1000) = some (13107075 / 131072) := by
  float_decide [sumTenth]
```

The theorem states the exact rational value stored in the accumulator. To inspect a value without stating a theorem, use `#kernel_eval`. It prints the result and the time spent evaluating it.

### What can `float_decide` compute?

The same tactic can prove a fact about the status of an operation. Here `.ternary = .lt` means that the sum rounded downward lies strictly below the exact sum of the two operands.

```lean standalone
import FloatLib

open FloatLib.Floats

example : (ExecFloat.Binary.add (0.1 : Binary32) 0.2 (mode := .down) (status := true)).ternary = .lt := by
  float_decide
```

The available rewrites depend on the format. Operations that have no registered equation still have their ordinary Lean definitions. The [decimal chapter](#/chapter/decimal-arithmetic/can-leans-kernel-check-a-decimal-computation) works through a decimal proof.

| Format | Examples of operations with rewrites |
| --- | --- |
| Configured binary formats | Arithmetic, `sqrt` and `fma` in every rounding direction, selected status flags, comparisons, classification, `nextUp`, `nextDown`, `remainder`, the NaN payload operations, conversions to integers, rationals and character sequences, the formatOf values, the augmented operations, the reductions and scaled products, and `pown`, `rootn`, `rSqrt` and `hypot` |
| Decimal interchange | Arithmetic on the sign, coefficient and exponent, `remainder`, `rootn`, integral rounding, reductions, `nextUp`, `quantize`, comparisons, the four encoding operations, and conversions to and from character sequences |
| Posits | Arithmetic and comparisons on the encodings at every supported width and for any number of exponent bits, conversions between widths and to and from signed and unsigned integers, and quire accumulation and rounding |
| P3109 | Every arithmetic operation of section 4.10 of the report on two or three operands of any formats (`Add` to `FMA`, `FAA`, `Recip`, `CopySign`, `Sqrt`, `RSqrt`, `Hypot`), the ten extrema and `Clamp`, the comparisons, the classification queries and the neighbours, the conversion between descriptors, the conversion of a binary interchange value and the mixed arithmetic on values of P3109 formats, values of binary formats and rationals, each with the specified rounding and saturation |
| OCP and NVFP4 | Nearest-even MX element conversion and block scales, and the NVFP4 quantizer on the encodings of a binary working format. E4M3 and E5M2 also have optional tables for sums, differences and products |
| Fixed-point and logarithmic | Sums and differences of fixed-point values on their coefficients, products of logarithmic values on their codes, and equality of two codes |

```lean standalone
import FloatLib

open FloatLib.Floats

example : ExecFloat.Posit.toNatBits ((1.5 : Posit16) + 2.25) =
    ExecFloat.Posit.toNatBits (3.75 : Posit16) := by
  float_decide

example : ((1.5 : ExecFloat.P3109 .binary8p4se) + 2.25).toNatBits =
    (3.75 : ExecFloat.P3109 .binary8p4se).toNatBits := by
  float_decide
```

### How to prove a statement about every pair of values

Suppose the theorem ranges over two `Fin 256` arguments. There are 65,536 pairs. When the indices occur only through their natural-number values, `float_decide` can enumerate the pairs. `lane_decide` can check certain equations on all the pairs together. It lays the arguments out in lanes of two large natural numbers, computes each side on the lanes, and checks that no intermediate result spilled into its neighbour. The proof that this implies the equation at every pair is [[FloatLib.Numerics.Packed.forall_pairs]].

```lean standalone
import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
import FloatLib.Floats.Formats.OCP.FP8.KernelTables
import FloatLib.Tactic.FloatDecide

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath
open FloatLib.Numerics

/-- A product commutes on all pairs below 256: one run of each side on 65,536 lanes. -/
theorem mul_comm_pairs : ∀ a b : Fin 256, Nat.mul a.val b.val = Nat.mul b.val a.val := by
  lane_decide

/-- `value`, or zero when both encodings are NaNs of an FP8 format (`0x7F` and `0xFF`). -/
def unlessBothNaN (a b value : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.land a 127) 127) value
    (Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.land b 127) 127) value 0)

/-- Multiplication of E4M3 commutes on all pairs of encodings that are not both NaN. -/
theorem e4m3_mul_comm : ∀ a b : Fin 256,
    unlessBothNaN a.val b.val (KernelPath.mul FloatFormat.e4m3 .nearest a.val b.val) =
      unlessBothNaN a.val b.val (KernelPath.mul FloatFormat.e4m3 .nearest b.val a.val) := by
  lane_decide

/-- The products of the numbers below 16, in lanes of eight bits. -/
lane_table products (width := 8) (size := 16) := fun a b => Nat.mul a b

example (a b : Fin 16) : Packed.lane 8 (a.val * 16 + b.val) products = Nat.mul a.val b.val :=
  products.lookup a b

/-- With the tables imported, a product of E4M3 values is a lookup: `1.0 * 2.0 = 2.0`. -/
example : KernelPath.toNat ((KernelPath.ofNat 0x38 : E4M3) * KernelPath.ofNat 0x40) = 0x40 := by
  float_decide
```

The exception in `e4m3_mul_comm` matters. If both operands are NaNs, multiplication returns the first NaN, so swapping the two can change the result encoding. In the recorded run, proving this qualified statement took 23.4 seconds by enumeration and 0.76 seconds with lanes ([Figure 13.1](#/chapter/proof-by-computation/figure-kernel-all-pairs)).

![7 rows, one per statement, on a logarithmic time axis: an open circle for the loop of float_decide and a filled circle for lane_decide, joined by a bar where both were run.](assets/kernel-all-pairs.png "Kernel time to decide one statement about all 65,536 pairs of encodings, by the loop of float_decide and by lane_decide in FloatLib. A mark is the time Lean's kernel takes for a statement about all pairs of an 8-bit format, or about a slice of 65,536 pairs of binary16. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

`lane_decide` handles arithmetic such as addition, subtraction and multiplication, masks, shifts, and branches on comparisons. Division, remainder and loops with a different iteration count in each lane do not have lane instructions. A failed guard gives no proof. You can supply a bounded replacement for an operation with `@[lane_call]`. The [bit-length rule](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/KernelPath/Lanes.lean) gives an example.

`lane_table` stores a table together with its lookup theorem. The import of `OCP.FP8.KernelTables` supplies checked tables for nearest-even addition, subtraction and multiplication of the two FP8 formats. The last proof uses the table for E4M3 multiplication.

### How does an implementation get onto the kernel path?

Prove that the reference operation equals your implementation. Register the equation with `@[kernel_optimize]`, and `float_decide` can rewrite calls to the reference wherever the theorem is imported.

```lean standalone
import FloatLib.Tactic.FloatDecide
import FloatLib.Tactic.KernelRules

/-- A reference operation. -/
def reference (a b : Nat) : Nat := a + b

/-- An implementation on the kernel's own addition. -/
def onKernel (a b : Nat) : Nat := Nat.add a b

@[kernel_optimize (cost := 1)]
theorem reference_eq_onKernel (a b : Nat) : reference a b = onKernel a b := rfl

example : reference 2 3 = 5 := by float_decide

#kernel_rules reference
-- reference: reference_eq_onKernel, 1 µs
```

`@[kernel_optimize ←]` uses an equality in reverse. `@[kernel_optimize unfold]` exposes the body of a wrapper, such as a definition that selects an operation by rounding direction. When multiple rules match, the smaller declared cost gives a rule priority. `KernelForm` supplies the equations that connect public arithmetic and its notation to a format's kernel implementation.

### What about compiled code?

For compiled execution, `@[compiler_optimize]` registers a candidate implementing a specification. Its certificate supplies the function to run, a cost estimate, and the proof that the function computes the specification. A candidate can return `none` for formats it does not serve. Here is a candidate that adds the coefficients of decimal fixed-point numbers in reverse order.

```lean standalone
import FloatLib.Floats.Formats.FixedPoint
import FloatLib.Tactic.CompilerBackends

open FloatLib.Floats FloatLib.Floats.ExecFloat

/-- A second addition kernel: the operands in the other order. -/
def swappedAdd {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x y : ExecFloat.FixedPoint radix digits) : ExecFloat.FixedPoint radix digits :=
  FixedPoint.add y x

/-- The second kernel computes the reference addition. -/
theorem swappedAdd_eq {radix : FloatLib.Numerics.Radix} {digits : Nat}
    (x y : ExecFloat.FixedPoint radix digits) : swappedAdd x y = FixedPoint.add x y := by
  unfold swappedAdd FixedPoint.add Formats.FixedPoint.Code.add
  simp [Int.add_comm]

/-- A cheap candidate for the decimal formats only: it declines every other radix. -/
@[compiler_optimize]
def cheapDecimal {radix : FloatLib.Numerics.Radix} {digits : Nat} :
    Option (Backend.Certified (FixedPoint.add (radix := radix) (fractionalDigits := digits))) :=
  if radix.base = 10 then
    some (Backend.Certified.binary
      { name := "cheap decimal", kind := .custom "example kernel" 0, steadyCost := 1 }
      FixedPoint.add swappedAdd swappedAdd_eq)
  else none

#compiler_backends FixedPoint.add
-- FloatLib.Floats.ExecFloat.FixedPoint.add: FixedPoint.Plan.addCertified (baseline)
-- FloatLib.Floats.ExecFloat.FixedPoint.add: cheapDecimal (alternative)

/-- Arithmetic still equals the reference, whichever candidate runs. -/
example (x y : ExecFloat.FixedPoint FloatLib.Numerics.decimalRadix 2) :
    x + y = FixedPoint.add x y :=
  FloatLib.Floats.ExecFloat.Add.run_eq_spec x y
```

The planner collects candidates where a capability is elaborated. A definition that fixes its format therefore keeps the candidates available at that definition. Import a new candidate before elaborating code that should consider it.

### What do the tags refuse?

The registry checks the shape of a rule or certificate and the axioms of its proof. It rejects unfinished proofs, including imported lemmas that depend on `sorry`. The admitted axioms are `propext`, `Classical.choice` and `Quot.sound`. A lemma supplied by hand to `float_decide` contributes its own assumptions to the resulting theorem.

The compiled registry also checks visible uses of `@[implemented_by]` and `@[extern]` replacements outside Lean's library. A replacement needs a registered proof, apart from a recognized compiler-generated constructor-index operation. The check can only traverse definition bodies available to the registering module. [FloatLib’s trust assumptions](https://github.com/lean-dojo/FloatLib/blob/main/TRUST.md) describe this boundary.

### How to see what is registered

Use `#kernel_rules reference` for the rewrite rules on one operation and `#compiler_backends spec` for the compiled candidates for a specification. Both commands accept an empty argument list to show the whole registry. To measure a kernel rewrite, time the term itself.

```lean standalone
import FloatLib
import FloatLib.Tactic.KernelCost

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange.KernelPath

#kernel_eval toNat ((1.5 : Binary32) + 2.25)
-- 1081081856

#kernel_cost toNat ((1.5 : Binary32) + 2.25)
-- value: 1081081856
```

`#kernel_cost` reports the time before and after rewriting and prints the computed value. If the original computation is too slow to run, use `#kernel_cost rewritten t`.

### How to write a kernel operation of your own

You can write a calculation in small definitions and prove lemmas about those definitions. For kernel evaluation, `kernel_inline%` unfolds the stages you name. `kernel_refl%` then checks the equality of the two definitions.

```lean standalone
import FloatLib.Tactic.KernelInline
import FloatLib.Tactic.KernelRefl

def double (n : Nat) : Nat := Nat.add n n

def staged (a b : Nat) : Nat := Nat.add (double a) (double b)

noncomputable def flat (a b : Nat) : Nat :=
  kernel_inline% [staged, double] (staged a b)

theorem flat_eq (a b : Nat) : flat a b = staged a b := kernel_refl%
```

The kernel pays for the shape of a term as well as for its length. A `casesOn`, a `match`, a numeral such as `255`, an operator such as `+` and an `if` on a comparison each cost it several steps before it reaches the recursor, the literal or the built-in function behind them. `kernel_inline%` writes those forms directly and computes the operations whose operands are literals. `kernel_shape f` does the same for one stage that should stay a call: it declares `f.kernel`, the body of `f` in that shape with the registered equations applied, and the rule `f.kernel_eq : @f = @f.kernel` for `float_decide`. `kernel_constant c` is for a constant of a format that every operation reads, such as a mask, or for a stage on a rare path: the flat forms call the copy `c.kernel`, which the kernel computes on literals once in a proof and finds again at every later call. A formula that only such constants use can be tagged `@[kernel_inline]`, and it is then unfolded wherever a flat form or a shape uses it.

For a reusable function, `kernel_prepare%` applies the registered equations to its body and packages the result with an equality proof. `kernel_proj%` selects a structure field by its index. In proofs, `kernel_notation` expresses primitive forms such as `Nat.add` in the notation used by tactics such as `omega`. The binary formats use `kernel_operation` to declare an operation on stored values along with its refinement theorem and rewrite rule.

<a id="how-much-faster-is-it"></a>

### Comparing Lean's kernel with Rocq

[Figure 13.2](#/chapter/proof-by-computation/figure-kernel-loops) adds a fourth measurement to the opening table. Flocq can prove each result by ordinary kernel conversion as well as with `vm_compute`. For the binary64 dot product, conversion took 9.35 seconds and the VM took 0.73 seconds. Both ran the same Flocq operations, `Bplus` and `Bmult`. For the two binary64 benchmarks Flocq precomputes the operand lists, while Lean constructs them inside its kernel. The Lean times shown are for checking the loop itself. The rewrite and the final theorem are timed separately in the [benchmark record](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/kernel/README.md#three-theorems-about-loops-of-1000-steps).

![Three rows, one per theorem, on a logarithmic time axis: an open circle for decide +kernel and a filled circle for float_decide in Lean, joined by a bar, and a triangle and a square for the same result in Coq by conversion and by vm_compute.](assets/kernel-loops.png "Time to check a theorem about a loop of 1,000 floating-point operations: FloatLib by decide +kernel and by float_decide, and Flocq 4.2.2 in Coq 8.20.1. A mark is the time the proof checker spends on a theorem that states the encoding of the loop's result. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20); the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs.")

For individual operations, the measurements cover format widths from 8 through 4,096 bits. The public Lean operations were measured as written only through 128 bits. [Figure 13.3](#/chapter/proof-by-computation/figure-kernel-binary) shows where rewriting saves time within Lean. [Figure 13.4](#/chapter/proof-by-computation/figure-kernel-vs-coq) compares the same operations in FloatLib and Flocq across widths. The [benchmark figures and data](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/FIGURES.md) also cover operand classes, flags, casts, IEEE operations, and other format families.

![Six panels, one per arithmetic operation: kernel time against format width, with open markers for the public operation as written up to 128 bits and a line for the kernel path up to 4,096 bits.](assets/kernel-binary.png "Kernel time of one binary operation of FloatLib from 8 to 4,096 bits, as written and on the kernel path. A point is the time Lean's kernel takes for one operation on normal operands, rounded to nearest even, as the median over the formats of that width; as written is the public operation, and the kernel path is the term that float_decide checks. Both axes are logarithmic, lower is faster, and the public operations were not measured above 128 bits. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

![5 panels of lines, one per operation: time per operation against format width for FloatLib in Lean's kernel and for Flocq in Coq under vm_compute and under lazy, with crosses along the top edge at the widths where Coq gave no result.](assets/kernel-vs-coq.png "Time of one floating-point operation inside the proof checker: FloatLib in Lean's kernel against Flocq 4.2.2 in Coq 8.20.1 under vm_compute and under lazy. A point is the time per operation in a loop of 100 operations (10 from 512 bits on) on the same operands; a cross at the top marks a width where Coq gave no result within 8 GB and 300 seconds. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20); the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs.")

### Which proof checkers accept these proofs?

Five checker configurations replayed the definition modules, exact-arithmetic tests, and the three loop theorems using both kinds of Lean proof. All five accepted those four groups. We also supplied two theorems about all pairs of E4M3 encodings. Lean's ordinary and paranoid replay modes and the independent checker `con-ron` accepted both. The runs of `nanoda_bin` and `leanchecker --from-export` ended without a verdict on that group. [Figure 13.5](#/chapter/proof-by-computation/figure-kernel-checkers) gives the time for each run on the shared machine. [Checker commands and records](https://github.com/lean-dojo/FloatLib/tree/main/benchmarks/kernel)

![5 panels of horizontal bars, one panel per family of proofs and one bar per checker, each bar ending in its time in seconds; a hatched grey bar is a run that ended without a verdict.](assets/kernel-checkers.png "Time the independent checkers of Lean proofs take on the kernel proofs of FloatLib, by family of proofs. A bar is the time of one check of a family with everything it imports, and a hatched bar is a run that ended without a verdict, at the time it stopped. The checkers ran once, and the timing mode does not run them again.")

### When should you use it?

Use `#eval` to see what compiled code returns, or `#kernel_eval` to inspect a kernel calculation. Use `float_decide` when the result should be a theorem, and supply the names of definitions that contain the operations to rewrite. For an equation about two finite indices, `lane_decide` is an alternative when both sides have lane instructions.

`native_decide` compiles the decision procedure and records its successful result as an extra axiom. With `float_decide`, the kernel checks the result by reduction. For a recorded comparison, an integer square-root proof took 11.5 milliseconds with FloatLib's exact arithmetic under `decide +kernel` and 13.1 with `native_decide`. On a modular-power proof with a 1,279-bit modulus, the times were 30 and 17.7 milliseconds respectively. [Exact-arithmetic measurements](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/exact/native.md)

Costs also depend on the expression. For example, computing some binary status flags requires aligning values on an absolute exponent grid, so increasing the exponent range can make a status calculation considerably more expensive. The certified functions of clause 9.2, binary `pow`, the formatOf square root and the public conversion `x.cast (target := T)` are among the operations that retain their ordinary definitions.

## Exact arithmetic in the kernel

An interval certificate may involve thousands of exact integer operations. Lean's kernel has efficient primitives for operations on natural-number literals, including addition, multiplication, shifts and division. FloatLib implements integer and rational arithmetic in terms of these primitives, with equalities relating the implementations to Lean's ordinary operations. You can use these equalities in a proof that already mentions `Int` or `Rat`.

```lean standalone
import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact

example : (123456789 : Int) * 987654321 - 5 ≤ 121932631112635270 := by
  simp only [kernel_optimize]
  decide +kernel

example : (1 : Rat) / 3 + 1 / 6 ≤ 1 / 2 ∧ |(-7 : Rat) / 4| * 2 < 4 := by
  simp only [kernel_optimize]
  decide +kernel
```

### Which type should a checker use?

If you control the representation, you can often save work before the final comparison. For example, `Frac` can add a third and a sixth and compare the sum with a half without reducing it to lowest terms.

```lean standalone
import FloatLib.Numerics.Kernel.Frac

open FloatLib.Numerics.Kernel

theorem third_add_sixth :
    Frac.le (Frac.add ⟨1, 0, 3, by decide⟩ ⟨1, 0, 6, by decide⟩) ⟨1, 0, 2, by decide⟩ = true := by
  decide +kernel
```

The inequality concerns the values represented by the fractions. [[FloatLib.Numerics.Kernel.Frac.le_iff]] and [[FloatLib.Numerics.Kernel.Frac.le_cast]] let a proof use the comparison in the rationals or the reals.

| Type | Representation | Typical use |
| --- | --- | --- |
| `Z`, `Q` | Operations on Lean's `Int` and `Rat` | Speed up an existing definition while keeping its types |
| `Signed`, `Frac` | A difference of two naturals, or that difference divided by a positive denominator | Integer and rational certificates with unreduced intermediate results |
| `Dyad` | A signed numerator over a power of two | An exact value on a binary grid |
| `Ball`, `CBall` | A dyadic midpoint and radius, or a pair of such enclosures | Real and complex interval calculations |
| `CFix` | Fixed-point complex coordinates, a shared radius, and a validity flag | Products of values near the unit circle |

There are corresponding operations for integer roots, modular powers, bit lengths and bisection. For instance, [[FloatLib.Numerics.Kernel.isqrt_eq]] identifies the integer square root with `Nat.sqrt`. [[FloatLib.Numerics.Kernel.Ball.contains_mul]] states that multiplying any two members gives a member of the returned ball. [Figure 13.6](#/chapter/proof-by-computation/figure-kernel-exact-operations) compares 64-bit and 1,024-bit operands. The [exact-arithmetic measurements](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/results/exact/operations.md) include ordinary Lean operations and Coq comparisons where the operation agrees.

![Two panels, operands of 64 and of 1,024 bits, with one row per exact operation on a logarithmic time axis: a grey cross for the operation written with core Lean and Mathlib, a filled circle for FloatLib's kernel layer, joined by a bar, and a square for Coq on 3 of the rows.](assets/kernel-exact-operations.png "Kernel time of one exact operation (integers, fractions, bit operations, roots, modular powers, dyadics, balls and lists), written with the types of core Lean and Mathlib and on the kernel layer of FloatLib, with Coq 8.20.1 where the operation is the same. A mark is the time the kernel takes for one operation in a fresh kernel state; a row with one mark is a type that only the kernel layer has. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20); the Coq times were recorded on 2026-11-15 in a container.")

### Complex balls and `exp (i t)`

Given a ball `x` containing a real number `t` and a ball `h` containing `π / 2`, `CBall.expI x h j n p` encloses `exp (i t)`. Its real and imaginary components enclose `cos t` and `sin t`. The calculation removes quarter turns, evaluates a Taylor polynomial, and bounds the remainder. If the reduced argument fails the size check or the term count is zero, it returns the square `[-1, 1]²`. [[FloatLib.Numerics.Kernel.CBall.mem_expI]]

```lean standalone
import FloatLib.Numerics.Kernel.CBall

open FloatLib.Numerics.Kernel

-- the real part of `exp (i)` at 66 bits is a ball of radius at most `8 / 2 ^ 66`
example : Nat.ble (CBall.expI (Ball.ofNat 1) CBall.halfPi 0 22 66).re.rad 8 = true := by
  decide +kernel
```

### Sums of a multiplicative function

If `f 1 = 1` and `f (a * b) = f a * f b`, products of values at primes determine `f n`. A `Cover` splits the integers from one through a specified bound into factorizations, with a kernel proof that each integer occurs exactly once. Here each value is one, so the sum counts the integers from one through 100.

```lean standalone
import FloatLib.Tactic.Cover

open FloatLib.Numerics.Kernel

def cover100 : Cover := cover% 100 5

-- the constant one is completely multiplicative: the total counts the hundred integers
example : (cover100.total 8 fun _ => CFix.one 8).count = 100 := by decide +kernel
```

[[FloatLib.Numerics.Kernel.Cover.total_contains]] gives the enclosure theorem for a complex-valued completely multiplicative function when the supplied prime enclosures contain its values.

### Rows packed in one number

We can compute a dot product with one integer multiplication. Pack the coefficients of each row into equal-width lanes, wide enough to hold each sum of products. Reversing one row puts the dot product in a single lane. This is the same [Kronecker substitution](#/chapter/proving-numerical-bounds/how-does-the-kernel-check-a-certificate-so-fast) we used for polynomial multiplication [@harvey2009]. Here the lane holds `3 * 2 + 1 * 7 + 4 * 1 = 17`.

```lean standalone
import FloatLib
import FloatLib.Tactic.PackedRow
import FloatLib.Tactic.PackedValues

open FloatLib.Floats FloatLib.Numerics.Packed

/-- Three signed entries in lanes of sixteen bits. -/
packed_row small (width := 16) := [1, -2, 3]

example : entries 16 3 small = [1, -2, 3] := by decide +kernel

/-- `1.5`, `-0.25` and `3` in binary32. -/
def single : List Binary32 := [.ofNatBits 0x3FC00000, .ofNatBits 0xBE800000, .ofNatBits 0x40400000]

/-- The same three values as integers over the denominator four. -/
packed_values singleRow (width := 8) := single

-- a dot product is one lane of one product: `3 * 2 + 1 * 7 + 4 * 1 = 17`
example : dot 16 3 (packRev 16 [3, 1, 4]) (packFwd 16 [2, 7, 1, 8]) = 17 := by decide +kernel
```

The width condition in [[FloatLib.Numerics.Packed.dot_eq]] bounds the intermediate sums so that adjacent lanes cannot exchange carries. The analogous checks for matrix multiplication and binary matrix inversion have their own correctness theorems, [[FloatLib.Numerics.Packed.entries_matMul]] and [[FloatLib.Numerics.Packed.F2.isInverse_sound]]. The [polynomial bound on the whole circle](#/chapter/proving-numerical-bounds/how-to-bound-a-polynomial-on-the-whole-circle) uses packed rows to check a coefficient bound.

### How to speed up a program you do not own

`kernel_twin` follows a function's definitions, rewrites their bodies, and produces an equality with the original function. The following proof still states a property of `Their.check`. Only the computation uses its twin.

```lean standalone
import FloatLib.Tactic.KernelTwin
import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing

namespace Their

def check (xs : List Nat) : Bool := xs.length == 3

end Their

namespace Twin

kernel_twin Their.check

end Twin

example : Their.check [2, 3, 5] = true := by
  rw [Twin.Their.check.twin_eq]
  decide +kernel
```

By default the command stays within the current module. Use `kernel_twin Their.check within Their` to include imported definitions under that namespace. The `Plumbing` module supplies equations for operations on lists, arrays and options.

`kernel_twin` leaves `partial`, `opaque` and `unsafe` constants alone. It also preserves the program's data structures and algorithms. For example, repeated array pushes that reduce quadratically in the kernel still have that cost in the twin.
