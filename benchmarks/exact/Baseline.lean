/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Harness
import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime
import FloatLib.Numerics.Enclosure.Interval.Elementary
import FloatLib.Numerics.Enclosure.Constants.Runtime
import FloatLib.Numerics.Enclosure.Expression.Backends
import FloatLib.Numerics.Enclosure.Expression.Check
import FloatLib.Numerics.Enclosure.Expression.Extensions
import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime
import FloatLib.Numerics.Exact.Dyadic.Comparison.Runtime
import FloatLib.Numerics.Exact.IntegerRoot.Runtime

/-!
# Kernel cost of FloatLib's own exact layer

Every row uses only definitions outside `FloatLib.Numerics.Kernel`: the dyadic numbers of
`Numerics/Exact`, the fixed-point intervals `BinaryGrid`, the rational and the grid enclosures of
the elementary functions, the constants, the integer roots, and the bound of a logarithm and of
an exponential on the grid. `benchmarks/exact/run.sh baseline` runs this file and writes
`benchmarks/results/exact/baseline.md`.
-/

open FloatLibBenchmarks.Exact
open FloatLib.Numerics FloatLib.Numerics.Interval

/-! ## Dyadic numbers: core Lean's `Dyadic` and FloatLib's sign, significand and exponent -/
#kernel_op "dyadic/core a + b" (sizes := [64, 1024, 4096]) (count := 8) fun a b : Nat =>
  ((_root_.Dyadic.ofIntWithPrec (Int.ofNat a) 17 + _root_.Dyadic.ofIntWithPrec (Int.negSucc b) 5).toRat).den
#kernel_op "dyadic/core a * b" (sizes := [64, 1024, 4096]) (count := 8) fun a b : Nat =>
  ((_root_.Dyadic.ofIntWithPrec (Int.ofNat a) 17 * _root_.Dyadic.ofIntWithPrec (Int.negSucc b) 5).toRat).den
#kernel_op "dyadic/FloatLib add" (sizes := [64, 1024, 4096, 16384]) (count := 8) fun a b : Nat =>
  (FloatLib.Numerics.Dyadic.add ⟨false, a, Int.negSucc 2⟩ ⟨true, b, Int.ofNat 5⟩).significand
#kernel_op "dyadic/FloatLib mul" (sizes := [64, 1024, 4096, 16384]) (count := 8) fun a b : Nat =>
  (FloatLib.Numerics.Dyadic.mul ⟨false, a, Int.negSucc 2⟩ ⟨true, b, Int.ofNat 5⟩).significand
#kernel_op "dyadic/FloatLib isLess" (sizes := [64, 1024, 4096, 16384]) (count := 8) fun a b : Nat =>
  FloatLib.Numerics.Dyadic.isLess ⟨false, a, Int.negSucc 2⟩ ⟨false, b, Int.ofNat 5⟩

/-! ## Fixed-point intervals (`BinaryGrid`), 64 fractional bits -/
#kernel_op "grid/add" (sizes := [64, 1024, 4096, 16384]) (count := 16) fun a b c d : Nat =>
  (BinaryGrid.add ⟨Int.negSucc a, Int.ofNat b⟩ ⟨Int.ofNat c, Int.ofNat (c + d)⟩).hi.natAbs
#kernel_op "grid/sub" (sizes := [64, 1024, 4096, 16384]) (count := 16) fun a b c d : Nat =>
  (BinaryGrid.sub ⟨Int.negSucc a, Int.ofNat b⟩ ⟨Int.ofNat c, Int.ofNat (c + d)⟩).hi.natAbs
#kernel_op "grid/mul" (sizes := [64, 1024, 4096, 16384]) (count := 16) fun a b c d : Nat =>
  (BinaryGrid.mul 64 ⟨Int.negSucc a, Int.ofNat b⟩ ⟨Int.ofNat c, Int.ofNat (c + d)⟩).hi.natAbs
#kernel_op "grid/square" (sizes := [64, 1024, 4096, 16384]) (count := 16) fun a b : Nat =>
  (BinaryGrid.square 64 ⟨Int.negSucc a, Int.ofNat b⟩).hi.natAbs
#kernel_op "grid/abs" (sizes := [64, 1024, 4096, 16384]) (count := 16) fun a b : Nat =>
  (BinaryGrid.abs ⟨Int.negSucc a, Int.ofNat b⟩).hi.natAbs
#kernel_op "grid/div?" (sizes := [64, 1024, 4096, 16384]) (count := 16) fun a b c d : Nat =>
  ((BinaryGrid.div? 64 ⟨Int.negSucc a, Int.ofNat b⟩ ⟨Int.ofNat c, Int.ofNat (c + d)⟩).map fun I => I.hi.natAbs).getD 0
#kernel_op "grid/pow 7" (sizes := [64, 1024, 4096]) (count := 4) fun a b : Nat =>
  (BinaryGrid.pow 64 ⟨Int.negSucc a, Int.ofNat b⟩ 7).hi.natAbs
#kernel_op "grid/divideNat" (sizes := [64, 1024, 4096, 16384]) (count := 16) fun a b : Nat =>
  (Enclosure.BinaryGrid.divideNat ⟨Int.negSucc a, Int.ofNat b⟩ 12345).hi.natAbs
#kernel_op "grid/enclose" (sizes := [64, 1024, 4096]) (count := 8) fun a b : Nat =>
  (BinaryGrid.enclose 64 (mkRat (Int.ofNat a) b)).hi.natAbs

/-! ## Elementary functions on the grid: `x = 1431655765 / 2 ^ 32`, degree 20; the size is the precision -/
def third : ℚ := mkRat 1431655765 4294967296
#kernel_op "elementary/grid exp" (sizes := [64, 256, 1024, 4096]) (count := 2) (reps := 1) fun p : Nat =>
  ((Enclosure.BinaryGrid.exp third 20 (Nat.log2 p + 1)).hi.num).natAbs
#kernel_op "elementary/grid log" (sizes := [64, 256, 1024, 4096]) (count := 2) (reps := 1) fun p : Nat =>
  ((Enclosure.BinaryGrid.log third 20 (Nat.log2 p + 1)).hi.num).natAbs

/-! ## Rational enclosures at `1/3` and `4/3`, degrees 12, 20 and 40 -/
def small : ℚ := mkRat 1 3
def near : ℚ := mkRat 4 3
#kernel_term "elementary/rational exp (1/3), degree 12" (reps := 2) id (Enclosure.exp small 12).hi.num.natAbs
#kernel_term "elementary/rational exp (1/3), degree 20" (reps := 2) id (Enclosure.exp small 20).hi.num.natAbs
#kernel_term "elementary/rational exp (1/3), degree 40" (reps := 2) id (Enclosure.exp small 40).hi.num.natAbs
#kernel_term "elementary/rational log (4/3), degree 12" (reps := 2) id (Enclosure.log near 12).hi.num.natAbs
#kernel_term "elementary/rational log (4/3), degree 20" (reps := 2) id (Enclosure.log near 20).hi.num.natAbs
#kernel_term "elementary/rational log (4/3), degree 40" (reps := 2) id (Enclosure.log near 40).hi.num.natAbs
#kernel_term "elementary/rational sin (1/3), degree 12" (reps := 2) id (Enclosure.sin small 12).hi.num.natAbs
#kernel_term "elementary/rational sin (1/3), degree 20" (reps := 2) id (Enclosure.sin small 20).hi.num.natAbs
#kernel_term "elementary/rational sin (1/3), degree 40" (reps := 2) id (Enclosure.sin small 40).hi.num.natAbs
#kernel_term "elementary/rational cos (1/3), degree 20" (reps := 2) id (Enclosure.cos small 20).hi.num.natAbs
#kernel_term "elementary/rational atan (1/3), degree 12" (reps := 2) id (Enclosure.atan small 12).hi.num.natAbs
#kernel_term "elementary/rational atan (1/3), degree 20" (reps := 2) id (Enclosure.atan small 20).hi.num.natAbs

/-! ## Square root bounds and the constants; the size is the number of fractional bits -/
#kernel_op "elementary/sqrt bounds" (sizes := [64, 256, 1024]) (count := 2) (reps := 1) fun p : Nat =>
  ((Interval.sqrtPointBounds third (Nat.log2 p + 1)).hi.num).natAbs
#kernel_op "elementary/pi" (sizes := [64, 256, 1024]) (count := 2) (reps := 1) fun p : Nat =>
  (Enclosure.Constants.piLevel (Nat.log2 p + 1)).halfPi
#kernel_op "elementary/log 2" (sizes := [64, 256, 1024]) (count := 2) (reps := 1) fun p : Nat =>
  Enclosure.Constants.ln2Fixed (Nat.log2 p + 1)

/-! ## One operation of the grid backend of the `interval` tactic, default precision and degree -/
def lower : Int := Int.ofNat 1801439850948198
def upper : Int := Int.ofNat 3377699720527872
/-- Ten, and ten plus `2 ^ (-54)`, in units of `2 ^ (-64)`. -/
def lowerTen : Int := Int.ofNat 184467440737095516160
def upperTen : Int := Int.ofNat 184467440737095517184
#kernel_term "backend/exp" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .exp ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/log" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .log ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/sin" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .sin ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/cos" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .cos ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/sqrt" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .sqrt ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/atan" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .atan ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/tan" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .tan ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/sinh" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .sinh ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/cosh" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .cosh ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/tanh" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .tanh ⟨lower, upper⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/sin, argument near 10" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .sin ⟨lowerTen, upperTen⟩).map fun I => I.hi.natAbs) 0)
#kernel_term "backend/log, argument near 10" id (Option.getD (((Interval.Backend.binaryGrid {}).unary? .log ⟨lowerTen, upperTen⟩).map fun I => I.hi.natAbs) 0)

/-! ## Integer roots -/
#kernel_op "root/IntegerRoot.newton 2" (sizes := [64, 1024, 4096]) (count := 2) (reps := 1) fun a : Nat =>
  FloatLib.Numerics.IntegerRoot.newton 2 a
#kernel_op "root/IntegerRoot.newton 3" (sizes := [64, 1024, 4096]) (count := 2) (reps := 1) fun a : Nat =>
  FloatLib.Numerics.IntegerRoot.newton 3 a

/-! ## An upper bound of a logarithm and of an exponential on the grid -/
def anchor : ℚ := mkRat 7 5
#kernel_term "bound/log (7/5) ≤ 0.3365, degree 18, 64 bits" (reps := 1)
  decide ((Enclosure.BinaryGrid.log anchor 18 64).hi ≤ mkRat 3365 10000)
#kernel_term "bound/log (7/5), degree 40, 192 bits" (reps := 1)
  ((Enclosure.BinaryGrid.log anchor 40 192).hi.num).natAbs
#kernel_term "bound/exp (7/5) ≤ 4.0553, degree 20, 64 bits" (reps := 1)
  decide ((Enclosure.BinaryGrid.exp anchor 20 64).hi ≤ mkRat 40553 10000)
#kernel_term "bound/exp (7/5), degree 40, 192 bits" (reps := 1)
  ((Enclosure.BinaryGrid.exp anchor 40 192).hi.num).natAbs

/-! ## The checker of the `interval` tactic on `x * (1 - x) ≤ 13/50`, `x` in `[0, 1]` -/
/-- `x * (1 - x) - 13/50`, as the tactic reifies it. -/
def parabola : Expr :=
  Expr.binary BinaryOp.sub
    (Expr.binary BinaryOp.mul (Expr.var 0)
      (Expr.binary BinaryOp.sub (Expr.const (mkRat (Int.ofNat 1) 1)) (Expr.var 0)))
    (Expr.const (mkRat (Int.ofNat 13) 50))
/-- The grid backend with no registered functions, as the tactic builds it. -/
def gridBackend : Backend Int := Backend.binaryGrid.withExtensions { } []
/-- The unit interval. -/
def unitBox : Box := [{ lo := mkRat (Int.ofNat 0) 1, hi := mkRat (Int.ofNat 1) 1 }]
#kernel_term "checker/the whole check, depth 8 (35 boxes)" id
  (Bool.rec 0 1 (parabola.check gridBackend Relation.nonpositive unitBox 8) : Nat)
#kernel_op "checker/one evaluation of the expression" (sizes := [60]) (count := 32) fun a b : Nat =>
  Option.getD ((parabola.eval? gridBackend
    (fun i => [(⟨Int.ofNat a, Int.ofNat (Nat.add a b)⟩ : Interval Int)][i]?)).map
      fun I => I.hi.natAbs) 0
#kernel_op "checker/one box" (sizes := [60]) (count := 32) fun a b : Nat =>
  (Bool.rec 0 1 (parabola.checkBox gridBackend Relation.nonpositive
    [⟨mkRat (Int.ofNat a) 1152921504606846976,
      mkRat (Int.ofNat (Nat.add a b)) 1152921504606846976⟩]) : Nat)
#kernel_op "checker/one bisection" (sizes := [60]) (count := 32) fun a b : Nat =>
  Option.getD ((Box.bisect?
    [⟨mkRat (Int.ofNat a) 1152921504606846976, mkRat (Int.ofNat (Nat.add a b)) 1152921504606846976⟩]).map
      fun p => (p.1.headD ⟨0, 0⟩).hi.den + (p.2.headD ⟨0, 0⟩).lo.den) 0
