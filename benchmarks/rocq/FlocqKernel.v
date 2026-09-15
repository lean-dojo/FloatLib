(**
  We include Flocq because it gives us an independent, proved binary
  floating-point reference:
  https://flocq.gitlabpages.inria.fr/

  We keep Flocq's precision proofs in Rocq and extract only the small OCaml
  surface needed by the benchmark. We use nearest-even rounding and a generous
  exponent range so significand precision is the variable. The row compares
  arithmetic cost; it does not claim the same exponent range or
  exceptional-value policy as every FloatLib descriptor.
*)

From Coq Require Import ZArith Extraction ExtrOcamlBasic ExtrOcamlZBigInt.
From Flocq Require Import Core.FLX IEEE754.BinarySingleNaN.

Open Scope Z_scope.

Definition benchmark_emax : Z := 16384.

Definition flocq_make
    (prec : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec benchmark_emax)
    (sign : bool)
    (mantissa exponent : Z) :
    binary_float prec benchmark_emax :=
  binary_normalize prec benchmark_emax prec_gt_0_ prec_lt_emax_
    mode_NE (if sign then -mantissa else mantissa) exponent sign.

Definition flocq_add
    (prec : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec benchmark_emax)
    (x y : binary_float prec benchmark_emax) :
    binary_float prec benchmark_emax :=
  @Bplus prec benchmark_emax prec_gt_0_ prec_lt_emax_ mode_NE x y.

Definition flocq_sub
    (prec : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec benchmark_emax)
    (x y : binary_float prec benchmark_emax) :
    binary_float prec benchmark_emax :=
  @Bminus prec benchmark_emax prec_gt_0_ prec_lt_emax_ mode_NE x y.

Definition flocq_mul
    (prec : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec benchmark_emax)
    (x y : binary_float prec benchmark_emax) :
    binary_float prec benchmark_emax :=
  @Bmult prec benchmark_emax prec_gt_0_ prec_lt_emax_ mode_NE x y.

Definition flocq_div
    (prec : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec benchmark_emax)
    (x y : binary_float prec benchmark_emax) :
    binary_float prec benchmark_emax :=
  @Bdiv prec benchmark_emax prec_gt_0_ prec_lt_emax_ mode_NE x y.

Definition flocq_from_ratio
    (prec : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec benchmark_emax)
    (sign : bool)
    (numerator denominator : Z) :
    binary_float prec benchmark_emax :=
  flocq_div prec prec_gt_0_ prec_lt_emax_
    (flocq_make prec prec_gt_0_ prec_lt_emax_ sign numerator 0)
    (flocq_make prec prec_gt_0_ prec_lt_emax_ false denominator 0).

Definition flocq_sqrt
    (prec : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec benchmark_emax)
    (x : binary_float prec benchmark_emax) :
    binary_float prec benchmark_emax :=
  @Bsqrt prec benchmark_emax prec_gt_0_ prec_lt_emax_ mode_NE x.

Definition flocq_fma
    (prec : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec benchmark_emax)
    (x y z : binary_float prec benchmark_emax) :
    binary_float prec benchmark_emax :=
  @Bfma prec benchmark_emax prec_gt_0_ prec_lt_emax_ mode_NE x y z.

Extraction Language OCaml.
Set Extraction Optimize.

Extraction "flocq_kernel.ml"
  flocq_make
  flocq_add
  flocq_sub
  flocq_mul
  flocq_div
  flocq_from_ratio
  flocq_sqrt
  flocq_fma.
