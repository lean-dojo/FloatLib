(**
  We include Flocq because it gives us an independent, proved binary
  floating-point reference:
  https://flocq.gitlabpages.inria.fr/

  We keep Flocq's precision proofs in Rocq and extract only the small OCaml
  surface needed by the benchmark. Precision, exponent bounds, nearest-even
  rounding, and subnormal behavior match the corresponding FloatLib and MPFR
  rows. Exact rational fixtures are rounded once before timing. We compare
  arithmetic values; this single-NaN interface does not preserve NaN payloads.
*)

From Coq Require Import ZArith Extraction ExtrOcamlBasic ExtrOcamlZBigInt.
From Flocq Require Import Core.FLX IEEE754.BinarySingleNaN.

Open Scope Z_scope.

Definition flocq_make
    (prec emax : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec emax)
    (sign : bool)
    (mantissa exponent : Z) :
    binary_float prec emax :=
  binary_normalize prec emax prec_gt_0_ prec_lt_emax_
    mode_NE (if sign then -mantissa else mantissa) exponent sign.

Definition flocq_add
    (prec emax : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec emax)
    (x y : binary_float prec emax) :
    binary_float prec emax :=
  @Bplus prec emax prec_gt_0_ prec_lt_emax_ mode_NE x y.

Definition flocq_sub
    (prec emax : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec emax)
    (x y : binary_float prec emax) :
    binary_float prec emax :=
  @Bminus prec emax prec_gt_0_ prec_lt_emax_ mode_NE x y.

Definition flocq_mul
    (prec emax : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec emax)
    (x y : binary_float prec emax) :
    binary_float prec emax :=
  @Bmult prec emax prec_gt_0_ prec_lt_emax_ mode_NE x y.

Definition flocq_div
    (prec emax : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec emax)
    (x y : binary_float prec emax) :
    binary_float prec emax :=
  @Bdiv prec emax prec_gt_0_ prec_lt_emax_ mode_NE x y.

(** [Bdiv_correct_aux] rounds an exact quotient of integer significands. Its
    inputs need not first be rounded to the destination format. The resulting
    validity proof lets [SF2B] package the rounded quotient as a binary float. *)
Definition flocq_from_ratio
    (prec emax : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec emax)
    (sign : bool)
    (numerator denominator : positive) :
    binary_float prec emax :=
  SF2B _ (proj1
    (@Bdiv_correct_aux prec emax prec_gt_0_ prec_lt_emax_
      mode_NE sign numerator 0 false denominator 0)).

Definition flocq_sqrt
    (prec emax : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec emax)
    (x : binary_float prec emax) :
    binary_float prec emax :=
  @Bsqrt prec emax prec_gt_0_ prec_lt_emax_ mode_NE x.

Definition flocq_fma
    (prec emax : Z)
    (prec_gt_0_ : FLX.Prec_gt_0 prec)
    (prec_lt_emax_ : Prec_lt_emax prec emax)
    (x y z : binary_float prec emax) :
    binary_float prec emax :=
  @Bfma prec emax prec_gt_0_ prec_lt_emax_ mode_NE x y z.

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
