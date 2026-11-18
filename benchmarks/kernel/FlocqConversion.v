(**
  The three loops of [Loops.lean], checked by Coq 8.20.1 with Flocq 4.2.2.

  Each lemma is proved twice: by the kernel's ordinary conversion, which is what Lean's
  [decide +kernel] corresponds to, and through the bytecode VM, which Lean's kernel does not
  have. [Time Qed] prints the time of the kernel check.

  The binary64 operands are computed once by [vm_compute] and stored as lists, so that the
  measured conversions contain floating-point operations only.

  Run it in the benchmark container:
  docker run --rm --memory=8g --cpus=2 -v DIR:/work -w /work leanfloat-flocq-bench:4.2.2 \
    bash -lc 'coqc FlocqConversion.v'
*)

From Coq Require Import ZArith List.
From Flocq Require Import IEEE754.BinarySingleNaN IEEE754.Binary IEEE754.Bits.
Open Scope Z_scope.

(* binary32 0.1, from its bit pattern *)
Definition tenth : binary32 := b32_of_bits 1036831949.

(* add 0.1 to s, n times, rounding to nearest even each time *)
Fixpoint sumTenth (n : nat) (s : binary32) : binary32 :=
  match n with O => s | S k => sumTenth k (b32_plus mode_NE s tenth) end.

Definition rtenth (n : nat) : Z := bits_of_b32 (sumTenth n (b32_of_bits 0)).

(* The encoding of the i-th binary64 operand of stream k, as [operand] in Loops.lean. *)
Definition operand (k i : Z) : Z :=
  ((i / 3) mod 2) * 9223372036854775808
  + (1019 + ((i * 7 + k) mod 9)) * 4503599627370496
  + (((i + k * 1000) * 6364136223846793005 + 1442695040888963407) mod 4503599627370496).

Fixpoint indices (n : nat) (i : Z) : list Z :=
  match n with O => nil | S m => i :: indices m (i + 1) end.

Definition xs : list Z := Eval vm_compute in map (operand 0) (indices 1000 0).
Definition ys : list Z := Eval vm_compute in map (operand 1) (indices 1000 0).

(* Sum of the operands, left to right, nearest even. *)
Fixpoint sum64 (l : list Z) (s : binary64) : binary64 :=
  match l with
  | nil => s
  | x :: t => sum64 t (b64_plus mode_NE s (b64_of_bits x))
  end.

(* Dot product of two operand lists, without FMA. *)
Fixpoint dot64 (l m : list Z) (s : binary64) : binary64 :=
  match l, m with
  | x :: t, y :: u =>
      dot64 t u (b64_plus mode_NE s (b64_mult mode_NE (b64_of_bits x) (b64_of_bits y)))
  | _, _ => s
  end.

Definition rsum : Z := bits_of_b64 (sum64 xs (b64_of_bits 0)).
Definition rdot : Z := bits_of_b64 (dot64 xs ys (b64_of_bits 0)).

(* The kernel's ordinary conversion. *)
Lemma tenth_kernel : rtenth 1000 = 1120403331.
Proof. exact_no_check (eq_refl 1120403331). Time Qed.

Lemma sum_kernel : rsum = 13851123079082828159.
Proof. exact_no_check (eq_refl 13851123079082828159). Time Qed.

Lemma dot_kernel : rdot = 4676214714831268436.
Proof. exact_no_check (eq_refl 4676214714831268436). Time Qed.

(* The kernel's bytecode VM. *)
Lemma tenth_vm : rtenth 1000 = 1120403331.
Proof. vm_cast_no_check (eq_refl 1120403331). Time Qed.

Lemma sum_vm : rsum = 13851123079082828159.
Proof. vm_cast_no_check (eq_refl 13851123079082828159). Time Qed.

Lemma dot_vm : rdot = 4676214714831268436.
Proof. vm_cast_no_check (eq_refl 4676214714831268436). Time Qed.
