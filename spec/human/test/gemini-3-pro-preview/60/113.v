Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

(* Pre: no special constraints for `sum_to_n` *)
Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

Example test_problem_60 : problem_60_pre (Z.to_nat 499999%Z) -> problem_60_spec (Z.to_nat 499999%Z) (Z.to_nat 124999750000%Z).
Proof.
  intros H.
  unfold problem_60_spec.
  zify.
  lia.
Qed.