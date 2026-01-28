Require Import Coq.Arith.Arith.

(* Pre: no special constraints for `sum_to_n` *)
Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

Example test_problem_60 : problem_60_pre 90 -> problem_60_spec 90 4095.
Proof.
  intros H.
  unfold problem_60_spec.
  reflexivity.
Qed.