Require Import Coq.Arith.Arith.

(* Pre: no special constraints for `sum_to_n` *)
Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

Example test_problem_60 : problem_60_pre 45 -> problem_60_spec 45 1035.
Proof.
  intros H.
  unfold problem_60_spec.
  reflexivity.
Qed.