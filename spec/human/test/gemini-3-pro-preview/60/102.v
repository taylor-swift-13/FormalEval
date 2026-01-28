Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for `sum_to_n` *)
Definition problem_60_pre (n : Z) : Prop := n > 0.

Definition problem_60_spec (n output: Z) : Prop :=
  2 * output = n*(n+1).

Example test_problem_60 : problem_60_pre 500000 -> problem_60_spec 500000 125000250000.
Proof.
  intros H.
  unfold problem_60_spec.
  simpl.
  reflexivity.
Qed.