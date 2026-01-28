Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for `sum_to_n` *)
Definition problem_60_pre (n : Z) : Prop := n > 0.

Definition problem_60_spec (n output: Z) : Prop :=
  2 * output = n * (n + 1).

Example test_problem_60 : problem_60_pre 532173 -> problem_60_spec 532173 141604317051.
Proof.
  intros H.
  unfold problem_60_spec.
  reflexivity.
Qed.