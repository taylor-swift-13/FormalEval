Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_60_pre (n : Z) : Prop := n > 0.

Definition problem_60_spec (n output: Z) : Prop :=
  2 * output = n*(n+1).

Example test_problem_60 : problem_60_pre 499992 -> problem_60_spec 499992 124996250028.
Proof.
  intros H.
  unfold problem_60_spec.
  reflexivity.
Qed.