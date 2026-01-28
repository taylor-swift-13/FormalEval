Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_455_399_456 : problem_157_spec 455%Z 399%Z 456%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. apply False_ind. discriminate H.
  - intros HP. apply False_ind. destruct HP as [H|[H|H]]; cbv in H; discriminate H.
Qed.