Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_22_13_21 : problem_157_spec 22%Z 13%Z 21%Z false.
Proof.
  unfold problem_157_spec.
  split; [ intros H; exfalso; discriminate H | intros H; exfalso; cbv in H; destruct H as [H|[H|H]]; congruence ].
Qed.