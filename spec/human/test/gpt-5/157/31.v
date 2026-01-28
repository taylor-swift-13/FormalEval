Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_6_8_13 : problem_157_spec 6%Z 8%Z 13%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H.
    exfalso.
    discriminate H.
  - intros H.
    cbv in H.
    destruct H as [H|[H|H]]; exfalso; lia.
Qed.