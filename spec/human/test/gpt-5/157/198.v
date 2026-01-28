Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_10002_10001_10002 : problem_157_spec 10002%Z 10001%Z 10002%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [H|[H|H]]; cbv in H.
    + assert (200060005%Z <> 100040004%Z) by lia.
      exfalso; apply H0; exact H.
    + assert (200080008%Z <> 100020001%Z) by lia.
      exfalso; apply H0; exact H.
    + assert (200060005%Z <> 100040004%Z) by lia.
      exfalso; apply H0; exact H.
Qed.