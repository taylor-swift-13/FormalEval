Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_496_10000_10000 : problem_157_spec 496%Z 10000%Z 10000%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate.
  - intros H.
    exfalso.
    destruct H as [H|[H|H]].
    + rewrite <- (Z.add_0_l (10000 * 10000)%Z) in H.
      apply Z.add_cancel_r in H.
      cbv in H.
      lia.
    + rewrite <- (Z.add_0_l (10000 * 10000)%Z) in H.
      apply Z.add_cancel_r in H.
      cbv in H.
      lia.
    + cbv in H.
      lia.
Qed.