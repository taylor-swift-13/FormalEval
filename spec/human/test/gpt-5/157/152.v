Require Import ZArith Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_120_12_15 : problem_157_spec 120%Z 12%Z 15%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso.
    destruct H as [H | [H | H]].
    + cbv in H.
      assert (14544 <> 225) by lia.
      apply H0 in H. contradiction.
    + cbv in H.
      assert (14625 <> 144) by lia.
      apply H0 in H. contradiction.
    + cbv in H.
      assert (369 <> 14400) by lia.
      apply H0 in H. contradiction.
Qed.