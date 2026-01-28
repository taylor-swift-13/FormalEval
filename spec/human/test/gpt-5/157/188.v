Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_10_384_13 : problem_157_spec 10%Z 384%Z 13%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    exfalso.
    destruct H as [H | [H | H]].
    + cbv in H.
      assert (147556 > 169)%Z by lia.
      rewrite H in H0.
      lia.
    + cbv in H.
      assert (269 < 147456)%Z by lia.
      rewrite H in H0.
      lia.
    + cbv in H.
      assert (147625 > 100)%Z by lia.
      rewrite H in H0.
      lia.
Qed.