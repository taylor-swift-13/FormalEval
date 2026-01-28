Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_11_457_9 : problem_157_spec 11%Z 457%Z 9%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso.
    destruct H as [H | [H | H]]; cbv in H.
    + assert (81 < 208970)%Z by lia.
      rewrite H in H0.
      lia.
    + assert (202 < 208849)%Z by lia.
      rewrite H in H0.
      lia.
    + assert (121 < 208930)%Z by lia.
      rewrite H in H0.
      lia.
Qed.