Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_3_5_21 : problem_157_spec 3%Z 5%Z 21%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso.
    destruct H as [H | [H | H]].
    + assert ((3 * 3 + 5 * 5) < (21 * 21))%Z by (cbv; lia).
      rewrite H in H0. lia.
    + assert ((3 * 3 + 21 * 21) > (5 * 5))%Z by (cbv; lia).
      rewrite H in H0. lia.
    + assert ((5 * 5 + 21 * 21) > (3 * 3))%Z by (cbv; lia).
      rewrite H in H0. lia.
Qed.