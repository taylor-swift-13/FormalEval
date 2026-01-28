Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_12_383_37 : problem_157_spec 12%Z 383%Z 37%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intro H. exfalso. discriminate H.
  - intro H. exfalso.
    destruct H as [H|[H|H]].
    + assert (383 * 383 > 37 * 37) by (cbv; lia).
      rewrite <- H in H0. cbv in H0. lia.
    + assert (383 * 383 > 12 * 12 + 37 * 37) by (cbv; lia).
      rewrite H in H0. cbv in H0. lia.
    + assert (383 * 383 + 37 * 37 > 12 * 12) by (cbv; lia).
      rewrite H in H0. cbv in H0. lia.
Qed.