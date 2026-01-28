Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_12_4_21 : problem_157_spec 12%Z 4%Z 21%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H; exfalso; discriminate H.
  - intros H.
    destruct H as [H|[H|H]].
    + cbv in H.
      assert (160 <> 441) by lia.
      contradiction.
    + cbv in H.
      assert (585 <> 16) by lia.
      contradiction.
    + cbv in H.
      assert (457 <> 144) by lia.
      contradiction.
Qed.