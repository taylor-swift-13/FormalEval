Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_14_10001_2022 : problem_157_spec 14%Z 10001%Z 2022%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intro H. discriminate H.
  - intros HP.
    exfalso.
    destruct HP as [H | [H | H]].
    + cbv in H.
      assert (100020197%Z > 4088484%Z) as H0 by lia.
      rewrite H in H0.
      lia.
    + cbv in H.
      assert (100020001%Z > 4088680%Z) as H0 by lia.
      rewrite H in H0.
      lia.
    + cbv in H.
      assert (104108485%Z > 196%Z) as H0 by lia.
      rewrite H in H0.
      lia.
Qed.