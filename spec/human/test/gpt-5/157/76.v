Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_5_5_5 : problem_157_spec 5%Z 5%Z 5%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. discriminate.
  - intros H.
    destruct H as [H1 | [H2 | H3]].
    + cbv in H1. lia.
    + cbv in H2. lia.
    + cbv in H3. lia.
Qed.