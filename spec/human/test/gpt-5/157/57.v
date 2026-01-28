Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_9_8_13 : problem_157_spec 9%Z 8%Z 13%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. inversion H.
  - intros H.
    exfalso.
    destruct H as [H|[H|H]].
    + assert (9 * 9 + 8 * 8 <> 13 * 13) by lia. contradiction.
    + assert (9 * 9 + 13 * 13 <> 8 * 8) by lia. contradiction.
    + assert (8 * 8 + 13 * 13 <> 9 * 9) by lia. contradiction.
Qed.