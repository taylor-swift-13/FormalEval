Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_17_8_20 : problem_157_spec 17%Z 8%Z 20%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. cbv in H. destruct H as [H|[H|H]].
    + assert (353%Z <> 400%Z) by lia. contradiction.
    + assert (689%Z <> 64%Z) by lia. contradiction.
    + assert (464%Z <> 289%Z) by lia. contradiction.
Qed.