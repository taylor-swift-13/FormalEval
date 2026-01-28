Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_25_37_37 : problem_157_spec 25%Z 37%Z 37%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [H|[H|H]].
    + exfalso. cbv in H. assert (1994%Z <> 1369%Z) by lia. contradiction.
    + exfalso. cbv in H. assert (1994%Z <> 1369%Z) by lia. contradiction.
    + exfalso. cbv in H. assert (2738%Z <> 625%Z) by lia. contradiction.
Qed.