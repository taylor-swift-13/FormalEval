Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_13_16_20 : problem_157_spec 13%Z 16%Z 20%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso.
    cbv in H.
    destruct H as [H|[H|H]].
    + assert (425 <> 400)%Z by lia. contradiction.
    + assert (569 <> 256)%Z by lia. contradiction.
    + assert (656 <> 169)%Z by lia. contradiction.
Qed.