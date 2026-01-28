Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_384_385_11 : problem_157_spec 384%Z 385%Z 11%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. destruct H as [H|[H|H]]; cbv in H.
    + assert (295681%Z <> 121%Z) by lia. congruence.
    + assert (147577%Z <> 148225%Z) by lia. congruence.
    + assert (148346%Z <> 147456%Z) by lia. congruence.
Qed.