Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_13_14_15 : problem_157_spec 13%Z 14%Z 15%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H; exfalso; discriminate.
  - intros H; destruct H as [H|[H|H]];
    [ assert (13%Z * 13%Z + 14%Z * 14%Z <> 15%Z * 15%Z) by lia; contradiction
    | assert (13%Z * 13%Z + 15%Z * 15%Z <> 14%Z * 14%Z) by lia; contradiction
    | assert (14%Z * 14%Z + 15%Z * 15%Z <> 13%Z * 13%Z) by lia; contradiction ].
Qed.