Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_15_13_13 : problem_157_spec 15%Z 13%Z 13%Z false.
Proof.
  unfold problem_157_spec.
  cbv.
  split.
  - intros H; discriminate.
  - intros [H|[H|H]]; exfalso; lia.
Qed.