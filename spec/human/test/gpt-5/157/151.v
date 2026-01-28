Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_11_119_120 : problem_157_spec 11%Z 119%Z 120%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. discriminate.
  - intros H.
    destruct H as [H|[H|H]].
    + cbv in H. assert (14282 < 14400)%Z by lia. exfalso. lia.
    + cbv in H. assert (14161 < 14521)%Z by lia. exfalso. lia.
    + cbv in H. assert (121 < 28561)%Z by lia. exfalso. lia.
Qed.