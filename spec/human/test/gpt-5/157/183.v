Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_10_76_2022 : problem_157_spec 10%Z 76%Z 2022%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H; discriminate.
  - intros H; exfalso; destruct H as [H|[H|H]].
    + assert (10*10 + 76*76 < 2022*2022) by (vm_compute; lia). rewrite H in H0. lia.
    + assert (10*10 + 2022*2022 > 76*76) by (vm_compute; lia). rewrite H in H0. lia.
    + assert (76*76 + 2022*2022 > 10*10) by (vm_compute; lia). rewrite H in H0. lia.
Qed.