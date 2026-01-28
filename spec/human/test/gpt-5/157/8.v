Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_15_8_17 : problem_157_spec 15%Z 8%Z 17%Z true.
Proof.
  unfold problem_157_spec.
  split; [ intros _; left; cbv; reflexivity | intros _; reflexivity ].
Qed.