Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_65_10000_10001 : problem_157_spec 65%Z 10000%Z 10001%Z false.
Proof.
  unfold problem_157_spec.
  split; [ intros H; exfalso; discriminate H | intros _; discriminate ].
Qed.