Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_2019_2019_2019 : problem_157_spec 2019%Z 2019%Z 2019%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intro H; exfalso; discriminate H.
  - intro HP; exfalso; destruct HP as [H|[H|H]];
    rewrite <- Z.add_0_l in H;
    apply Z.add_cancel_r in H;
    apply Z.mul_eq_0 in H;
    destruct H; discriminate.
Qed.