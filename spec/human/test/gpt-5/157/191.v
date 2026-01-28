Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_25_24_65 : problem_157_spec 25%Z 24%Z 65%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso. destruct H as [H1 | [H2 | H3]]; cbv in *; lia.
Qed.