Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_20_23_5 : problem_157_spec 20%Z 23%Z 5%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros HP. exfalso.
    cbv in HP.
    destruct HP as [H|[H|H]]; lia.
Qed.