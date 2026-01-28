Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_12_35_138 : problem_157_spec 12%Z 35%Z 138%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros HP. exfalso.
    destruct HP as [H1 | H23].
    + cbv in H1. lia.
    + destruct H23 as [H2 | H3].
      * cbv in H2. lia.
      * cbv in H3. lia.
Qed.