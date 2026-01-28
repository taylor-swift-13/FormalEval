Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_16_76_2020 : problem_157_spec 16%Z 76%Z 2020%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    cbv in H.
    destruct H as [H1 | [H2 | H3]].
    + assert (6032%Z <> 4080400%Z) by lia. contradiction.
    + assert (4080656%Z <> 5776%Z) by lia. contradiction.
    + assert (4086176%Z <> 256%Z) by lia. contradiction.
Qed.