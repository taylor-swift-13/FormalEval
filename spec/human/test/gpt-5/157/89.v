Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_16_8_19 : problem_157_spec 16%Z 8%Z 19%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H.
    exfalso.
    cbv in H.
    destruct H as [H|[H|H]];
    [assert (320 <> 361) by lia; contradiction
    |assert (617 <> 64) by lia; contradiction
    |assert (425 <> 256) by lia; contradiction].
Qed.