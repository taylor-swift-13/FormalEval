Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_12_10_10 : problem_157_spec 12%Z 10%Z 10%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso.
    destruct H as [H|[H|H]];
    [assert (12*12 + 10*10 <> 10*10)%Z by lia; contradiction
    |assert (12*12 + 10*10 <> 10*10)%Z by lia; contradiction
    |assert (10*10 + 10*10 <> 12*12)%Z by lia; contradiction].
Qed.