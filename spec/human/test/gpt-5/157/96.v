Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example problem_157_test_20_21_20 : problem_157_spec 20%Z 21%Z 20%Z false.
Proof.
  unfold problem_157_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros H. exfalso.
    destruct H as [H|[H|H]]; cbv in H;
    [ assert (841 <> 400)%Z by lia; apply H0 in H; exact H
    | assert (800 <> 441)%Z by lia; apply H0 in H; exact H
    | assert (841 <> 400)%Z by lia; apply H0 in H; exact H ].
Qed.