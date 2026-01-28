Require Import Coq.ZArith.ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition problem_102_pre (x y : Z) : Prop := x > 0 /\ y > 0.

Definition problem_102_spec (x y res : Z) : Prop :=
  ( (exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (Z.even res = true/\ x <= res /\ res <= y /\ (forall z' : Z, res < z' /\ z' <= y ->  Z.even z' = false)) )
  /\
  ( (~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    res = -1 ).

Example problem_102_pre_holds_for_test :
  problem_102_pre 2 20.
Proof.
  unfold problem_102_pre; split; lia.
Qed.

Example problem_102_spec_holds_for_test :
  problem_102_spec 2 20 20.
Proof.
  unfold problem_102_spec.
  split.
  - intros _.
    split.
    + now compute.
    + split; [lia|].
      split; [lia|].
      intros z' [Hlt Hle].
      exfalso; lia.
  - intros Hnone.
    exfalso.
    apply Hnone.
    exists 20.
    repeat split; try lia; now compute.
Qed.