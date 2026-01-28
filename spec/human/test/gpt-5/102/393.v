Require Import Coq.ZArith.ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition problem_102_pre (x y : Z) : Prop := x > 0 /\ y > 0.

Definition problem_102_spec (x y res : Z) : Prop :=
  ((exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
   (Z.even res = true /\ x <= res /\ res <= y /\ (forall z' : Z, res < z' /\ z' <= y -> Z.even z' = false)))
  /\
  ((~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
   res = -1).

Example problem_102_pre_holds_for_test :
  problem_102_pre 16 3.
Proof.
  unfold problem_102_pre; split; lia.
Qed.

Example problem_102_spec_holds_for_test :
  problem_102_spec 16 3 (-1).
Proof.
  unfold problem_102_spec.
  split.
  - intros [z [Hzx [Hzy Heven]]].
    exfalso.
    lia.
  - intros _.
    reflexivity.
Qed.