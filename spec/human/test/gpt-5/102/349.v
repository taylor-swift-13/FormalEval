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
  problem_102_pre 100 11.
Proof.
  unfold problem_102_pre; split; lia.
Qed.

Example problem_102_spec_holds_for_test :
  problem_102_spec 100 11 (-1).
Proof.
  unfold problem_102_spec.
  split.
  - intros Hex.
    destruct Hex as [z [Hz1 [Hz2 Hev]]].
    exfalso.
    assert (100 <= 11) by (apply (Z.le_trans 100 z 11); [exact Hz1 | exact Hz2]).
    assert (100 > 11) by lia.
    lia.
  - intros _.
    reflexivity.
Qed.