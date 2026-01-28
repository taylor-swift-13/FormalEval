Require Import Coq.ZArith.ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition problem_102_pre (x y : Z) : Prop := x > 0 /\ y > 0.

Definition problem_102_spec (x y res : Z) : Prop :=
  ( (exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (Z.even res = true /\ x <= res /\ res <= y /\ (forall z' : Z, res < z' /\ z' <= y -> Z.even z' = false)) )
  /\
  ( (~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    res = -1 ).

Example test_problem_102 : problem_102_spec 29 30 30.
Proof.
  unfold problem_102_spec.
  split.
  - intros _.
    split.
    + simpl. reflexivity.
    + split.
      * lia.
      * split.
        -- lia.
        -- intros z' [Hlt Hle].
           lia.
  - intros Hne.
    exfalso.
    apply Hne.
    exists 30.
    split; [lia | split; [lia | simpl; reflexivity]].
Qed.