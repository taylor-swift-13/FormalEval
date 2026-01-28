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

Example test_problem_102 : problem_102_spec 1000000 1000001 1000000.
Proof.
  unfold problem_102_spec.
  split.
  - intros _.
    split.
    + reflexivity.
    + split.
      * lia.
      * split.
        -- lia.
        -- intros z' [Hlt Hle].
           assert (z' = 1000001) by lia.
           subst z'.
           reflexivity.
  - intros Hne.
    exfalso.
    apply Hne.
    exists 1000000.
    split; [lia | split; [lia | reflexivity]].
Qed.