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

Example test_problem_102 : problem_102_spec 21 16 (-1).
Proof.
  unfold problem_102_spec.
  split.
  - intros Hex.
    exfalso.
    destruct Hex as [z [Hle1 [Hle2 Heven]]].
    lia.
  - intros _.
    reflexivity.
Qed.