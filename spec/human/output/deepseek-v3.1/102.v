Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition problem_102_pre (x y : Z) : Prop := x > 0 /\ y > 0.

Definition problem_102_spec (x y res : Z) : Prop :=
  ( (exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (Z.even res = true /\ x <= res /\ res <= y /\ 
     (forall z' : Z, res < z' /\ z' <= y -> Z.even z' = false)) )
  /\
  ( (~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    res = -1 ).

Lemma example_proof : problem_102_spec 12 15 14.
Proof.
  unfold problem_102_spec.
  split.
  - intro H_ex.
    split.
    + compute. reflexivity.
    + split.
      * lia.
      * split.
        -- lia.
        -- intro z'.
           intros [H_lt H_le].
           assert (H_z' : z' = 15) by lia.
           subst z'.
           compute.
           reflexivity.
  - intro H_no_even.
    exfalso.
    apply H_no_even.
    exists 14.
    split; [lia|].
    split; [lia|].
    compute.
    reflexivity.
Qed.