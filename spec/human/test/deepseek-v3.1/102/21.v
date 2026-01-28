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

Lemma example_proof : problem_102_spec 101 6 (-1).
Proof.
  unfold problem_102_spec.
  split.
  - intro H_ex.
    exfalso.
    destruct H_ex as [z [H_xz [H_zy H_even]]].
    assert (H_z_dim : z >= 101 /\ z <= 6) by lia.
    destruct H_z_dim as [H_z_min H_z_max].
    lia.
  - intro H_no_even.
    reflexivity.
Qed.