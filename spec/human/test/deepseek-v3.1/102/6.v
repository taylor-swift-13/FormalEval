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

Lemma example_proof : problem_102_spec 27 10 (-1).
Proof.
  unfold problem_102_spec.
  split.
  - intro H_ex.
    destruct H_ex as [z [Hx [Hy Heq]]].
    lia.
  - intro H_no_even.
    reflexivity.
Qed.