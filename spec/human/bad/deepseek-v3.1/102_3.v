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

Lemma example_proof : problem_102_spec 33 12354 12354.
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
           assert (H_z' : z' = 12354) by lia.
           subst z'.
           compute.
           reflexivity.
  - intro H_no_even.
    assert (H_even_exists : exists z : Z, 33 <= z /\ z <= 12354 /\ Z.even z = true).
    {
      exists 34.
      split; [lia|].
      split; [lia|].
      simpl.
      reflexivity.
    }
    apply H_no_even in H_even_exists.
    destruct H_even_exists as [z [H_range H_even]].
    assert (H_z : z = 34) by (apply Z.mod_pow2_eq; assumption).
    subst z.
    specialize (H_even_exists).
    exfalso.
    (* We now show that evenness at z=34 should be false, contradicting earlier assumption *)
    rewrite H_even in H_even.
    discriminate.
Qed.