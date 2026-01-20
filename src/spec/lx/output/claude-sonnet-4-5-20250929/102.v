Require Import Coq.ZArith.ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y res : Z) : Prop :=
  ( (exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    (Z.even res = true/\ x <= res /\ res <= y /\ (forall z' : Z, res < z' /\ z' <= y ->  Z.even z' = false)) )
  /\
  ( (~ exists z : Z, x <= z /\ z <= y /\ Z.even z = true) ->
    res = -1 ).

Lemma even_14 : Z.even 14 = true.
Proof.
  reflexivity.
Qed.

Lemma even_12 : Z.even 12 = true.
Proof.
  reflexivity.
Qed.

Lemma odd_13 : Z.even 13 = false.
Proof.
  reflexivity.
Qed.

Lemma odd_15 : Z.even 15 = false.
Proof.
  reflexivity.
Qed.

Example test_choose_num :
  choose_num_spec 12 15 14.
Proof.
  unfold choose_num_spec.
  split.
  - intro H.
    split.
    + apply even_14.
    + split.
      * lia.
      * split.
        -- lia.
        -- intros z' [H_gt H_le].
           assert (H_z_cases : z' = 15) by lia.
           rewrite H_z_cases.
           apply odd_15.
  - intro H.
    exfalso.
    apply H.
    exists 14.
    split.
    + lia.
    + split.
      * lia.
      * apply even_14.
Qed.