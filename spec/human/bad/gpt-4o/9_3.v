Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example problem_9_test_case : problem_9_spec [4%Z; 3%Z; 2%Z; 1%Z] [4%Z; 4%Z; 4%Z; 4%Z].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i. intros H.
    split.
    + intros j Hj.
      destruct j; simpl.
      * apply Z.le_refl.
      * destruct j; simpl.
        ** apply Z.le_refl.
        ** destruct j; simpl.
           *** apply Z.le_refl.
           *** destruct j; simpl.
               **** apply Z.le_refl.
               **** lia.
    + exists 0%nat. split; auto.
      destruct i; simpl; reflexivity.
Qed.