Require Import List ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_problem_9 : problem_9_spec [-1; -2; -3; -4; -4; -2; -1; -4] [-1; -1; -1; -1; -1; -1; -1; -1].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    split.
    + intros j Hj.
      do 8 (destruct i; [do 8 (destruct j; [simpl; lia | ]); simpl in Hj; lia | ]).
      simpl in H. lia.
    + do 8 (destruct i; [exists 0%nat; simpl; lia | ]).
      simpl in H. lia.
Qed.