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

Example test_problem_9 : problem_9_spec [0; -2; -3; -4; -5; -4; -3; -2; -1] [0; 0; 0; 0; 0; 0; 0; 0; 0].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    split.
    + intros j Hj.
      do 9 (destruct i; [do 9 (destruct j; [simpl; lia | ]); simpl in Hj; lia | ]).
      simpl in H. lia.
    + exists 0%nat.
      split.
      * lia.
      * do 9 (destruct i; [simpl; reflexivity | ]).
        simpl in H. lia.
Qed.