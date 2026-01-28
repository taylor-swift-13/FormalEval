Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_case_1 : problem_9_spec [0; -2; -3; -4; -5; -4; -3; -2; -1] [0; 0; 0; 0; 0; 0; 0; 0; 0].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 9 (destruct i; [
      split; [
        intros j Hj;
        do 9 (destruct j; [ simpl; lia | ]); lia
      |
        exists 0%nat; split; [ lia | reflexivity ]
      ]
      |
    ]).
    lia.
Qed.