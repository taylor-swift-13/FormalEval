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

Example test_case_new : problem_9_spec [-1; -2; -3; -4; -4; -2; -1; -4] [-1; -1; -1; -1; -1; -1; -1; -1].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    repeat (destruct i as [|i]; [
      split; [
        intros j Hj;
        repeat (destruct j as [|j]; [
          simpl; lia
        |
          try lia
        ])
      |
        exists 0%nat; split; [lia | simpl; reflexivity]
      ]
    | ]).
    lia.
Qed.