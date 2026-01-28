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

Example test_case_1 : problem_9_spec [1; 3; 2; 4; 3; 5; 4; 6; 2] [1; 3; 3; 4; 4; 5; 5; 6; 6].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    repeat (destruct i as [|i]; [
      split; [
        intros j Hj;
        repeat (destruct j as [|j]; [ simpl; lia | try lia ])
      |
        (exists 0%nat; split; [lia|simpl;reflexivity]) ||
        (exists 1%nat; split; [lia|simpl;reflexivity]) ||
        (exists 2%nat; split; [lia|simpl;reflexivity]) ||
        (exists 3%nat; split; [lia|simpl;reflexivity]) ||
        (exists 4%nat; split; [lia|simpl;reflexivity]) ||
        (exists 5%nat; split; [lia|simpl;reflexivity]) ||
        (exists 6%nat; split; [lia|simpl;reflexivity]) ||
        (exists 7%nat; split; [lia|simpl;reflexivity]) ||
        (exists 8%nat; split; [lia|simpl;reflexivity])
      ]
    | try lia ]).
Qed.