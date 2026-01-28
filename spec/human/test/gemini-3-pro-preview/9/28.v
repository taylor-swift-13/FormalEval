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

Example test_case_1 : problem_9_spec [-1%Z; -2%Z; -3%Z; -4%Z; -4%Z; -3%Z; -2%Z; -1%Z; -4%Z] [-1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 9 (destruct i as [|i]; [
      simpl; split; [
        intros j Hj;
        do 9 (destruct j as [|j]; [ simpl; lia | ]); lia
      | exists 0%nat; split; [ lia | reflexivity ]
      ]
    | ]).
    simpl in H. lia.
Qed.