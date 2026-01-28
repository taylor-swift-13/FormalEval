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

Example test_case : problem_9_spec [10; 6; 20; 30; 25; 20; 15; 10] [10; 10; 20; 30; 30; 30; 30; 30].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    repeat (destruct i as [|i]; [
      split; [
        intros j Hj;
        repeat (destruct j as [|j]; [ simpl; lia | try (simpl in Hj; lia) ])
      |
        (exists 0%nat; split; [lia | simpl; reflexivity]) ||
        (exists 1%nat; split; [lia | simpl; reflexivity]) ||
        (exists 2%nat; split; [lia | simpl; reflexivity]) ||
        (exists 3%nat; split; [lia | simpl; reflexivity]) ||
        (exists 4%nat; split; [lia | simpl; reflexivity]) ||
        (exists 5%nat; split; [lia | simpl; reflexivity]) ||
        (exists 6%nat; split; [lia | simpl; reflexivity]) ||
        (exists 7%nat; split; [lia | simpl; reflexivity])
      ]; clear i
    | simpl in Hi; try lia ]).
Qed.