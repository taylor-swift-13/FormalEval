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

Example test_case_1 : problem_9_spec [4; 3; 2; 1; 6] [4; 4; 4; 4; 6].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i as [|i].
    { (* i = 0 *)
      split.
      - intros j Hj. destruct j; [simpl; lia | lia].
      - exists 0%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { (* i = 1 *)
      split.
      - intros j Hj. do 2 (destruct j; [simpl; lia | ]). lia.
      - exists 0%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { (* i = 2 *)
      split.
      - intros j Hj. do 3 (destruct j; [simpl; lia | ]). lia.
      - exists 0%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { (* i = 3 *)
      split.
      - intros j Hj. do 4 (destruct j; [simpl; lia | ]). lia.
      - exists 0%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { (* i = 4 *)
      split.
      - intros j Hj. do 5 (destruct j; [simpl; lia | ]). lia.
      - exists 4%nat. split; [lia | simpl; reflexivity]. }
    lia.
Qed.