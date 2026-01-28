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

Example test_case_1 : problem_9_spec [10; 5; 20; 30; 25; 20; 10; 21; 10] [10; 10; 20; 30; 30; 30; 30; 30; 30].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 0%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 0%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 2%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 3%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 3%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 3%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 3%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 3%nat. split; [lia | simpl; reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 10 (destruct j as [|j]; [simpl; lia | ]). simpl in Hj. lia.
      - exists 3%nat. split; [lia | simpl; reflexivity]. }
    simpl in H. lia.
Qed.