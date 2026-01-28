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

Example test_case_1 : problem_9_spec [10; 5; 20; 30; 50; 20; 15; 10; 2] [10; 10; 20; 30; 50; 50; 50; 50; 50].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    destruct i as [|i].
    { split.
      - intros j Hj. do 1 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 0%nat. split; [lia|reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 2 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 0%nat. split; [lia|reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 3 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 2%nat. split; [lia|reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 4 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 3%nat. split; [lia|reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 5 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 4%nat. split; [lia|reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 6 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 4%nat. split; [lia|reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 7 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 4%nat. split; [lia|reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 8 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 4%nat. split; [lia|reflexivity]. }
    destruct i as [|i].
    { split.
      - intros j Hj. do 9 (destruct j as [|j]; [simpl; lia|]). lia.
      - exists 4%nat. split; [lia|reflexivity]. }
    simpl in H. lia.
Qed.