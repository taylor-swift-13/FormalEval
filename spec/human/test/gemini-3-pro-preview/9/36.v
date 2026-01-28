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

Example test_case_1 : problem_9_spec [27; 6; 6; 20; 62; 5] [27; 27; 27; 27; 62; 62].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [| try (simpl in H; lia) ]).
    + split.
      * intros j Hj. destruct j; [simpl; lia | lia].
      * exists 0%nat. split; [lia | reflexivity].
    + split.
      * intros j Hj. do 2 (destruct j; [simpl; lia | ]). lia.
      * exists 0%nat. split; [lia | reflexivity].
    + split.
      * intros j Hj. do 3 (destruct j; [simpl; lia | ]). lia.
      * exists 0%nat. split; [lia | reflexivity].
    + split.
      * intros j Hj. do 4 (destruct j; [simpl; lia | ]). lia.
      * exists 0%nat. split; [lia | reflexivity].
    + split.
      * intros j Hj. do 5 (destruct j; [simpl; lia | ]). lia.
      * exists 4%nat. split; [lia | reflexivity].
    + split.
      * intros j Hj. do 6 (destruct j; [simpl; lia | ]). lia.
      * exists 4%nat. split; [lia | reflexivity].
Qed.