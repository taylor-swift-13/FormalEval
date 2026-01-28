Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example problem_9_test_case : problem_9_spec [1%Z; 3%Z; 2%Z; 4%Z; 3%Z; 5%Z; 4%Z; 6%Z] [1%Z; 3%Z; 3%Z; 4%Z; 4%Z; 5%Z; 5%Z; 6%Z].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    split.
    + intros j Hj.
      destruct j; destruct i; simpl; try lia.
      destruct j; destruct i; simpl; try lia.
      destruct j; destruct i; simpl; try lia.
      destruct j; destruct i; simpl; try lia.
      destruct j; destruct i; simpl; try lia.
      destruct j; destruct i; simpl; try lia.
      destruct j; destruct i; simpl; try lia.
      destruct j; destruct i; simpl; try lia.
    + destruct i; simpl; try (exists 0; lia).
      destruct i; simpl; try (exists 1; lia).
      destruct i; simpl; try (exists 2; lia).
      destruct i; simpl; try (exists 3; lia).
      destruct i; simpl; try (exists 4; lia).
      destruct i; simpl; try (exists 5; lia).
      destruct i; simpl; try (exists 6; lia).
      destruct i; simpl; try (exists 7; lia).
Qed.