Require Import List ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_problem_9 : problem_9_spec [1; 2; 3; 4] [1; 2; 3; 4].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    destruct i as [|[|[|[|i']]]].
    + split.
      * intros j Hj. assert (j = 0)%nat by lia. subst. simpl. lia.
      * exists 0%nat. split; [lia | reflexivity].
    + split.
      * intros j Hj. destruct j as [|[|j']]; simpl; lia.
      * exists 1%nat. split; [lia | reflexivity].
    + split.
      * intros j Hj. destruct j as [|[|[|j']]]; simpl; lia.
      * exists 2%nat. split; [lia | reflexivity].
    + split.
      * intros j Hj. destruct j as [|[|[|[|j']]]]; simpl; lia.
      * exists 3%nat. split; [lia | reflexivity].
    + simpl in H. lia.
Qed.