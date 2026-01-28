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

Example test_problem_9 : problem_9_spec [1; 2; 3; 4; 5; 4; 3; 2; 1] [1; 2; 3; 4; 5; 5; 5; 5; 5].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    simpl in H.
    split.
    + intros j Hj.
      destruct i as [|[|[|[|[|[|[|[|[|]]]]]]]]]; simpl; try lia;
      destruct j as [|[|[|[|[|[|[|[|[|]]]]]]]]]; simpl; try lia.
    + destruct i as [|[|[|[|[|[|[|[|[|]]]]]]]]]; simpl; try lia.
      * exists 0%nat. split; [lia | reflexivity].
      * exists 1%nat. split; [lia | reflexivity].
      * exists 2%nat. split; [lia | reflexivity].
      * exists 3%nat. split; [lia | reflexivity].
      * exists 4%nat. split; [lia | reflexivity].
      * exists 4%nat. split; [lia | reflexivity].
      * exists 4%nat. split; [lia | reflexivity].
      * exists 4%nat. split; [lia | reflexivity].
      * exists 4%nat. split; [lia | reflexivity].
Qed.