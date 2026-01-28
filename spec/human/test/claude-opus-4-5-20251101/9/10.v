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

Example test_problem_9 : problem_9_spec [10; 20; 30; 40; 50] [10; 20; 30; 40; 50].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    split.
    + intros j Hj.
      destruct i as [|[|[|[|[|]]]]]; simpl in H; try lia;
      destruct j as [|[|[|[|[|]]]]]; simpl; try lia.
    + destruct i as [|[|[|[|[|]]]]]; simpl in H; try lia.
      * exists 0%nat. split; [lia | reflexivity].
      * exists 1%nat. split; [lia | reflexivity].
      * exists 2%nat. split; [lia | reflexivity].
      * exists 3%nat. split; [lia | reflexivity].
      * exists 4%nat. split; [lia | reflexivity].
Qed.