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

Example test_problem_9 : problem_9_spec [50; 40; 30; 20; 10] [50; 50; 50; 50; 50].
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
      * exists 0%nat. split; [lia | reflexivity].
      * exists 0%nat. split; [lia | reflexivity].
      * exists 0%nat. split; [lia | reflexivity].
      * exists 0%nat. split; [lia | reflexivity].
Qed.