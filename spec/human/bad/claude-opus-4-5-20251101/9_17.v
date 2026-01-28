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

Example test_problem_9 : problem_9_spec [10; 5; 20; 30; 50; 20; 15; 10; 2] [10; 10; 20; 30; 50; 50; 50; 50; 50].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i H.
    destruct i as [|i']; simpl in *.
    + split.
      * intros j Hj. assert (j = 0)%nat by lia. subst. simpl. lia.
      * exists 0%nat. split; [lia | reflexivity].
    + destruct i' as [|i'']; simpl in *.
      * split.
        -- intros j Hj. destruct j as [|j']; simpl; lia.
        -- exists 0%nat. split; [lia | reflexivity].
      * destruct i'' as [|i''']; simpl in *.
        -- split.
           ++ intros j Hj. destruct j as [|[|[|]]]; simpl; lia.
           ++ exists 2%nat. split; [lia | reflexivity].
        -- destruct i''' as [|i'''']; simpl in *.
           ++ split.
              ** intros j Hj. destruct j as [|[|[|[|]]]]; simpl; lia.
              ** exists 3%nat. split; [lia | reflexivity].
           ++ destruct i'''' as [|i''''']; simpl in *.
              ** split.
                 --- intros j Hj. destruct j as [|[|[|[|[|]]]]]; simpl; lia.
                 --- exists 4%nat. split; [lia | reflexivity].
              ** destruct i''''' as [|i'''''']; simpl in *.
                 --- split.
                     +++ intros j Hj. destruct j as [|[|[|[|[|[|]]]]]]; simpl; lia.
                     +++ exists 4%nat. split; [lia | reflexivity].
                 --- destruct i'''''' as [|i''''''']; simpl in *.
                     +++ split.
                         *** intros j Hj. destruct j as [|[|[|[|[|[|[|]]]]]]]; simpl; lia.
                         *** exists 4%nat. split; [lia | reflexivity].
                     +++ destruct i''''''' as [|i'''''''']; simpl in *.
                         *** split.
                             ---- intros j Hj. destruct j as [|[|[|[|[|[|[|[|]]]]]]]]; simpl; lia.
                             ---- exists 4%nat. split; [lia | reflexivity].
                         *** destruct i'''''''' as [|i''''''''']; simpl in *.
                             ---- split.
                                  ++++ intros j Hj. destruct j as [|[|[|[|[|[|[|[|[|]]]]]]]]]; simpl; lia.
                                  ++++ exists 4%nat. split; [lia | reflexivity].
                             ---- lia.
Qed.