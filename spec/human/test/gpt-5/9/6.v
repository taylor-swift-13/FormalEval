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

Example problem_9_test_empty :
  problem_9_spec [5%Z; 4%Z; 3%Z; 2%Z; 1%Z] [5%Z; 5%Z; 5%Z; 5%Z; 5%Z].
Proof.
  unfold problem_9_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i1].
    + split.
      * intros j Hj.
        destruct j as [|j1].
        -- simpl. lia.
        -- exfalso. lia.
      * exists 0%nat. split; [lia| simpl; reflexivity].
    + assert (i1 < 4)%nat by lia.
      destruct i1 as [|i2].
      * split.
        -- intros j Hj. destruct j as [|j1].
           ++ simpl. lia.
           ++ destruct j1 as [|j2].
              ** simpl. lia.
              ** exfalso. lia.
        -- exists 0%nat. split; [lia| simpl; reflexivity].
      * assert (i2 < 3)%nat by lia.
        destruct i2 as [|i3].
        -- split.
           ++ intros j Hj. destruct j as [|j1].
              ** simpl. lia.
              ** destruct j1 as [|j2].
                 --- simpl. lia.
                 --- destruct j2 as [|j3].
                     +++ simpl. lia.
                     +++ exfalso. lia.
           ++ exists 0%nat. split; [lia| simpl; reflexivity].
        -- assert (i3 < 2)%nat by lia.
           destruct i3 as [|i4].
           ++ split.
              ** intros j Hj. destruct j as [|j1].
                 --- simpl. lia.
                 --- destruct j1 as [|j2].
                     +++ simpl. lia.
                     +++ destruct j2 as [|j3].
                         *** simpl. lia.
                         *** destruct j3 as [|j4].
                             ---- simpl. lia.
                             ---- exfalso. lia.
              ** exists 0%nat. split; [lia| simpl; reflexivity].
           ++ assert (i4 < 1)%nat by lia.
              destruct i4 as [|i5].
              ** split.
                 --- intros j Hj. destruct j as [|j1].
                     +++ simpl. lia.
                     +++ destruct j1 as [|j2].
                         *** simpl. lia.
                         *** destruct j2 as [|j3].
                             ---- simpl. lia.
                             ---- destruct j3 as [|j4].
                                  ----- simpl. lia.
                                  ----- destruct j4 as [|j5].
                                        +++++ simpl. lia.
                                        +++++ exfalso. lia.
                 --- exists 0%nat. split; [lia| simpl; reflexivity].
              ** exfalso. lia.
Qed.