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

Example problem_9_test_case :
  problem_9_spec [5%Z; 4%Z; 3%Z; 1%Z; 1%Z] [5%Z; 5%Z; 5%Z; 5%Z; 5%Z].
Proof.
  unfold problem_9_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i].
    + split.
      * intros j Hj.
        destruct j as [|j].
        -- simpl. lia.
        -- exfalso. lia.
      * exists 0%nat. split; [lia| simpl; reflexivity].
    + destruct i as [|i].
      * split.
        -- intros j Hj.
           destruct j as [|j].
           ++ simpl. lia.
           ++ destruct j as [|j].
              ** simpl. lia.
              ** exfalso. lia.
        -- exists 0%nat. split; [lia| simpl; reflexivity].
      * destruct i as [|i].
        -- split.
           --- intros j Hj.
               destruct j as [|j].
               +++ simpl. lia.
               +++ destruct j as [|j].
                   *** simpl. lia.
                   *** destruct j as [|j].
                       **** simpl. lia.
                       **** exfalso. lia.
           --- exists 0%nat. split; [lia| simpl; reflexivity].
        -- destruct i as [|i].
           --- split.
               ---- intros j Hj.
                    destruct j as [|j].
                    ++++ simpl. lia.
                    ++++ destruct j as [|j].
                         ***** simpl. lia.
                         ***** destruct j as [|j].
                               ****** simpl. lia.
                               ****** destruct j as [|j].
                                      ******* simpl. lia.
                                      ******* exfalso. lia.
               ---- exists 0%nat. split; [lia| simpl; reflexivity].
           --- destruct i as [|i].
               ---- split.
                    ----- intros j Hj.
                          destruct j as [|j].
                          +++++ simpl. lia.
                          +++++ destruct j as [|j].
                                ****** simpl. lia.
                                ****** destruct j as [|j].
                                       ******* simpl. lia.
                                       ******* destruct j as [|j].
                                               ******** simpl. lia.
                                               ******** destruct j as [|j].
                                                        ********* simpl. lia.
                                                        ********* exfalso. lia.
                    ----- exists 0%nat. split; [lia| simpl; reflexivity].
               ---- exfalso. lia.
Qed.