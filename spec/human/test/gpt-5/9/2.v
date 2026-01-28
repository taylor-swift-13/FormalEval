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

Example problem_9_test_increasing :
  problem_9_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 2%Z; 3%Z; 4%Z].
Proof.
  unfold problem_9_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i1].
    + simpl.
      split.
      * intros j Hj.
        destruct j as [|j1].
        -- simpl; lia.
        -- exfalso; lia.
      * exists 0%nat.
        split; [lia | simpl; reflexivity].
    + destruct i1 as [|i2].
      * simpl.
        split.
        -- intros j Hj.
           destruct j as [|j1].
           ++ simpl; lia.
           ++ destruct j1 as [|j2].
              ** simpl; lia.
              ** exfalso; lia.
        -- exists 1%nat.
           split; [lia | simpl; reflexivity].
      * destruct i2 as [|i3].
        -- simpl.
           split.
           ++ intros j Hj.
              destruct j as [|j1].
              ** simpl; lia.
              ** destruct j1 as [|j2].
                 --- simpl; lia.
                 --- destruct j2 as [|j3].
                     **** simpl; lia.
                     **** exfalso; lia.
           ++ exists 2%nat.
              split; [lia | simpl; reflexivity].
        -- destruct i3 as [|i4].
           ++ simpl.
              split.
              ** intros j Hj.
                 destruct j as [|j1].
                 --- simpl; lia.
                 --- destruct j1 as [|j2].
                     **** simpl; lia.
                     **** destruct j2 as [|j3].
                          ++++ simpl; lia.
                          ++++ destruct j3 as [|j4].
                               ***** simpl; lia.
                               ***** exfalso; lia.
              ** exists 3%nat.
                 split; [lia | simpl; reflexivity].
           ++ exfalso; lia.
Qed.