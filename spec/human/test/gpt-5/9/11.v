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
  problem_9_spec [50%Z; 40%Z; 30%Z; 20%Z; 10%Z] [50%Z; 50%Z; 50%Z; 50%Z; 50%Z].
Proof.
  unfold problem_9_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    split.
    + intros j Hj.
      destruct i as [|i1].
      * simpl in Hj.
        destruct j as [|j1].
        -- simpl. lia.
        -- exfalso. lia.
      * destruct i1 as [|i2].
        -- simpl.
           destruct j as [|[|j2]].
           ++ simpl. lia.
           ++ simpl. lia.
           ++ exfalso. lia.
        -- destruct i2 as [|i3].
           ++ simpl.
              destruct j as [|[|[|j3]]].
              ** simpl. lia.
              ** simpl. lia.
              ** simpl. lia.
              ** exfalso. lia.
           ++ destruct i3 as [|i4].
              ** simpl.
                 destruct j as [|[|[|[|j4]]]].
                 --- simpl. lia.
                 --- simpl. lia.
                 --- simpl. lia.
                 --- simpl. lia.
                 --- exfalso. lia.
              ** destruct i4 as [|i5].
                 --- simpl.
                     destruct j as [|[|[|[|[|j5]]]]].
                     **** simpl. lia.
                     **** simpl. lia.
                     **** simpl. lia.
                     **** simpl. lia.
                     **** simpl. lia.
                     **** exfalso. lia.
                 --- exfalso. lia.
    + destruct i as [|i1].
      * exists 0%nat. split; [lia | simpl; reflexivity].
      * destruct i1 as [|i2].
        -- exists 0%nat. split; [lia | simpl; reflexivity].
        -- destruct i2 as [|i3].
           ++ exists 0%nat. split; [lia | simpl; reflexivity].
           ++ destruct i3 as [|i4].
              ** exists 0%nat. split; [lia | simpl; reflexivity].
              ** destruct i4 as [|i5].
                 --- exists 0%nat. split; [lia | simpl; reflexivity].
                 --- exfalso. lia.
Qed.