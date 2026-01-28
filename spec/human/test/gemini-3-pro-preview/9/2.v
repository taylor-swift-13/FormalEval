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

Example test_case_1 : problem_9_spec [1; 2; 3; 4] [1; 2; 3; 4].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    destruct i.
    + split.
      * intros j Hj. replace j with 0%nat by lia. simpl. lia.
      * exists 0%nat. split; [lia | simpl; reflexivity].
    + destruct i.
      * split.
        -- intros j Hj. assert (j = 0 \/ j = 1)%nat by lia. destruct H; subst; simpl; lia.
        -- exists 1%nat. split; [lia | simpl; reflexivity].
      * destruct i.
        -- split.
           ++ intros j Hj. assert (j = 0 \/ j = 1 \/ j = 2)%nat by lia. destruct H as [|[|]]; subst; simpl; lia.
           ++ exists 2%nat. split; [lia | simpl; reflexivity].
        -- destruct i.
           ++ split.
              ** intros j Hj. assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%nat by lia. destruct H as [|[|[|]]]; subst; simpl; lia.
              ** exists 3%nat. split; [lia | simpl; reflexivity].
           ++ lia.
Qed.