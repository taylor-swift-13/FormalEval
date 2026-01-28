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
  problem_9_spec [4%Z; 3%Z; 2%Z; 1%Z] [4%Z; 4%Z; 4%Z; 4%Z].
Proof.
  unfold problem_9_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i'].
    + split.
      * intros j Hj.
        assert (j = 0%nat) by lia.
        subst j.
        simpl. lia.
      * exists 0%nat. split; [lia|reflexivity].
    + assert (Hle : (i' <= 2)%nat) by lia.
      split.
      * intros j Hj.
        assert (Hi_cases : i' = 0%nat \/ i' = 1%nat \/ i' = 2%nat) by lia.
        destruct Hi_cases as [Hi0 | [Hi1 | Hi2]]; subst i'.
        -- destruct j as [|j'].
           ++ simpl. lia.
           ++ assert (j' = 0%nat) by lia. subst j'. simpl. lia.
        -- destruct j as [|j'].
           ++ simpl. lia.
           ++ assert (Hj'le : (j' <= 1)%nat) by lia.
              destruct j' as [|j''].
              ** simpl. lia.
              ** assert (j'' = 0%nat) by lia. subst. simpl. lia.
        -- destruct j as [|j'].
           ++ simpl. lia.
           ++ assert (Hj'le : (j' <= 2)%nat) by lia.
              destruct j' as [|j''].
              ** simpl. lia.
              ** destruct j'' as [|j'''].
                 --- simpl. lia.
                 --- assert (j''' = 0%nat) by lia. subst. simpl. lia.
      * assert (Hi_cases : i' = 0%nat \/ i' = 1%nat \/ i' = 2%nat) by lia.
        destruct Hi_cases as [Hi0 | [Hi1 | Hi2]]; subst i'.
        -- exists 0%nat. split; [lia|reflexivity].
        -- exists 0%nat. split; [lia|reflexivity].
        -- exists 0%nat. split; [lia|reflexivity].
Qed.