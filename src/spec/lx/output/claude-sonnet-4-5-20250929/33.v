Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Definition Spec (input output : list Z) : Prop :=
  length input = length output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\
  (forall (i : nat), i < length output -> i mod 3 = 0 ->
    exists (j : nat), j < length input /\ j mod 3 = 0 /\ nth j input 0%Z = nth i output 0%Z) /\
  (forall (i : nat), i < length input -> i mod 3 = 0 ->
    exists (j : nat), j < length output /\ j mod 3 = 0 /\ nth j output 0%Z = nth i input 0%Z) /\
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example test_sort_third :
  Spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  unfold Spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H_bound H_not_div.
      destruct i as [|i'].
      * simpl in H_not_div.
        contradiction.
      * destruct i' as [|i''].
        -- assert (H_mod : 1 mod 3 = 1) by reflexivity.
           rewrite H_mod in H_not_div.
           simpl. reflexivity.
        -- destruct i'' as [|i'''].
           ++ assert (H_mod : 2 mod 3 = 2) by reflexivity.
              rewrite H_mod in H_not_div.
              simpl. reflexivity.
           ++ simpl in H_bound.
              lia.
    + split.
      * intros i H_bound H_div.
        destruct i as [|i'].
        -- exists 0.
           split; [simpl; lia | split; [reflexivity | simpl; reflexivity]].
        -- destruct i' as [|i''].
           ++ assert (H_mod : 1 mod 3 = 1) by reflexivity.
              rewrite H_mod in H_div.
              discriminate.
           ++ destruct i'' as [|i'''].
              ** assert (H_mod : 2 mod 3 = 2) by reflexivity.
                 rewrite H_mod in H_div.
                 discriminate.
              ** simpl in H_bound.
                 lia.
      * split.
        -- intros i H_bound H_div.
           destruct i as [|i'].
           ++ exists 0.
              split; [simpl; lia | split; [reflexivity | simpl; reflexivity]].
           ++ destruct i' as [|i''].
              ** assert (H_mod : 1 mod 3 = 1) by reflexivity.
                 rewrite H_mod in H_div.
                 discriminate.
              ** destruct i'' as [|i'''].
                 --- assert (H_mod : 2 mod 3 = 2) by reflexivity.
                     rewrite H_mod in H_div.
                     discriminate.
                 --- simpl in H_bound.
                     lia.
        -- intros i j [H_i_bound [H_j_bound [H_i_div [H_j_div H_lt]]]].
           destruct i as [|i']; destruct j as [|j'].
           ++ lia.
           ++ destruct j' as [|j''].
              ** assert (H_mod : 1 mod 3 = 1) by reflexivity.
                 rewrite H_mod in H_j_div.
                 discriminate.
              ** destruct j'' as [|j'''].
                 --- assert (H_mod : 2 mod 3 = 2) by reflexivity.
                     rewrite H_mod in H_j_div.
                     discriminate.
                 --- simpl in H_j_bound.
                     lia.
           ++ lia.
           ++ destruct i' as [|i''].
              ** assert (H_mod : 1 mod 3 = 1) by reflexivity.
                 rewrite H_mod in H_i_div.
                 discriminate.
              ** destruct i'' as [|i'''].
                 --- assert (H_mod : 2 mod 3 = 2) by reflexivity.
                     rewrite H_mod in H_i_div.
                     discriminate.
                 --- simpl in H_i_bound.
                     lia.
Qed.