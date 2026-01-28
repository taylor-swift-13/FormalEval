Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Definition problem_37_pre (input : list Z) : Prop := True.

Definition problem_37_spec (input output : list Z) : Prop :=
  Permutation input output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 2 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 2 = 0 /\ j mod 2 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example problem_37_test1 :
  problem_37_spec [2%Z; 6%Z; 4%Z; 8%Z; 10%Z] [2%Z; 6%Z; 4%Z; 8%Z; 10%Z].
Proof.
  unfold problem_37_spec.
  split; [| split].
  - apply Permutation_refl.
  - intros i Hi Hodd.
    simpl in Hi.
    destruct i as [|i'].
    + simpl in Hodd. exfalso. apply Hodd. reflexivity.
    + destruct i' as [|i''].
      * simpl. reflexivity.
      * destruct i'' as [|i'''].
        -- simpl in Hodd. exfalso. apply Hodd. reflexivity.
        -- destruct i''' as [|i''''].
           ++ simpl. reflexivity.
           ++ simpl in Hi. lia.
  - intros i j [Hilen [Hjlen [Himod [Hjmod Hij]]]].
    simpl in Hilen, Hjlen.
    destruct i as [|i'].
    + destruct j as [|j'].
      * lia.
      * destruct j' as [|j''].
        -- simpl in Hjmod. discriminate.
        -- destruct j'' as [|j'''].
           ++ simpl. lia.
           ++ destruct j''' as [|j''''].
              ** simpl in Hjmod. discriminate.
              ** destruct j'''' as [|j'''''].
                 --- simpl. lia.
                 --- lia.
    + destruct i' as [|i''].
      * simpl in Himod. discriminate.
      * destruct i'' as [|i'''].
        -- destruct j as [|j'].
           ++ lia.
           ++ destruct j' as [|j''].
              ** simpl in Hjmod. discriminate.
              ** destruct j'' as [|j'''].
                 --- lia.
                 --- destruct j''' as [|j''''].
                     +++ simpl in Hjmod. discriminate.
                     +++ destruct j'''' as [|j'''''].
                         *** simpl. lia.
                         *** lia.
        -- destruct i''' as [|i''''].
           ++ simpl in Himod. discriminate.
           ++ destruct i'''' as [|i'''''].
              ** destruct j as [|j'].
                 --- lia.
                 --- destruct j' as [|j''].
                     +++ simpl in Hjmod. discriminate.
                     +++ destruct j'' as [|j'''].
                         *** lia.
                         *** destruct j''' as [|j''''].
                             ---- simpl in Hjmod. discriminate.
                             ---- lia.
              ** lia.
Qed.