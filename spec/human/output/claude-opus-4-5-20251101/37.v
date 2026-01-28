Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* Pre: no additional constraints for `sort_even` by default *)
Definition problem_37_pre (input : list Z) : Prop := True.

(* Spec 的定义 *)
Definition problem_37_spec (input output : list Z) : Prop :=
  (* 1. input 是 output 的排列 (Permutation) *)
  Permutation input output /\

  (* 2. 如果索引 i 不能被 2 整除，则 output[i] 必须等于 input[i] *)
  (forall (i : nat), (i < length input)%nat -> (i mod 2 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\

  (* 3. output 中所有索引能被 2 整除的元素，必须是按索引顺序排好序的 (非递减) *)
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 2 = 0 /\ j mod 2 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example problem_37_test1 :
  problem_37_spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  unfold problem_37_spec.
  split; [| split].
  - (* Permutation [1; 2; 3] [1; 2; 3] *)
    apply Permutation_refl.
  - (* Odd indices preservation *)
    intros i Hi Hodd.
    simpl in Hi.
    destruct i as [|i'].
    + (* i = 0 *) simpl in Hodd. exfalso. apply Hodd. reflexivity.
    + destruct i' as [|i''].
      * (* i = 1 *) simpl. reflexivity.
      * destruct i'' as [|i'''].
        -- (* i = 2 *) simpl in Hodd. exfalso. apply Hodd. reflexivity.
        -- (* i >= 3 *) simpl in Hi. lia.
  - (* Even indices sorted *)
    intros i j [Hilen [Hjlen [Himod [Hjmod Hij]]]].
    simpl in Hilen, Hjlen.
    destruct i as [|i'].
    + (* i = 0 *)
      destruct j as [|j'].
      * (* j = 0 *) lia.
      * destruct j' as [|j''].
        -- (* j = 1 *) simpl in Hjmod. discriminate.
        -- destruct j'' as [|j'''].
           ++ (* j = 2 *) simpl. lia.
           ++ (* j >= 3 *) lia.
    + destruct i' as [|i''].
      * (* i = 1 *) simpl in Himod. discriminate.
      * destruct i'' as [|i'''].
        -- (* i = 2 *)
           destruct j as [|j'].
           ++ lia.
           ++ destruct j' as [|j''].
              ** simpl in Hjmod. discriminate.
              ** destruct j'' as [|j'''].
                 --- lia.
                 --- lia.
        -- (* i >= 3 *) lia.
Qed.