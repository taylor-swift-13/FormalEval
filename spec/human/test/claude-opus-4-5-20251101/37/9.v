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

Example problem_37_test2 :
  problem_37_spec [3%Z] [3%Z].
Proof.
  unfold problem_37_spec.
  split; [| split].
  - apply Permutation_refl.
  - intros i Hi Hodd.
    simpl in Hi.
    destruct i as [|i'].
    + simpl in Hodd. exfalso. apply Hodd. reflexivity.
    + lia.
  - intros i j [Hilen [Hjlen [Himod [Hjmod Hij]]]].
    simpl in Hilen, Hjlen.
    destruct i as [|i'].
    + destruct j as [|j'].
      * lia.
      * lia.
    + lia.
Qed.