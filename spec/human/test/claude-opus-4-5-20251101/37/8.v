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
  problem_37_spec [] [].
Proof.
  unfold problem_37_spec.
  split; [| split].
  - apply Permutation_refl.
  - intros i Hi Hodd.
    simpl in Hi. lia.
  - intros i j [Hilen [Hjlen [Himod [Hjmod Hij]]]].
    simpl in Hilen. lia.
Qed.