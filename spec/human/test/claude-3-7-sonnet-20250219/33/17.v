Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Definition problem_33_pre (input : list Z) : Prop := True.

Definition problem_33_spec (input output : list Z) : Prop :=
  Permutation input output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example problem_33_test1 :
  problem_33_spec [1%Z] [1%Z].
Proof.
  unfold problem_33_spec.
  split.
  - apply Permutation_refl.
  - split.
    + intros i Hi Hmod.
      simpl in Hi.
      destruct i as [|i']; simpl.
      * lia.
      * lia.
    + intros i j [Hi [Hj [Hmi [Hmj Hij]]]].
      simpl in Hi, Hj.
      destruct i as [|i']; destruct j as [|j']; simpl; try lia.
Qed.