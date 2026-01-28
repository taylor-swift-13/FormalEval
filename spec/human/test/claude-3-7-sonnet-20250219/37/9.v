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

Example test_problem_37 : problem_37_spec [3%Z] [3%Z].
Proof.
  unfold problem_37_spec.
  split.
  - apply Permutation_refl.
  - split.
    + intros i Hi Hodd.
      simpl in Hi.
      destruct i as [|i'].
      * lia.
      * simpl. lia.
    + intros i j [Hi [Hj [Heven_i [Heven_j Hlt]]]].
      simpl in Hi, Hj.
      destruct i as [|i']; destruct j as [|j'];
        try lia; simpl; try lia.
Qed.