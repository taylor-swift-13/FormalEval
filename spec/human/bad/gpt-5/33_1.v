Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_33_pre (input : list Z) : Prop := True.

Definition problem_33_spec (input output : list Z) : Prop :=
  Permutation input output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example problem_33_example :
  problem_33_spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  split.
  - apply Permutation_refl.
  - intros i Hi Hmod. reflexivity.
  - intros i j H.
    destruct H as [Hi [Hj [Himod [Hjmod Hlt]]]].
    simpl in Hi, Hj.
    assert (Hmi : i mod 3 = i) by (apply Nat.mod_small; lia).
    assert (Hmj : j mod 3 = j) by (apply Nat.mod_small; lia).
    rewrite Hmi in Himod.
    rewrite Hmj in Hjmod.
    subst i. subst j.
    simpl. lia.
Qed.