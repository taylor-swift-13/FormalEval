Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Reals.Reals.
Require Import Arith.PeanoNat.
Require Import Lia.
Require Import Psatz.
Import ListNotations.

Definition problem_37_pre (input : list R) : Prop := True.

Definition problem_37_spec (input output : list R) : Prop :=
  Permutation input output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 2 <> 0) ->
    nth i output 0%R = nth i input 0%R) /\
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 2 = 0 /\ j mod 2 = 0 /\ i < j ->
    (nth i output 0%R <= nth j output 0%R)%R).

Example problem_37_test :
  problem_37_spec [29.192135197854643%R; 33.66238184288656%R; 29.291147603502964%R]
                  [29.192135197854643%R; 33.66238184288656%R; 29.291147603502964%R].
Proof.
  unfold problem_37_spec.
  split.
  - apply Permutation_refl.
  - split.
    + intros i Hi Hodd.
      simpl. reflexivity.
    + intros i j H.
      destruct H as [Hi [Hj [Hi2 [Hj2 Hij]]]].
      simpl in *.
      destruct i as [| [| [|i']]].
      * destruct j as [| [| [|j']]].
        -- lia.
        -- simpl in Hj2; discriminate.
        -- simpl. lra.
        -- lia.
      * simpl in Hi2; discriminate.
      * destruct j as [| [| [|j']]].
        -- lia.
        -- simpl in Hj2; discriminate.
        -- lia.
        -- lia.
      * lia.
Qed.