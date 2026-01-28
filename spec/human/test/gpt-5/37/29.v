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

Example problem_37_test :
  problem_37_spec [3%Z; 2%Z; 5%Z; 2%Z; 14%Z; 1%Z; 1%Z] [1%Z; 2%Z; 3%Z; 2%Z; 5%Z; 1%Z; 14%Z].
Proof.
  unfold problem_37_spec.
  split.
  - apply perm_trans with (l' := [3%Z; 1%Z; 2%Z; 5%Z; 2%Z; 14%Z; 1%Z]).
    + apply (perm_skip 3%Z).
      eapply perm_trans.
      * apply (perm_skip 2%Z).
        apply (perm_skip 5%Z).
        apply (perm_skip 2%Z).
        apply Permutation_sym. apply perm_swap.
      * eapply perm_trans.
        -- apply (perm_skip 2%Z).
           apply (perm_skip 5%Z).
           apply Permutation_sym. apply perm_swap.
        -- eapply perm_trans.
           ++ apply (perm_skip 2%Z).
              apply Permutation_sym. apply perm_swap.
           ++ apply Permutation_sym. apply perm_swap.
    + apply perm_trans with (l' := [1%Z; 3%Z; 2%Z; 5%Z; 2%Z; 14%Z; 1%Z]).
      * apply Permutation_sym. apply perm_swap.
      * apply perm_trans with (l' := [1%Z; 2%Z; 3%Z; 5%Z; 2%Z; 14%Z; 1%Z]).
        -- apply (perm_skip 1%Z).
           apply Permutation_sym. apply perm_swap.
        -- apply perm_trans with (l' := [1%Z; 2%Z; 3%Z; 2%Z; 5%Z; 14%Z; 1%Z]).
           ++ apply (perm_skip 1%Z).
              apply (perm_skip 2%Z).
              apply (perm_skip 3%Z).
              apply Permutation_sym. apply perm_swap.
           ++ apply (perm_skip 1%Z).
              apply (perm_skip 2%Z).
              apply (perm_skip 3%Z).
              apply (perm_skip 2%Z).
              apply (perm_skip 5%Z).
              apply Permutation_sym. apply perm_swap.
  - split.
    + intros i Hi Hodd.
      simpl in Hi.
      destruct i as [| [| [| [| [| [| [|i']]]]]]].
      * simpl in Hodd. exfalso. apply Hodd. reflexivity.
      * simpl. reflexivity.
      * simpl in Hodd. exfalso. apply Hodd. reflexivity.
      * simpl. reflexivity.
      * simpl in Hodd. exfalso. apply Hodd. reflexivity.
      * simpl. reflexivity.
      * simpl in Hodd. exfalso. apply Hodd. reflexivity.
      * lia.
    + intros i j H.
      destruct H as [Hi [Hj [Hi2 [Hj2 Hij]]]].
      simpl in *.
      destruct i as [| [| [| [| [| [| [|i']]]]]]].
      * destruct j as [| [| [| [| [| [| [|j']]]]]]].
        -- lia.
        -- simpl in Hj2; discriminate.
        -- simpl. lia.
        -- simpl in Hj2; discriminate.
        -- simpl. lia.
        -- simpl in Hj2; discriminate.
        -- simpl. lia.
        -- lia.
      * simpl in Hi2; discriminate.
      * destruct j as [| [| [| [| [| [| [|j']]]]]]].
        -- lia.
        -- simpl in Hj2; discriminate.
        -- lia.
        -- simpl in Hj2; discriminate.
        -- simpl. lia.
        -- simpl in Hj2; discriminate.
        -- simpl. lia.
        -- lia.
      * simpl in Hi2; discriminate.
      * destruct j as [| [| [| [| [| [| [|j']]]]]]].
        -- lia.
        -- simpl in Hj2; discriminate.
        -- lia.
        -- simpl in Hj2; discriminate.
        -- lia.
        -- simpl in Hj2; discriminate.
        -- simpl. lia.
        -- lia.
      * simpl in Hi2; discriminate.
      * destruct j as [| [| [| [| [| [| [|j']]]]]]].
        -- lia.
        -- simpl in Hj2; discriminate.
        -- lia.
        -- simpl in Hj2; discriminate.
        -- lia.
        -- simpl in Hj2; discriminate.
        -- lia.
        -- lia.
      * lia.
Qed.