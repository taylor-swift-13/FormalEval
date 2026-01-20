Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec [5; 2; 7; 9; 3; -6; 11; 8; -6; -11; 0; 300; 5; 1; 13; 6; 19; 19] [-11; 2; 7; 5; 3; -6; 5; 8; -6; 6; 0; 300; 9; 1; 13; 11; 19; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 19 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        assert (H1: [-11; 5; 5; 6; 9; 11] = [-11] ++ 5 :: [5; 6; 9; 11]) by reflexivity.
        rewrite H1. apply Permutation_cons_app. simpl.
        assert (H2: [-11; 5; 6; 9; 11] = [-11; 5; 6] ++ 9 :: [11]) by reflexivity.
        rewrite H2. apply Permutation_cons_app. simpl.
        assert (H3: [-11; 5; 6; 11] = [-11; 5; 6] ++ 11 :: []) by reflexivity.
        rewrite H3. apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; apply Z.leb_le; reflexivity ]).
        apply Sorted_nil.
Qed.