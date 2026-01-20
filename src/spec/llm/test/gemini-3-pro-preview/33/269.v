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

Example test_case : sort_third_spec 
  [1; 2; 3; 11; 5; 1; 16; -8; 9; -11; 7; 4; -12; 7; 7] 
  [-12; 2; 3; -11; 5; 1; 1; -8; 9; 11; 7; 4; 16; 7; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ 
        simpl in *; 
        try (exfalso; apply H; reflexivity); 
        try reflexivity 
        | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        change [1; 11; 16; -11; -12] with ([1; 11; 16; -11] ++ [-12] ++ []).
        apply Permutation_trans with (-12 :: [1; 11; 16; -11] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        change [1; 11; 16; -11] with ([1; 11; 16] ++ [-11] ++ []).
        apply Permutation_trans with (-11 :: [1; 11; 16] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; unfold Z.le; simpl; intro; discriminate) ]).
        apply Sorted_nil.
Qed.