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
  [1; 2; 3; 5; 1; 0; -8; 9; -12; 7; -4; 6; 1; 6] 
  [-8; 2; 3; 1; 1; 0; 1; 9; -12; 5; -4; 6; 7; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (5 :: 1 :: -8 :: 7 :: 1 :: []). apply Permutation_swap.
        transitivity (5 :: -8 :: 1 :: 7 :: 1 :: []). apply Permutation_cons. apply Permutation_swap.
        transitivity (-8 :: 5 :: 1 :: 7 :: 1 :: []). apply Permutation_swap.
        apply Permutation_cons.
        transitivity (1 :: 5 :: 7 :: 1 :: []). apply Permutation_swap.
        apply Permutation_cons.
        transitivity (7 :: 5 :: 1 :: []). apply Permutation_swap.
        transitivity (7 :: 1 :: 5 :: []). apply Permutation_cons. apply Permutation_swap.
        transitivity (1 :: 7 :: 5 :: []). apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; apply HdRel_cons; auto with zarith ]).
        apply Sorted_nil.
Qed.