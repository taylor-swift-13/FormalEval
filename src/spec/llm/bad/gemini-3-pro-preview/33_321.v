Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [-4; 8; 3; -6; 0; -8; 6; 2; 1; 8; 13; 6; 6; -8; 14; -6] 
  [-6; 8; 3; -6; 0; -8; -4; 2; 1; 6; 13; 6; 6; -8; 14; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply Permutation_trans with (l' := -6 :: -4 :: 6 :: 8 :: 6 :: -6 :: []).
        { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := -4 :: 6 :: 8 :: -6 :: 6 :: []).
        { apply Permutation_cons. apply Permutation_cons. apply Permutation_cons. apply Permutation_swap. }
        apply Permutation_trans with (l' := -4 :: 6 :: -6 :: 8 :: 6 :: []).
        { apply Permutation_cons. apply Permutation_cons. apply Permutation_swap. }
        apply Permutation_trans with (l' := -4 :: -6 :: 6 :: 8 :: 6 :: []).
        { apply Permutation_cons. apply Permutation_swap. }
        apply Permutation_trans with (l' := -6 :: -4 :: 6 :: 8 :: 6 :: []).
        { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.