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
  [-4; 3; -6; 3; 0; -8; 2; 1; 8; 14; 0; 2] 
  [-4; 3; -6; 2; 0; -8; 3; 1; 8; 14; 0; 2].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i as [|i]; [
        simpl in *;
        try reflexivity;
        try (exfalso; apply H; reflexivity)
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        apply Permutation_swap.
        apply Permutation_refl.
      * simpl.
        apply Sorted_cons. simpl. auto with zarith.
        apply Sorted_cons. simpl. auto with zarith.
        apply Sorted_cons. simpl. auto with zarith.
        apply Sorted_cons. simpl. auto with zarith.
        apply Sorted_nil.
Qed.