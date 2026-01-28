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
  [3; -3; 1; 16; 16; -8; 9; -12; 7; 6; -12; 16; 7] 
  [3; -3; 1; 6; 16; -8; 7; -12; 7; 9; -12; 16; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i as [|i]; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        apply Permutation_trans with (l' := [16; 6; 9; 7]).
        { apply Permutation_cons. apply Permutation_swap. }
        apply Permutation_trans with (l' := [6; 16; 9; 7]).
        { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := [16; 7; 9]).
        { apply Permutation_cons. apply Permutation_swap. }
        apply Permutation_trans with (l' := [7; 16; 9]).
        { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try (apply HdRel_cons; compute; discriminate); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.