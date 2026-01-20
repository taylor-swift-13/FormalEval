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
  [5; 2; 9; 3; -7; 11; 8; -6; 0; 6; 1; 13; 6; -2; 19] 
  [3; 2; 9; 5; -7; 11; 6; -6; 0; 6; 1; 13; 8; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i as [|i]; [
        simpl in *; 
        try (match goal with | H : ?x <> 0 |- _ => elim H; reflexivity end); 
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply Permutation_trans with (l' := [3; 5; 8; 6; 6]).
        { apply Permutation_swap. }
        apply Permutation_cons. apply Permutation_cons.
        apply Permutation_trans with (l' := [6; 8; 6]).
        { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.