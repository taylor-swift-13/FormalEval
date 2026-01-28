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
  [1; 2; 3; -3; 5; 1; 5; 16; -8; 9; -12; 7; 6; 16; 5] 
  [-3; 2; 3; 1; 5; 1; 5; 16; -8; 6; -12; 7; 9; 16; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i; [ simpl in *; try reflexivity; try (exfalso; lia) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (-3 :: 1 :: 5 :: 9 :: 6).
        { apply Permutation_swap. }
        apply Permutation_skip. apply Permutation_skip. apply Permutation_skip.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ simpl; try lia | ]).
        apply Sorted_nil.
Qed.