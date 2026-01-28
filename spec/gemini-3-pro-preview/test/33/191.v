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
  [1; 2; 3; 5; 1; 0; -8; 9; -12; 7; 6; 6; 1; -12; -8] 
  [-8; 2; 3; 1; 1; 0; 1; 9; -12; 5; 6; 6; 7; -12; -8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in *; try (compute in H; contradict H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (1 :: -8 :: 5 :: 7 :: 1 :: []).
        { apply perm_skip. apply perm_swap. }
        transitivity (-8 :: 1 :: 5 :: 7 :: 1 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_skip.
        transitivity (5 :: 1 :: 7 :: []).
        { apply perm_skip. apply perm_swap. }
        transitivity (1 :: 5 :: 7 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try (compute; discriminate)).
Qed.