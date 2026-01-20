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
  [5; 2; 7; 9; 15; 3; 7; -7; 11; 8; 0; 13; 6; -2; 19; 5; 15; 11; 6]
  [5; 2; 7; 5; 15; 3; 6; -7; 11; 6; 0; 13; 7; -2; 19; 8; 15; 11; 9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 19 (destruct i as [|i]; [ simpl in *; try reflexivity; try lia | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_skip.
        transitivity (5 :: [9; 7; 8; 6; 6]).
        { symmetry. apply Permutation_middle. }
        apply perm_skip.
        transitivity (6 :: [9; 7; 8; 6]).
        { symmetry. apply Permutation_middle. }
        apply perm_skip.
        transitivity (6 :: [9; 7; 8]).
        { symmetry. apply Permutation_middle. }
        apply perm_skip.
        transitivity (7 :: [9; 8]).
        { symmetry. apply Permutation_middle. }
        apply perm_skip.
        transitivity (8 :: [9]).
        { symmetry. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try lia).
Qed.