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
  [5; 2; 7; 9; 3; -6; -6; 0; 300; 1; 13; 1; 6; -2; 19]
  [-6; 2; 7; 1; 3; -6; 5; 0; 300; 6; 13; 1; 9; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-6 :: [5; 9] ++ [1; 6]).
        { apply perm_skip.
          transitivity (1 :: [5; 9] ++ [6]).
          { apply perm_skip. apply perm_skip. apply perm_swap. }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * simpl.
        repeat (constructor; try (compute; discriminate)).
Qed.