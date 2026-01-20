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
  [1; 2; 3; 5; 1; 0; -8; 9; 0; -12; 7; 6; 6; 1; -12] 
  [-12; 2; 3; -8; 1; 0; 1; 9; 0; 5; 7; 6; 6; 1; -12].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [
        try (compute in H; exfalso; apply H; reflexivity);
        reflexivity 
      | ]).
      reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply Permutation_trans with (l' := -12 :: [1; 5; -8; 6]).
        { change [1; 5; -8; -12; 6] with ([1; 5; -8] ++ -12 :: [6]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := -8 :: [1; 5; 6]).
        { change [1; 5; -8; 6] with ([1; 5] ++ -8 :: [6]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try (compute; discriminate)).
Qed.