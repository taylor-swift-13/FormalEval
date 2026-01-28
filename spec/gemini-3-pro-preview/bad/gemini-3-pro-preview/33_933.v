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
  [500; 9; 8; 7; 6; 5; 4; 2; 1; -7; -1; -2; -3; -4; -1; -6; -6; -7; -8; -9; -11; 9; 9]
  [-8; 9; 8; -7; 6; 5; -6; 2; 1; -3; -1; -2; 4; -4; -1; 7; -6; -7; 9; -9; -11; 500; 9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i; [ simpl in H |- *; try reflexivity; try (exfalso; compute in H; discriminate) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -8 :: [500; 7; 4; -7; -3; -6] ++ [9]).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.

        apply Permutation_trans with (l' := -7 :: [500; 7; 4] ++ [-3; -6; 9]).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.

        apply Permutation_trans with (l' := -6 :: [500; 7; 4; -3] ++ [9]).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.

        apply Permutation_trans with (l' := -3 :: [500; 7; 4] ++ [9]).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.

        apply Permutation_trans with (l' := 4 :: [500; 7] ++ [9]).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.

        apply Permutation_trans with (l' := 7 :: [500] ++ [9]).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.

        apply Permutation_trans with (l' := 9 :: [500] ++ []).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip. simpl.

        apply Permutation_refl.
      * simpl.
        repeat constructor.
Qed.