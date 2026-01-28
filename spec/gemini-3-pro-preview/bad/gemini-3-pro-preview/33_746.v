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
  [5; 2; 7; 9; 3; -6; 9; 11; 8; -6; 0; 300; 1; 13; 6; -2; 19] 
  [-6; 2; 7; -2; 3; -6; 1; 11; 8; 5; 0; 300; 9; 13; 6; 9; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (-6 :: [5; 9; 9] ++ [1; -2]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        transitivity (-2 :: [5; 9; 9; 1]).
        { apply Permutation_sym. change [5; 9; 9; 1; -2] with ([5; 9; 9; 1] ++ -2 :: []). apply Permutation_middle. }
        apply perm_skip.
        simpl.
        transitivity (1 :: [5; 9; 9]).
        { apply Permutation_sym. change [5; 9; 9; 1] with ([5; 9; 9] ++ 1 :: []). apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; cbv; discriminate) ]).
        apply Sorted_nil.
Qed.