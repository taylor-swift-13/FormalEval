Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [-4; 7; 9; -6; 3; 11; -8; 6; 2; -11; 1; 8; 14; 0; 4; 6; 9; 2] 
  [-11; 7; 9; -8; 3; 11; -6; 6; 2; -4; 1; 8; 6; 0; 4; 14; 9; 2].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 18 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      simpl; reflexivity.
    + split.
      * simpl.
        change [-4; -6; -8; -11; 14; 6] with ([-4; -6; -8] ++ -11 :: [14; 6]).
        transitivity (-11 :: ([-4; -6; -8] ++ [14; 6])); [ apply Permutation_cons | apply Permutation_middle ].
        simpl.
        change [-4; -6; -8; 14; 6] with ([-4; -6] ++ -8 :: [14; 6]).
        transitivity (-8 :: ([-4; -6] ++ [14; 6])); [ apply Permutation_cons | apply Permutation_middle ].
        simpl.
        change [-4; -6; 14; 6] with ([-4] ++ -6 :: [14; 6]).
        transitivity (-6 :: ([-4] ++ [14; 6])); [ apply Permutation_cons | apply Permutation_middle ].
        simpl.
        change [-4; 14; 6] with ([] ++ -4 :: [14; 6]).
        transitivity (-4 :: ([] ++ [14; 6])); [ apply Permutation_cons | apply Permutation_middle ].
        simpl.
        change [14; 6] with ([14] ++ 6 :: []).
        transitivity (6 :: ([14] ++ [])); [ apply Permutation_cons | apply Permutation_middle ].
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ simpl; try lia | ]).
        apply Sorted_nil.
Qed.