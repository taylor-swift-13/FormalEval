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
  [29; 9; 8; 7; 6; 5; 4; 1; 0; -6; -1; -3; -4; 800; -5; -7; -8; -9; -11; -2; -1; -6; -1]
  [-11; 9; 8; -7; 6; 5; -6; 1; 0; -6; -1; -3; -4; 800; -5; 4; -8; -9; 7; -2; -1; 29; -1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl in *; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-11 :: [29; 7; 4; -6; -4; -7] ++ [-6]); [ apply perm_skip | apply Permutation_middle ].
        simpl.
        transitivity (-7 :: [29; 7; 4; -6; -4] ++ [-6]); [ apply perm_skip | apply Permutation_middle ].
        simpl.
        transitivity (-6 :: [29; 7; 4] ++ [-4; -6]); [ apply perm_skip | apply Permutation_middle ].
        simpl.
        transitivity (-6 :: [29; 7; 4; -4] ++ []); [ apply perm_skip | apply Permutation_middle ].
        simpl.
        transitivity (-4 :: [29; 7; 4] ++ []); [ apply perm_skip | apply Permutation_middle ].
        simpl.
        transitivity (4 :: [29; 7] ++ []); [ apply perm_skip | apply Permutation_middle ].
        simpl.
        transitivity (7 :: [29] ++ []); [ apply perm_skip | apply Permutation_middle ].
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; unfold Z.le; simpl; discriminate) ]).
        apply Sorted_nil.
Qed.