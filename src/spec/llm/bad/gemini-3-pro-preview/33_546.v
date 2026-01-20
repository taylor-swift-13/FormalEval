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
  [300; 500; 6; 2; 7; 8; 6; -277; 22; -277; 104; 200; 3; 0; 5; 901; 18; -901; 800; 1000; 0; -277; -277] 
  [-277; 500; 6; -277; 7; 8; 2; -277; 22; 3; 104; 200; 6; 0; 5; 300; 18; -901; 800; 1000; 0; 901; -277].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ 
        simpl in *; 
        try (exfalso; apply H; reflexivity); 
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        transitivity (-277 :: [300; 2; 6] ++ [3; 901; 800; -277]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (-277 :: [300; 2; 6; 3; 901; 800] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (2 :: [300] ++ [6; 3; 901; 800]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (3 :: [300; 6] ++ [901; 800]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (6 :: [300] ++ [901; 800]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply perm_skip.
        transitivity (800 :: [901] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * vm_compute.
        repeat apply Sorted_cons; [ apply Sorted_nil | apply HdRel_nil | apply HdRel_cons; apply Zle_bool_imp_le; reflexivity .. ].
Qed.