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
  [300; 500; 6; 7; 8; 289; -277; 22; -277; 104; 200; 3; 0; 5; 700; 901; 18; -901; 800; 1000; 0; -277; -277] 
  [-277; 500; 6; -277; 8; 289; 0; 22; -277; 7; 200; 3; 104; 5; 700; 300; 18; -901; 800; 1000; 0; 901; -277].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ vm_compute in H; try congruence; vm_compute; reflexivity | ]).
      vm_compute; reflexivity.
    + split.
      * replace (extract_thirds [-277; 500; 6; -277; 8; 289; 0; 22; -277; 7; 200; 3; 104; 5; 700; 300; 18; -901; 800; 1000; 0; 901; -277] 0)
          with [-277; -277; 0; 7; 104; 300; 800; 901] by vm_compute.
        replace (extract_thirds [300; 500; 6; 7; 8; 289; -277; 22; -277; 104; 200; 3; 0; 5; 700; 901; 18; -901; 800; 1000; 0; -277; -277] 0)
          with [300; 7; -277; 104; 0; 901; 800; -277] by vm_compute.
        
        transitivity (-277 :: [300; 7] ++ [104; 0; 901; 800; -277]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (-277 :: [300; 7; 104; 0; 901; 800] ++ []); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (0 :: [300; 7; 104] ++ [901; 800]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (7 :: [300] ++ [104; 901; 800]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (104 :: [300] ++ [901; 800]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (300 :: [] ++ [901; 800]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (800 :: [901] ++ []); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        apply Permutation_refl.
      * vm_compute. repeat constructor.
Qed.