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
  [19; 0; -901; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 17; 19; 21; 20; 200; 2] 
  [2; 0; -901; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 17; 19; 19; 20; 200; 21].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 25 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (2 :: 19 :: 5 :: 8 :: 11 :: 14 :: 17 :: 21 :: 2 :: []).
        { constructor 2. }
        apply Permutation_cons.
        transitivity (2 :: 19 :: 5 :: 8 :: 11 :: 14 :: 17 :: 21 :: []).
        { apply Permutation_sym. apply (Permutation_middle _ [19; 5; 8; 11; 14; 17; 21] [] 2). }
        apply Permutation_cons.
        transitivity (5 :: 19 :: 8 :: 11 :: 14 :: 17 :: 21 :: []).
        { constructor 2. }
        apply Permutation_cons.
        transitivity (8 :: 19 :: 11 :: 14 :: 17 :: 21 :: []).
        { constructor 2. }
        apply Permutation_cons.
        transitivity (11 :: 19 :: 14 :: 17 :: 21 :: []).
        { constructor 2. }
        apply Permutation_cons.
        transitivity (14 :: 19 :: 17 :: 21 :: []).
        { constructor 2. }
        apply Permutation_cons.
        transitivity (17 :: 19 :: 21 :: []).
        { constructor 2. }
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || apply Sorted_nil || constructor ]).
Qed.