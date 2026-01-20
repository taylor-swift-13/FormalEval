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
  [5; 2; 7; 9; 15; 3; 7; -7; 11; 8; 0; 13; 6; -2; 19; 5; 15] 
  [5; 2; 7; 5; 15; 3; 6; -7; 11; 7; 0; 13; 8; -2; 19; 9; 15].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for indices 0 to 16 explicitly *)
      do 17 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      (* For i >= 17, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [5; 5; 6; 7; 8; 9] [5; 9; 7; 8; 6; 5] *)
        apply perm_skip. (* Match first 5 *)
        transitivity (5 :: [9; 7; 8; 6]); [ | apply Permutation_sym; apply Permutation_middle ].
        apply perm_skip. (* Match second 5 *)
        transitivity (6 :: [9; 7; 8]); [ | apply Permutation_sym; apply Permutation_middle ].
        apply perm_skip. (* Match 6 *)
        transitivity (7 :: [9; 8]); [ | apply Permutation_sym; apply Permutation_middle ].
        apply perm_skip. (* Match 7 *)
        apply perm_swap. (* Swap 8 and 9 *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat constructor.
Qed.