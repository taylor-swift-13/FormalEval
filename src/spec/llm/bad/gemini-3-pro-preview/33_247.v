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
  [19; 0; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 11; 16] 
  [3; 0; 2; 6; 4; 5; 9; 7; 8; 11; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 19; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply (Permutation_cons_app _ _ [19] [6; 9; 12; 15; 18; 11] 3).
        apply (Permutation_cons_app _ _ [19] [9; 12; 15; 18; 11] 6).
        apply (Permutation_cons_app _ _ [19] [12; 15; 18; 11] 9).
        apply (Permutation_cons_app _ _ [19; 12; 15; 18] [] 11).
        apply (Permutation_cons_app _ _ [19] [15; 18] 12).
        apply (Permutation_cons_app _ _ [19] [18] 15).
        apply (Permutation_cons_app _ _ [19] [] 18).
        apply (Permutation_cons_app _ _ [] [] 19).
        apply Permutation_refl.
      * simpl.
        repeat (constructor; [ compute; try discriminate | ]).
Qed.