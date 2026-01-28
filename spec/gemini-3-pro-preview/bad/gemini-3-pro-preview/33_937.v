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
  [5; 2; 7; 9; 3; 7; -7; 11; 8; 0; 1; 13; 6; -2; 19; 5] 
  [-7; 2; 7; 0; 3; 7; 5; 11; 8; 5; 1; 13; 6; -2; 19; 9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i; [ simpl in H; try discriminate; reflexivity | simpl ]).
      reflexivity.
    + split.
      * simpl.
        apply (Permutation_trans (l' := -7 :: [5; 9; 0; 6; 5])).
        2: { apply Permutation_sym. apply (Permutation_middle _ _ [5; 9] [0; 6; 5]). }
        apply Permutation_cons.
        apply (Permutation_trans (l' := 0 :: [5; 9; 6; 5])).
        2: { apply Permutation_sym. apply (Permutation_middle _ _ [5; 9] [6; 5]). }
        apply Permutation_cons.
        apply Permutation_cons.
        apply (Permutation_trans (l' := 5 :: [9; 6])).
        2: { apply Permutation_sym. apply (Permutation_middle _ _ [9; 6] []). }
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try apply HdRel_cons; lia]).
        apply Sorted_nil.
Qed.