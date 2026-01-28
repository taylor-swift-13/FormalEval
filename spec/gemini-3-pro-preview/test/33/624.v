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
  [5; 2; 7; 9; 3; -6; 11; 8; -6; 0; 300; 1; 13; 6; -2; 19] 
  [0; 2; 7; 5; 3; -6; 9; 8; -6; 11; 300; 1; 13; 6; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i; [ simpl in *; try reflexivity; try (exfalso; compute in H; congruence) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (5 :: 0 :: 9 :: 11 :: 13 :: 19 :: []). apply perm_swap.
        apply perm_skip.
        apply perm_trans with (9 :: 0 :: 11 :: 13 :: 19 :: []). apply perm_swap.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; apply HdRel_cons; unfold Z.le; simpl; discriminate ]).
        apply Sorted_nil.
Qed.