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

Example test_case : sort_third_spec [1; 2; 3; 4; 5; 6; 7; 45; 9; 12; 14; 15; 3; 13] [1; 2; 3; 3; 5; 6; 4; 45; 9; 7; 14; 15; 12; 13].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; simpl in *; [
        try (exfalso; cbv in H; congruence);
        try reflexivity
      | ]).
      reflexivity.
    + split.
      * simpl.
        apply perm_skip.
        transitivity [4; 3; 7; 12]. apply perm_swap. apply perm_skip.
        transitivity [7; 3; 12]. apply perm_swap. apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_nil; try (apply HdRel_cons; cbv; intro; discriminate)]).
        apply Sorted_nil.
Qed.