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
  [-4; 1; 3; -6; 3; 0; -8; 6; 2; 1; 16; 8; 16; 0; 4; 1; 0] 
  [-8; 1; 3; -6; 3; 0; -4; 6; 2; 1; 16; 8; 1; 0; 4; 16; 0].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 17 (destruct i; [
        simpl in *;
        try (exfalso; apply H; reflexivity);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-8 :: [-4; -6] ++ [1; 16; 1]).
        2: apply Permutation_middle.
        apply perm_skip.
        transitivity (-6 :: [-4] ++ [1; 16; 1]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ 
          try apply HdRel_nil; 
          apply HdRel_cons; 
          apply Z.leb_le; reflexivity 
        | ]).
        apply Sorted_nil.
Qed.