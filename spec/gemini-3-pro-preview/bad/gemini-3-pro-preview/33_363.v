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
  [2; 3; -3; 1; 16; 16; -8; 9; -12; 19; 7; 6; -12; 16; 7] 
  [-12; 3; -3; -8; 16; 16; 1; 9; -12; 2; 7; 6; 19; 16; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i as [|i]; [
        simpl in H;
        try (exfalso; apply H; reflexivity);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-12 :: [2; 1; -8; 19]).
        2: apply Permutation_middle.
        apply perm_skip.
        transitivity (-8 :: [2; 1; 19]).
        2: apply Permutation_middle.
        apply perm_skip.
        transitivity (1 :: [2; 19]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.