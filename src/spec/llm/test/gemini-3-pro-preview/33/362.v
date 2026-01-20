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
  [-4; 7; 3; -6; 3; 0; -8; -7; 2; 0; 1; 5; 500; 0; 0; -7; 3] 
  [-8; 7; 3; -7; 3; 0; -6; -7; 2; -4; 1; 5; 0; 0; 0; 500; 3].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 17 (destruct i; [ simpl in H; try (exfalso; apply H; reflexivity); simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [-4; -6; -8; 0; 500; -7] with ([-4; -6] ++ -8 :: [0; 500; -7]).
        apply Permutation_trans with (-8 :: [-4; -6] ++ [0; 500; -7]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        change [-4; -6; 0; 500; -7] with ([-4; -6; 0; 500] ++ -7 :: []).
        apply Permutation_trans with (-7 :: [-4; -6; 0; 500] ++ []).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        change [-4; -6; 0; 500] with ([-4] ++ -6 :: [0; 500]).
        apply Permutation_trans with (-6 :: [-4] ++ [0; 500]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        change [-4; 0; 500] with ([] ++ -4 :: [0; 500]).
        apply Permutation_trans with (-4 :: [] ++ [0; 500]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        change [0; 500] with ([] ++ 0 :: [500]).
        apply Permutation_trans with (0 :: [] ++ [500]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; apply Zle_bool_imp_le; reflexivity) ]).
        apply Sorted_nil.
Qed.