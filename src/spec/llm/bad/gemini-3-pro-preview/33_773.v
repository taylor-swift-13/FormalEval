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
  [-4; 3; 289; 290; 3; 0; -8; 6; 2; 0; 1; -9; 8] 
  [-8; 3; 289; -4; 3; 0; 0; 6; 2; 8; 1; -9; 290].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 13 (destruct i; [ simpl in *; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (l' := 290 :: -4 :: -8 :: 0 :: 8 :: []).
        { constructor. }
        apply perm_trans with (l' := 290 :: -8 :: -4 :: 0 :: 8 :: []).
        { apply perm_skip. constructor. }
        apply perm_trans with (l' := -8 :: 290 :: -4 :: 0 :: 8 :: []).
        { constructor. }
        apply perm_skip.
        apply perm_trans with (l' := -4 :: 290 :: 0 :: 8 :: []).
        { constructor. }
        apply perm_skip.
        apply perm_trans with (l' := 0 :: 290 :: 8 :: []).
        { constructor. }
        apply perm_skip.
        constructor.
      * simpl.
        repeat apply Sorted_cons.
        all: try apply Sorted_nil.
        all: try apply HdRel_nil.
        all: apply Zle_bool_imp_le; reflexivity.
Qed.