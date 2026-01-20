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
  [1; 2; 3; -3; 5; 16; -278; 15; 16; -8; 10; -12; 7; 0; -12; 5] 
  [-278; 2; 3; -8; 5; 16; -3; 15; 16; 1; 10; -12; 5; 0; -12; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 17 (destruct i; [ simpl in *; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [-278; -8; -3; 1; 5; 7] [1; -3; -278; -8; 7; 5] *)
        apply Permutation_sym.
        (* Move -278 to front *)
        apply Permutation_trans with (l' := -3 :: 1 :: -278 :: -8 :: 7 :: 5 :: []).
        { apply perm_swap. }
        apply Permutation_trans with (l' := -3 :: -278 :: 1 :: -8 :: 7 :: 5 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -278 :: -3 :: 1 :: -8 :: 7 :: 5 :: []).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Move -8 to front of remaining *)
        apply Permutation_trans with (l' := -3 :: -8 :: 1 :: 7 :: 5 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -8 :: -3 :: 1 :: 7 :: 5 :: []).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Permutation [-3; 1; 7; 5] [-3; 1; 5; 7] *)
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ (apply HdRel_cons; unfold Z.le; simpl; discriminate) || apply HdRel_nil | ]).
        apply Sorted_nil.
Qed.