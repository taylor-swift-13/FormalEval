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
  [9; 0; 3; -4; 9; -5; 1; 17; 12; -4; 12] 
  [-4; 0; 3; -4; 9; -5; 1; 17; 12; 9; 12].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for i = 0 to 11 *)
      do 12 (destruct i; [ 
        try (simpl in H; exfalso; apply H; reflexivity); 
        simpl; reflexivity 
      | ]).
      (* For i >= 12 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-4; -4; 1; 9] [9; -4; 1; -4] *)
        apply Permutation_sym.
        apply perm_trans with (l' := -4 :: 9 :: 1 :: -4 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := 1 :: 9 :: -4 :: []).
        { apply perm_swap. }
        apply perm_trans with (l' := 1 :: -4 :: 9 :: []).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply Z.le_refl; try (apply Zle_bool_imp_le; reflexivity) ]).
        apply Sorted_nil.
Qed.