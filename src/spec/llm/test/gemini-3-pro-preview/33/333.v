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
  [1; 2; 3; -3; 5; 1; 0; 18; 4; 9; -12; 7; 6] 
  [-3; 2; 3; 0; 5; 1; 1; 18; 4; 6; -12; 7; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check each index i from 0 to 12 and beyond *)
      do 13 (destruct i; [
        (* For each specific i, check if i mod 3 == 0 *)
        try (exfalso; apply H; reflexivity); (* Case: i mod 3 = 0, contradiction *)
        try reflexivity (* Case: i mod 3 <> 0, values must match *)
      |]).
      (* For i >= 13, both lists are empty at index i *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-3; 0; 1; 6; 9] [1; -3; 0; 9; 6] *)
        apply Permutation_sym.
        (* Goal: Permutation [1; -3; 0; 9; 6] [-3; 0; 1; 6; 9] *)
        eapply perm_trans.
        apply perm_swap. (* Swaps first two: [-3; 1; 0; 9; 6] *)
        apply perm_skip. (* Matches -3 *)
        eapply perm_trans.
        apply perm_swap. (* Swaps 1 and 0: [0; 1; 9; 6] *)
        apply perm_skip. (* Matches 0 *)
        apply perm_skip. (* Matches 1 *)
        apply perm_swap. (* Swaps 9 and 6: [6; 9]. Matches 6 and 9. *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [-3; 0; 1; 6; 9] *)
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons. compute. discriminate. (* 6 <= 9 *)
        -- apply HdRel_cons. compute. discriminate. (* 1 <= 6 *)
        -- apply HdRel_cons. compute. discriminate. (* 0 <= 1 *)
        -- apply HdRel_cons. compute. discriminate. (* -3 <= 0 *)
Qed.