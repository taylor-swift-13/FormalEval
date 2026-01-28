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
  [29; 9; 8; 7; 6; 5; 4; 1; 0; -6; -1; -3; -4; 800; -5; -7; -8; -9; -11; -2; -1; -6; -1; -1] 
  [-11; 9; 8; -7; 6; 5; -6; 1; 0; -6; -1; -3; -4; 800; -5; 4; -8; -9; 7; -2; -1; 29; -1; -1].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for each index in the list range *)
      do 24 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      (* For indices beyond the list length *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Evaluate extract_thirds to concrete lists first to avoid matching issues *)
        let l1 := eval vm_compute in (extract_thirds [-11; 9; 8; -7; 6; 5; -6; 1; 0; -6; -1; -3; -4; 800; -5; 4; -8; -9; 7; -2; -1; 29; -1; -1] 0) in
        let l2 := eval vm_compute in (extract_thirds [29; 9; 8; 7; 6; 5; 4; 1; 0; -6; -1; -3; -4; 800; -5; -7; -8; -9; -11; -2; -1; -6; -1; -1] 0) in
        change (Permutation l1 l2).
        
        (* l1 (sorted) = [-11; -7; -6; -6; -4; 4; 7; 29] *)
        (* l2 (original) = [29; 7; 4; -6; -4; -7; -11; -6] *)
        
        (* Step 1: Move -11 to front *)
        change [29; 7; 4; -6; -4; -7; -11; -6] with ([29; 7; 4; -6; -4; -7] ++ -11 :: [-6]).
        apply Permutation_trans with (l' := -11 :: ([29; 7; 4; -6; -4; -7] ++ [-6])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Step 2: Move -7 to front *)
        change [29; 7; 4; -6; -4; -7; -6] with ([29; 7; 4; -6; -4] ++ -7 :: [-6]).
        apply Permutation_trans with (l' := -7 :: ([29; 7; 4; -6; -4] ++ [-6])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Step 3: Move -6 to front (first one in LHS) *)
        change [29; 7; 4; -6; -4; -6] with ([29; 7; 4] ++ -6 :: [-4; -6]).
        apply Permutation_trans with (l' := -6 :: ([29; 7; 4] ++ [-4; -6])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Step 4: Move -6 to front (second one in LHS) *)
        change [29; 7; 4; -4; -6] with ([29; 7; 4; -4] ++ -6 :: []).
        apply Permutation_trans with (l' := -6 :: ([29; 7; 4; -4] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Step 5: Move -4 to front *)
        change [29; 7; 4; -4] with ([29; 7; 4] ++ -4 :: []).
        apply Permutation_trans with (l' := -4 :: ([29; 7; 4] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Step 6: Move 4 to front *)
        change [29; 7; 4] with ([29; 7] ++ 4 :: []).
        apply Permutation_trans with (l' := 4 :: ([29; 7] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Step 7: Move 7 to front *)
        change [29; 7] with ([29] ++ 7 :: []).
        apply Permutation_trans with (l' := 7 :: ([29] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Step 8: 29 remains *)
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        let l1 := eval vm_compute in (extract_thirds [-11; 9; 8; -7; 6; 5; -6; 1; 0; -6; -1; -3; -4; 800; -5; 4; -8; -9; 7; -2; -1; 29; -1; -1] 0) in
        change (Sorted Z.le l1).
        repeat (constructor; try (vm_compute; reflexivity)).
Qed.