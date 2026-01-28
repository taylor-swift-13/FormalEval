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
  [500; 9; 8; 7; 6; 5; 4; 2; 1; -6; -1; -3; -4; 800; -5; -7; -8; -9; -11; -2; -1]
  [-11; 9; 8; -7; 6; 5; -6; 2; 1; -4; -1; -3; 4; 800; -5; 7; -8; -9; 500; -2; -1].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for each index i from 0 to 20 *)
      do 21 (destruct i; [ 
        simpl; 
        try reflexivity; 
        try (exfalso; apply H; reflexivity) 
      | ]).
      (* For i >= 21, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-11; -7; -6; -4; 4; 7; 500] [500; 7; 4; -6; -4; -7; -11] *)
        
        (* Strategy: Move matching elements from RHS to the front one by one *)

        (* Move -11 from end to front *)
        assert (H1: Permutation [500; 7; 4; -6; -4; -7; -11] (-11 :: [500; 7; 4; -6; -4; -7])).
        { apply Permutation_sym. apply Permutation_app_comm. }
        rewrite H1. apply perm_skip.
        
        (* Move -7 from end to front *)
        assert (H2: Permutation [500; 7; 4; -6; -4; -7] (-7 :: [500; 7; 4; -6; -4])).
        { apply Permutation_sym. apply Permutation_app_comm. }
        rewrite H2. apply perm_skip.
        
        (* Move -6 from middle to front *)
        (* [500; 7; 4; -6; -4] -> -6 :: [500; 7; 4; -4] *)
        assert (H3: Permutation [500; 7; 4; -6; -4] (-6 :: [500; 7; 4; -4])).
        { change [500; 7; 4; -6; -4] with ([500; 7; 4] ++ -6 :: [-4]).
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H3. apply perm_skip.
        
        (* Move -4 from end to front *)
        assert (H4: Permutation [500; 7; 4; -4] (-4 :: [500; 7; 4])).
        { apply Permutation_sym. apply Permutation_app_comm. }
        rewrite H4. apply perm_skip.
        
        (* Move 4 from end to front *)
        assert (H5: Permutation [500; 7; 4] (4 :: [500; 7])).
        { apply Permutation_sym. apply Permutation_app_comm. }
        rewrite H5. apply perm_skip.
        
        (* Swap 7 and 500 *)
        apply perm_swap.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; apply HdRel_cons; reflexivity ]).
        apply Sorted_nil.
Qed.