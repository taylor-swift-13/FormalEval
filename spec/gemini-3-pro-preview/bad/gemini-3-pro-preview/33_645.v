Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [5; 2; 7; 9; 3; -6; 8; -6; 0; 300; 1; 13; 6; -2; 19] 
  [5; 2; 7; 6; 3; -6; 8; -6; 0; 9; 1; 13; 300; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check the first 16 indices explicitly *)
      do 16 (destruct i; [ 
        simpl in *; 
        try contradiction; (* Handles cases where i mod 3 = 0, contradiction with H *)
        try reflexivity    (* Handles cases where elements match *)
      | ]).
      (* For i >= 16, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [5; 6; 8; 9; 300] [5; 9; 8; 300; 6] *)
        apply Permutation_cons.
        (* Goal: Permutation [6; 8; 9; 300] [9; 8; 300; 6] *)
        apply Permutation_sym.
        (* Goal: Permutation [9; 8; 300; 6] [6; 8; 9; 300] *)
        
        (* Observe that [9; 8; 300; 6] is [9; 8; 300] ++ [6] *)
        assert (H_app: [9; 8; 300; 6] = [9; 8; 300] ++ [6]) by reflexivity.
        rewrite H_app. clear H_app.
        
        (* Use Permutation_cons_app to move the last element 6 to the front *)
        (* Permutation_cons_app: Permutation (x :: l1 ++ l2) (l1 ++ x :: l2) *)
        (* Here x=6, l1=[9; 8; 300], l2=[] *)
        apply Permutation_cons_app.
        
        (* Goal: Permutation [6; 8; 9; 300] (6 :: [9; 8; 300]) *)
        (* RHS simplifies to [6; 9; 8; 300] *)
        apply Permutation_cons.
        (* Goal: Permutation [8; 9; 300] [9; 8; 300] *)
        apply Permutation_swap.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [5; 6; 8; 9; 300] *)
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
Qed.