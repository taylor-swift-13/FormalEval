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
  [500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -8; -901; 800; 1000; -277] 
  [-105; 6; 7; -8; 289; 20; 5; -277; 104; 8; 3; 4; 200; 700; 900; 500; -901; 800; 1000; -277].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check indices 0 to 20 explicitly using destruct *)
      do 21 (destruct i as [|i]; [
        simpl in *;
        try (exfalso; apply H; reflexivity); (* Case i mod 3 = 0 *)
        try reflexivity (* Case i mod 3 <> 0 *)
      | ]).
      (* Case i > 20, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-105; -8; 5; 8; 200; 500; 1000] [500; 8; -105; 200; 5; -8; 1000] *)
        
        (* Reorder -105 *)
        transitivity (-105 :: [500; 8] ++ [200; 5; -8; 1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        (* Reorder -8 *)
        simpl.
        transitivity (-8 :: [500; 8; 200; 5] ++ [1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        (* Reorder 5 *)
        simpl.
        transitivity (5 :: [500; 8; 200] ++ [1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        (* Reorder 8 *)
        simpl.
        transitivity (8 :: [500] ++ [200; 1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        (* Reorder 200 *)
        simpl.
        transitivity (200 :: [500] ++ [1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        (* Reorder 500 *)
        simpl.
        apply Permutation_cons.
        
        (* 1000 *)
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; compute; auto]).
        apply Sorted_nil.
Qed.