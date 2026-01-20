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
  [300; 500; 6; 7; 8; 289; 103; 20; -105; 104; 3; 7; 3; 12; 5; 700; 900; -901; 800; 1000]
  [3; 500; 6; 7; 8; 289; 103; 20; -105; 104; 3; 7; 300; 12; 5; 700; 900; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. Indices not divisible by 3 *)
      intros i H.
      (* Handle indices 0 to 19 individually to avoid complex symbolic reasoning *)
      do 20 (destruct i; [
        (* Check if i mod 3 <> 0. If false, H is contradictory. If true, verify nth_error. *)
        vm_compute in H; try congruence;
        vm_compute; reflexivity
      | ]).
      (* For i >= 20, both lists return None *)
      vm_compute. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* LHS: [3; 7; 103; 104; 300; 700; 800] *)
        (* RHS: [300; 7; 103; 104; 3; 700; 800] *)
        
        (* Move 3 to correct position *)
        apply Permutation_trans with (3 :: [300; 7; 103; 104] ++ [700; 800]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        (* Move 7 to correct position *)
        apply Permutation_trans with (7 :: [300] ++ [103; 104; 700; 800]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        (* Move 103 to correct position *)
        apply Permutation_trans with (103 :: [300] ++ [104; 700; 800]).
        2: apply Permutation_middle.
        apply Permutation_cons.

        (* Move 104 to correct position *)
        apply Permutation_trans with (104 :: [300] ++ [700; 800]).
        2: apply Permutation_middle.
        apply Permutation_cons.

        (* Move 300 to correct position *)
        apply Permutation_trans with (300 :: [] ++ [700; 800]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        apply Permutation_refl.
      * (* 4. Sortedness *)
        simpl.
        repeat (constructor; [ | simpl; try lia ]).
Qed.