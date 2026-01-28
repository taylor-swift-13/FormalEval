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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 7; 3; 4; 8; 700; 900; 16; -901; 800; 1000]
  [-901; 500; 6; 3; 8; 289; 7; -105; -277; 20; 200; 7; 104; 4; 8; 300; 900; 16; 700; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check each of the 21 indices specifically using destruct *)
      do 21 (destruct i as [|i]; [
        vm_compute in H; try contradiction;
        vm_compute; reflexivity
      | ]).
      (* For i >= 21, both nth_error return None *)
      vm_compute. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        vm_compute.
        (* Goal: Permutation [-901; 3; 7; 20; 104; 300; 700] [300; 7; 20; 104; 3; 700; -901] *)
        (* We reorder the RHS to match LHS one element at a time *)
        
        (* 1. Move -901 to front *)
        transitivity (-901 :: [300; 7; 20; 104; 3; 700]).
        { apply Permutation_sym. apply (Permutation_middle _ [300; 7; 20; 104; 3; 700] []). }
        apply Permutation_cons.
        
        (* 2. Move 3 to front *)
        transitivity (3 :: [300; 7; 20; 104; 700]).
        { apply Permutation_sym. apply (Permutation_middle _ [300; 7; 20; 104] [700]). }
        apply Permutation_cons.
        
        (* 3. Move 7 to front *)
        transitivity (7 :: [300; 20; 104; 700]).
        { apply Permutation_sym. apply (Permutation_middle _ [300] [20; 104; 700]). }
        apply Permutation_cons.
        
        (* 4. Move 20 to front *)
        transitivity (20 :: [300; 104; 700]).
        { apply Permutation_sym. apply (Permutation_middle _ [300] [104; 700]). }
        apply Permutation_cons.
        
        (* 5. Move 104 to front *)
        transitivity (104 :: [300; 700]).
        { apply Permutation_sym. apply (Permutation_middle _ [300] [700]). }
        apply Permutation_cons.
        
        (* 6. Move 300 to front *)
        transitivity (300 :: [700]).
        { apply Permutation_sym. apply (Permutation_middle _ [] [700]). }
        apply Permutation_cons.
        
        (* 7. Final element *)
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        repeat constructor.
Qed.