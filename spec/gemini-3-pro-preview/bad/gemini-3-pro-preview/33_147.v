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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; 900; 18; -901; 800; 1000; 0; -277]
  [-277; 500; 6; 0; 8; 289; 7; -105; -277; 20; 200; 3; 104; 5; 700; 300; 18; -901; 800; 1000; 0; 900].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 22 (destruct i as [|i]; [ 
        simpl in H; 
        try (contradiction || discriminate); 
        simpl; reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* We manually construct the permutation proof by bubble sorting the source list to match the target *)
        (* Target (sorted): [-277; 0; 7; 20; 104; 300; 800; 900] *)
        (* Source (extracted): [300; 7; 20; 104; 0; 900; 800; -277] *)
        
        (* Move -277 to front *)
        apply (Permutation_middle _ (-277) [300; 7; 20; 104; 0; 900; 800] []).
        apply Permutation_cons.
        
        (* Move 0 to front *)
        apply (Permutation_middle _ 0 [300; 7; 20; 104] [900; 800]).
        apply Permutation_cons.
        
        (* Move 7 to front *)
        apply (Permutation_middle _ 7 [300] [20; 104; 900; 800]).
        apply Permutation_cons.
        
        (* Move 20 to front *)
        apply (Permutation_middle _ 20 [300] [104; 900; 800]).
        apply Permutation_cons.
        
        (* Move 104 to front *)
        apply (Permutation_middle _ 104 [300] [900; 800]).
        apply Permutation_cons.
        
        (* 300 is already at front *)
        apply Permutation_cons.
        
        (* Move 800 to front *)
        apply (Permutation_middle _ 800 [900] []).
        apply Permutation_cons.
        
        (* 900 is at front *)
        apply Permutation_cons.
        
        apply Permutation_nil.
      * (* Sorted *)
        simpl.
        repeat constructor.
Qed.