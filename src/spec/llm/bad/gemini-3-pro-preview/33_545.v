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
  [500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 5; 700; 900; -901; 800; -11; 4] 
  [-105; 6; 7; -11; 289; 20; 8; -277; 104; 200; 3; 4; 500; 5; 700; 700; -901; 800; 900; 4].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* The list has length 20. We destruct i 20 times to handle each index concretely. *)
      do 20 (destruct i; [
        simpl in H; 
        try (exfalso; apply H; reflexivity); (* Case i mod 3 = 0, H is False *)
        simpl; reflexivity (* Case i mod 3 <> 0, check values *)
      | ]).
      (* Case i >= 20, both nth_error return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* extracted res: [-105; -11; 8; 200; 500; 700; 900] *)
        (* extracted l:   [500; 8; -105; 200; 700; 900; -11] *)
        
        (* Move -105 to front *)
        apply Permutation_trans with (l' := -105 :: [500; 8] ++ [200; 700; 900; -11]).
        2: apply (Permutation_middle _ [500; 8]).
        apply Permutation_cons.
        
        (* Move -11 to front *)
        apply Permutation_trans with (l' := -11 :: [500; 8; 200; 700; 900] ++ []).
        2: apply (Permutation_middle _ [500; 8; 200; 700; 900]).
        apply Permutation_cons.
        
        (* Move 8 to front *)
        apply Permutation_trans with (l' := 8 :: [500] ++ [200; 700; 900]).
        2: apply (Permutation_middle _ [500]).
        apply Permutation_cons.
        
        (* Move 200 to front *)
        apply Permutation_trans with (l' := 200 :: [500] ++ [700; 900]).
        2: apply (Permutation_middle _ [500]).
        apply Permutation_cons.
        
        (* Remaining: [500; 700; 900] Permutation [500; 700; 900] *)
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.