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
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; -901; 20; 3; 6; 8] 
  [-901; 6; 7; -901; 8; 289; 4; -105; -277; 6; 200; 3; 20; 700; 900; 104; 800; 1000; 290; 20; 3; 300; 8].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i for all indices up to the length of the list (23).
         For indices < 23, we compute the modulo and check equality.
         For indices >= 23, both lists return None. *)
      do 23 (destruct i as [|i]; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Extracted thirds from res: [-901; -901; 4; 6; 20; 104; 290; 300] *)
        (* Extracted thirds from l:   [300; 290; 20; 104; 4; -901; -901; 6] *)
        cbv [extract_thirds].
        (* We rearrange the right side to match the left side element by element *)
        transitivity (-901 :: [300; 290; 20; 104; 4] ++ [-901; 6]).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        
        transitivity (-901 :: [300; 290; 20; 104; 4] ++ [6]).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        
        transitivity (4 :: [300; 290; 20; 104] ++ [6]).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        
        transitivity (6 :: [300; 290; 20; 104] ++ []).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        
        transitivity (20 :: [300; 290] ++ [104]).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        
        transitivity (104 :: [300; 290] ++ []).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        
        transitivity (290 :: [300] ++ []).
        2: apply Permutation_middle. apply Permutation_cons. simpl.
        
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        cbv [extract_thirds].
        repeat (constructor; try lia).
Qed.