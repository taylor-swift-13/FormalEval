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
  [1; 2; 3; 11; 5; 1; 16; -8; 0; 9; -11; 7; -2; 4; -12; 7; 7] 
  [-2; 2; 3; 1; 5; 1; 7; -8; 0; 9; -11; 7; 11; 4; -12; 16; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We handle the first 17 indices individually *)
      do 17 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      (* For i >= 17, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* LHS (sorted): [-2; 1; 7; 9; 11; 16] *)
        (* RHS (extracted): [1; 11; 16; 9; -2; 7] *)
        
        (* Move -2 to front *)
        apply Permutation_trans with (l' := -2 :: [1; 11; 16; 9] ++ [7]).
        2: { change [1; 11; 16; 9; -2; 7] with ([1; 11; 16; 9] ++ -2 :: [7]). 
             apply Permutation_cons_app. apply Permutation_refl. }
        apply Permutation_cons.
        
        (* Move 1 (already at front of remainder) *)
        apply Permutation_trans with (l' := 1 :: [] ++ [11; 16; 9; 7]).
        2: { simpl. apply Permutation_refl. }
        apply Permutation_cons.
        
        (* Move 7 to front *)
        apply Permutation_trans with (l' := 7 :: [11; 16; 9] ++ []).
        2: { change [11; 16; 9; 7] with ([11; 16; 9] ++ 7 :: []).
             apply Permutation_cons_app. apply Permutation_refl. }
        apply Permutation_cons.
        
        (* Move 9 to front *)
        apply Permutation_trans with (l' := 9 :: [11; 16] ++ []).
        2: { change [11; 16; 9] with ([11; 16] ++ 9 :: []).
             apply Permutation_cons_app. apply Permutation_refl. }
        apply Permutation_cons.
        
        (* Remaining [11; 16] matches *)
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; simpl; lia || apply HdRel_nil]).
        apply Sorted_nil.
Qed.