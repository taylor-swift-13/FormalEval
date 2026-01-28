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
  [-4; 7; 3; -6; 3; 0; -8; 6; 2; 1; 105; 8; -8; 0] 
  [-8; 7; 3; -8; 3; 0; -6; 6; 2; -4; 105; 8; 1; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check each index 0..13. For indices divisible by 3, H yields a contradiction. *)
      do 14 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); reflexivity | ]).
      (* For indices >= 14, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply Permutation_sym.
        
        (* Goal: Permutation [-4; -6; -8; 1; -8] [-8; -8; -6; -4; 1] *)
        
        (* 1. Move first -8 (from index 2) to front *)
        change (Permutation (([-4; -6] ++ -8 :: [1; -8])) (-8 :: -8 :: -6 :: -4 :: 1 :: [])).
        apply Permutation_trans with (l' := -8 :: ([-4; -6] ++ [1; -8])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* 2. Move -8 (from index 3) to front *)
        change (Permutation (([-4; -6; 1] ++ -8 :: [])) (-8 :: -6 :: -4 :: 1 :: [])).
        apply Permutation_trans with (l' := -8 :: ([-4; -6; 1] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* 3. Move -6 (from index 1) to front *)
        change (Permutation (([-4] ++ -6 :: [1])) (-6 :: -4 :: 1 :: [])).
        apply Permutation_trans with (l' := -6 :: ([-4] ++ [1])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Remaining: Permutation [-4; 1] [-4; 1] *)
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; apply HdRel_cons; apply Zle_bool_imp_le; reflexivity ]).
        apply Sorted_nil.
Qed.