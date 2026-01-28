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
  [1; 2; 3; -3; 13; 1; 16; 16; 9; -12; 7; 6; -2; 7] 
  [-12; 2; 3; -3; 13; 1; -2; 16; 9; 1; 7; 6; 16; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for i = 0 to 13 *)
      do 14 (destruct i; [ 
        simpl in *; 
        try (exfalso; compute in H; congruence); 
        try reflexivity 
      | ]).
      (* For i >= 14 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-12; -3; -2; 1; 16] [1; -3; 16; -12; -2] *)
        apply Permutation_sym.
        (* Goal: Permutation [1; -3; 16; -12; -2] [-12; -3; -2; 1; 16] *)
        (* Move -12 to front to match target *)
        apply perm_trans with (l' := -12 :: [1; -3; 16; -2]).
        { change [1; -3; 16; -12; -2] with ([1; -3; 16] ++ -12 :: [-2]). apply Permutation_middle. }
        apply perm_skip.
        (* Move -3 to front *)
        apply perm_trans with (l' := -3 :: [1; 16; -2]).
        { change [1; -3; 16; -2] with ([1] ++ -3 :: [16; -2]). apply Permutation_middle. }
        apply perm_skip.
        (* Move -2 to front *)
        apply perm_trans with (l' := -2 :: [1; 16]).
        { change [1; 16; -2] with ([1; 16] ++ -2 :: []). apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; apply Zle_bool_imp_le; reflexivity) ]).
        apply Sorted_nil.
Qed.