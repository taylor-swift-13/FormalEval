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
  [1; 2; 3; 5; 1; 0; -8; 9; 200; -12; 7; 6; 6; 1; -13; 9] 
  [-12; 2; 3; -8; 1; 0; 1; 9; 200; 5; 7; 6; 6; 1; -13; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i to handle each index 0..15 individually. *)
      do 16 (destruct i; [ 
        simpl in *; 
        try (exfalso; compute in H; congruence); (* Solves cases where i mod 3 = 0 by contradiction *)
        try reflexivity (* Solves cases where i mod 3 <> 0 by checking equality *)
      | ]).
      (* For i >= 16, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-12; -8; 1; 5; 6; 9] [1; 5; -8; -12; 6; 9] *)
        (* We reorder the RHS to match LHS using transitivity and Permutation_middle *)
        
        (* Move -12 to front *)
        transitivity (-12 :: [1; 5; -8; 6; 9]).
        2: { change [1; 5; -8; -12; 6; 9] with ([1; 5; -8] ++ -12 :: [6; 9]). 
             apply Permutation_sym, Permutation_middle. }
        apply perm_skip.
        
        (* Move -8 to front *)
        transitivity (-8 :: [1; 5; 6; 9]).
        2: { change [1; 5; -8; 6; 9] with ([1; 5] ++ -8 :: [6; 9]).
             apply Permutation_sym, Permutation_middle. }
        apply perm_skip.
        
        (* The rest matches *)
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.