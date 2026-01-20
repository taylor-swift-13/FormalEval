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
  [19; 0; -901; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 17; 18; 19; 21; 20; 6] 
  [2; 0; -901; 5; 3; 4; 6; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 17; 18; 19; 21; 20; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 25 (destruct i as [|i]; [
        simpl in *;
        try (exfalso; apply H; reflexivity);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        vm_compute.
        apply Permutation_sym.
        (* Target: [2; 5; 6; 8; 11; 14; 17; 19; 19] *)
        (* Source: [19; 2; 5; 8; 11; 14; 17; 19; 6] *)
        
        apply Permutation_trans with (l' := 2 :: [19] ++ [5; 8; 11; 14; 17; 19; 6]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        
        apply Permutation_trans with (l' := 5 :: [19] ++ [8; 11; 14; 17; 19; 6]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        
        apply Permutation_trans with (l' := 6 :: [19; 8; 11; 14; 17; 19] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        
        apply Permutation_trans with (l' := 8 :: [19] ++ [11; 14; 17; 19]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        
        apply Permutation_trans with (l' := 11 :: [19] ++ [14; 17; 19]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        
        apply Permutation_trans with (l' := 14 :: [19] ++ [17; 19]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        
        apply Permutation_trans with (l' := 17 :: [19] ++ [19]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply Permutation_cons.
        
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        repeat (constructor; simpl; try trivial).
Qed.