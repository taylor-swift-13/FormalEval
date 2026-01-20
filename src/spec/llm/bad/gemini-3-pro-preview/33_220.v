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
  [1; 2; 3; -3; 5; 1; 16; 16; 9; -12; 7; 6; -12; 7] 
  [-12; 2; 3; -12; 5; 1; -3; 16; 9; 1; 7; 6; 16; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 14 (destruct i; [ simpl; try reflexivity; try (exfalso; compute in H; congruence) | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply Permutation_trans with (l' := 1 :: [-12; -12; -3; 16]).
        { apply Permutation_sym. apply (Permutation_middle _ [-12; -12; -3] [16] 1). }
        apply perm_skip.
        apply Permutation_trans with (l' := -3 :: [-12; -12; 16]).
        { apply Permutation_sym. apply (Permutation_middle _ [-12; -12] [16] (-3)). }
        apply perm_skip.
        apply Permutation_trans with (l' := 16 :: [-12; -12]).
        { apply Permutation_sym. apply (Permutation_middle _ [-12; -12] [] 16). }
        apply perm_skip.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; simpl; try discriminate).
Qed.