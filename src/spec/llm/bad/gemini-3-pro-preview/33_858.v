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
  [-4; 3; 3; 290; 3; 0; -8; 6; 2; 0; 8; 2; 19; 7] 
  [-8; 3; 3; -4; 3; 0; 0; 6; 2; 19; 8; 2; 290; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 14 (destruct i; [
        simpl in H; 
        match goal with 
        | [ H : ?x <> 0 |- _ ] => compute in H; try contradiction 
        end;
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply Permutation_trans with (l' := -8 :: ([-4; 290] ++ [0; 19])).
        2: apply Permutation_middle.
        apply Permutation_cons.
        simpl.
        apply Permutation_cons.
        apply Permutation_trans with (l' := 0 :: ([290] ++ [19])).
        2: apply Permutation_middle.
        apply Permutation_cons.
        simpl.
        apply Permutation_trans with (l' := 19 :: ([290] ++ [])).
        2: apply Permutation_middle.
        apply Permutation_cons.
        simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat constructor.
        all: try (compute; discriminate).
Qed.