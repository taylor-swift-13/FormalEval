Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [-4; 7; 3; -6; 3; 0; -8; 6; 2; 0; 19; 1; 8; -200; 0; 6] 
  [-8; 7; 3; -6; 3; 0; -4; 6; 2; 0; 19; 1; 6; -200; 0; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* We handle the first 16 indices individually and the rest as out-of-bounds *)
      do 16 (destruct i as [|i]; [
        simpl in H; try contradiction; simpl; reflexivity
      | ]).
      (* Case i >= 16: both lists have length 16, so nth_error is None for both *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Prove Permutation for the extracted lists:
           LHS (sorted): [-8; -6; -4; 0; 6; 8]
           RHS (input):  [-4; -6; -8; 0; 8; 6] *)
        apply Permutation_trans with (l' := [-6; -8; -4; 0; 6; 8]).
        { apply perm_swap. }
        apply Permutation_trans with (l' := [-6; -4; -8; 0; 6; 8]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [-4; -6; -8; 0; 6; 8]).
        { apply perm_swap. }
        do 4 apply perm_skip.
        apply perm_swap.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try lia).
Qed.