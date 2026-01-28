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
  [-4; 7; 9; -6; 3; 0; -8; 6; 2; 0; 1; 8; 14; 0; 4; 6; 9] 
  [-8; 7; 9; -6; 3; 0; -4; 6; 2; 0; 1; 8; 6; 0; 4; 14; 9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 17 (destruct i; [
        simpl in *;
        try (match goal with | H : (_ mod 3 <> 0)%nat |- _ =>
             exfalso; apply H; reflexivity
             end);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply Permutation_trans.
        2: { apply Permutation_swap. }
        eapply Permutation_trans.
        2: { apply Permutation_skip. apply Permutation_swap. }
        eapply Permutation_trans.
        2: { apply Permutation_swap. }
        apply Permutation_skip. apply Permutation_skip. apply Permutation_skip. apply Permutation_skip.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; constructor; try (compute; congruence) ]).
        apply Sorted_nil.
Qed.