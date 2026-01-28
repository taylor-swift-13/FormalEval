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
  [1; 2; 3; -3; 5; 1; 16; -8; 8; -12; 7; 6; 2; 16] 
  [-12; 2; 3; -3; 5; 1; 1; -8; 8; 2; 7; 6; 16; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i; [
        simpl in *;
        try (exfalso; apply H; reflexivity);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        eapply Permutation_trans.
        2: apply (Permutation_middle _ (-12) [1; -3; 16] [2]).
        apply Permutation_cons.
        eapply Permutation_trans.
        2: apply (Permutation_middle _ (-3) [1] [16; 2]).
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (constructor; simpl; try discriminate).
Qed.