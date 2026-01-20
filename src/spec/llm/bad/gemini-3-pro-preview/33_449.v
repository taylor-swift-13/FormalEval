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
  [16; 3; -6; 3; 0; 21; 6; 2; 1; 8; 14] 
  [3; 3; -6; 6; 0; 21; 8; 2; 1; 16; 14].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Check indices 0 to 11 *)
      do 12 (destruct i as [|i]; [
        simpl in H; try contradiction; simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        (* Goal: Permutation [3; 6; 8; 16] [16; 3; 6; 8] *)
        apply Permutation_sym.
        (* Goal: Permutation [16; 3; 6; 8] [3; 6; 8; 16] *)
        eapply Permutation_trans.
        apply Permutation_swap.
        apply Permutation_skip.
        eapply Permutation_trans.
        apply Permutation_swap.
        apply Permutation_skip.
        apply Permutation_swap.
      * simpl.
        repeat (constructor; simpl; try discriminate).
Qed.