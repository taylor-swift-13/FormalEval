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

Example test_case : sort_third_spec [5; 6; 9; 4; 8; 3; 2] [2; 6; 9; 4; 8; 3; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 8 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply perm_trans.
        apply perm_swap.
        eapply perm_trans.
        apply perm_skip. apply perm_swap.
        apply perm_swap.
      * simpl.
        repeat (constructor; simpl; try lia).
Qed.