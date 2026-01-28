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
  [5; 2; 7; 7; -1; 9; 0; 3; -6; 9; 7; 11; 8; -6; 0; 300; 1; 13; 6; -2; 19]
  [0; 2; 7; 5; -1; 9; 6; 3; -6; 7; 7; 11; 8; -6; 0; 9; 1; 13; 300; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply Permutation_trans.
        { apply (Permutation_cons_app 0 [5; 7] [9; 8; 300; 6]). }
        apply Permutation_cons.
        apply Permutation_cons.
        eapply Permutation_trans.
        { apply (Permutation_cons_app 6 [7; 9; 8; 300] []). }
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; simpl; try lia) ]).
        apply Sorted_nil.
Qed.