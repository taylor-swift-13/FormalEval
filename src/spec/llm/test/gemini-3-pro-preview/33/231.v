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
  [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; -1; -2; -3; -4; -5; -6; -7; -8; -9; -10; -6]
  [-9; 9; 8; -6; 6; 5; -3; 3; 2; 1; -1; -2; 4; -4; -5; 7; -7; -8; 10; -10; -6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl. apply Permutation_sym. apply Permutation_rev.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; unfold Z.le; simpl; intro Hc; discriminate ] ]).
        apply Sorted_nil.
Qed.