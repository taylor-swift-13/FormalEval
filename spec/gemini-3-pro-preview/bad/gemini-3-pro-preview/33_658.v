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
  [5; 2; 7; 9; 15; 3; 7; -7; 11; 8; 0; 1; 13; 6; -2; 19; 5] 
  [5; 2; 7; 7; 15; 3; 8; -7; 11; 9; 0; 1; 13; 6; -2; 19; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 18 (destruct i; [ vm_compute in H; try lia; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (7 :: 9 :: 8 :: 13 :: 19 :: []).
        2: apply Permutation_swap.
        apply Permutation_cons.
        apply Permutation_sym.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; [ lia | ] || apply HdRel_nil | ]); apply Sorted_nil.
Qed.