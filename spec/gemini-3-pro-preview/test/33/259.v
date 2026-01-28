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
  [-5; 1; 2; -3; 5; 1; 16; 16; -8; 9; -12; 7; 6; -12; 16; 1; 5] 
  [-5; 1; 2; -3; 5; 1; 1; 16; -8; 6; -12; 7; 9; -12; 16; 16; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 17 (destruct i; [
        simpl in *; try reflexivity; try (exfalso; compute in H; apply H; reflexivity)
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        constructor. constructor.
        apply Permutation_rev.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try apply HdRel_cons; compute; congruence]).
        apply Sorted_nil.
Qed.