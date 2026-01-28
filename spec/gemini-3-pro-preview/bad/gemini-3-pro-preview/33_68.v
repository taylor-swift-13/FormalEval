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
  [46; 40; 32; 77; 22; 18; 77; 57; 88; 66; 54; 54; 66] 
  [46; 40; 32; 66; 22; 18; 66; 57; 88; 77; 54; 54; 77].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i as [|i]; [
        simpl in H; 
        try contradiction;
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        change [66; 66; 77; 77] with ([66; 66] ++ [77; 77]).
        change [77; 77; 66; 66] with ([77; 77] ++ [66; 66]).
        apply Permutation_app_comm.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; constructor; unfold Z.le; simpl; discriminate ]).
        apply Sorted_nil.
Qed.