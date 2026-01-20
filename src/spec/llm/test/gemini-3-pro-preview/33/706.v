Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition le_bool (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | true, false => False
  | _, _ => True
  end.

Fixpoint extract_thirds (l : list bool) (i : nat) : list bool :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list bool) (res : list bool) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted le_bool (extract_thirds res 0).

Example test_case : sort_third_spec 
  [false; true; false; false; true; false; true; true; true; true; true] 
  [false; true; false; false; true; false; true; true; true; true; true].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H. reflexivity.
    + split.
      * simpl. apply Permutation_refl.
      * simpl. repeat constructor.
Qed.