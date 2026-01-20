Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint extract_thirds (l : list R) (i : nat) : list R :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list R) (res : list R) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Rle (extract_thirds res 0).

Example test_case : sort_third_spec 
  [-99.72274847671751%R; -83.09912721681734%R; -106.70482262238853%R; 73.18274033266016%R; 6.0403607760564215%R; -65.7881626366349%R; 40.58689270655174%R; -94.56530028394049%R; 8.760174116134323%R; 95.49028567433459%R]
  [-99.72274847671751%R; -83.09912721681734%R; -106.70482262238853%R; 40.58689270655174%R; 6.0403607760564215%R; -65.7881626366349%R; 73.18274033266016%R; -94.56530028394049%R; 8.760174116134323%R; 95.49028567433459%R].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 11 (destruct i; [ try (simpl in H; try discriminate); simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lra | ]).
        apply Sorted_nil.
Qed.