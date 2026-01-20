Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lra.
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
  [-99.7842461107317%R; -99.72274847671751%R; -83.09912721681734%R; -106.70482262238853%R; 72.36056595235235%R; -99.72274847671751%R; -65.7881626366349%R; 40.58689270655174%R; -94.56530028394049%R; -84.10256408187446%R; 8.760174116134323%R; 95.49028567433459%R] 
  [-106.70482262238853%R; -99.72274847671751%R; -83.09912721681734%R; -99.7842461107317%R; 72.36056595235235%R; -99.72274847671751%R; -84.10256408187446%R; 40.58689270655174%R; -94.56530028394049%R; -65.7881626366349%R; 8.760174116134323%R; 95.49028567433459%R].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i; [ simpl in H; try (exfalso; apply H; reflexivity); simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (l' := [-99.7842461107317%R; -106.70482262238853%R; -84.10256408187446%R; -65.7881626366349%R]).
        -- apply perm_swap.
        -- apply perm_skip. apply perm_skip. apply perm_swap.
      * simpl.
        repeat (constructor; try lra).
Qed.