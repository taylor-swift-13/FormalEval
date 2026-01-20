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

Definition d1 := -99.72274847671751%R.
Definition d2 := -83.09912721681734%R.
Definition d3 := 72.36056595235235%R.
Definition d4 := 40.58689270655174%R.
Definition d5 := -93.33888003792336%R.
Definition d6 := 8.760174116134323%R.
Definition d7 := 95.49028567433459%R.

Example test_case : sort_third_spec 
  [d1; d2; d3; d4; d5; d6; d7] 
  [d1; d2; d3; d4; d5; d6; d7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H. reflexivity.
    + split.
      * simpl. apply Permutation_refl.
      * simpl.
        unfold d1, d4, d7.
        repeat constructor; try lra.
Qed.