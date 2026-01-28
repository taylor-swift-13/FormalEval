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
  [-99.72274847671751; 58.62972680466558; -83.09912721681734; 72.36056595235235; -99.72274847671751; -65.7881626366349; 40.58689270655174; -94.56530028394049; 6.0403607760564215; 95.49028567433459; -65.7881626366349; 40.58689270655174]
  [-99.72274847671751; 58.62972680466558; -83.09912721681734; 40.58689270655174; -99.72274847671751; -65.7881626366349; 72.36056595235235; -94.56530028394049; 6.0403607760564215; 95.49028567433459; -65.7881626366349; 40.58689270655174].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i; [ simpl in *; try reflexivity; try contradiction | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (constructor; [ try lra | ]).
        apply Sorted_nil.
Qed.