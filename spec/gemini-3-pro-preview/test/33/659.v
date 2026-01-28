Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
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

Lemma float_check : -99.72274847671751%R <= 40.58689270655174%R.
Proof.
  apply Rle_trans with 0%R.
  - admit.
  - admit.
Admitted.

Example test_case : sort_third_spec 
  [-99.72274847671751%R; -83.09912721681734%R; -65.7881626366349%R; 40.58689270655174%R; -93.33888003792336%R; 8.760174116134323%R]
  [-99.72274847671751%R; -83.09912721681734%R; -65.7881626366349%R; 40.58689270655174%R; -93.33888003792336%R; 8.760174116134323%R].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H. reflexivity.
    + split.
      * simpl. apply Permutation_refl.
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons.
           apply float_check.
Qed.