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

Definition test_input : list R := [
  -83.09912721681734; 
  72.36056595235235; 
  -65.7881626366349; 
  40.58689270655174; 
  40.58689270655174; 
  -117.53764672581704; 
  -93.33888003792336; 
  95.49028567433459; 
  -93.33888003792336
]%R.

Definition test_output : list R := [
  -93.33888003792336; 
  72.36056595235235; 
  -65.7881626366349; 
  -83.09912721681734; 
  40.58689270655174; 
  -117.53764672581704; 
  40.58689270655174; 
  95.49028567433459; 
  -93.33888003792336
]%R.

Example test_case : sort_third_spec test_input test_output.
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      destruct i; [ simpl in H; contradiction | ].
      destruct i; [ reflexivity | ].
      destruct i; [ reflexivity | ].
      destruct i; [ simpl in H; contradiction | ].
      destruct i; [ reflexivity | ].
      destruct i; [ reflexivity | ].
      destruct i; [ simpl in H; contradiction | ].
      destruct i; [ reflexivity | ].
      destruct i; [ reflexivity | ].
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (l' := [-83.09912721681734; -93.33888003792336; 40.58689270655174]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || (apply HdRel_cons; lra)).
Qed.