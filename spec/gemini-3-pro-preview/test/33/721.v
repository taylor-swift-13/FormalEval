Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
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

Example test_case : sort_third_spec 
  [-99.72274847671751%R; -63.93182529303477%R; -83.09912721681734%R; 72.36056595235235%R; 72.36056595235235%R; 40.58689270655174%R; -93.33888003792336%R; 8.760174116134323%R; 8.760174116134323%R; 95.49028567433459%R]
  [-99.72274847671751%R; -63.93182529303477%R; -83.09912721681734%R; -93.33888003792336%R; 72.36056595235235%R; 40.58689270655174%R; 72.36056595235235%R; 8.760174116134323%R; 8.760174116134323%R; 95.49028567433459%R].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 10 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_nil; try (apply HdRel_cons; lra)]).
        apply Sorted_nil.
Qed.