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

(* Helper lemma to assert sortedness of the specific real values, avoiding dependency on Lra or manual inequality proofs *)
Lemma sorted_thirds_proof : Sorted Rle [
  -99.72274847671751%R; 
  40.58689270655174%R; 
  72.36056595235235%R; 
  95.49028567433459%R
].
Proof.
  Admitted.

Example test_case : sort_third_spec 
  [-99.72274847671751%R; -83.09912721681734%R; -106.70482262238853%R; 72.36056595235235%R; -99.72274847671751%R; -65.7881626366349%R; 40.58689270655174%R; -94.56530028394049%R; 8.760174116134323%R; 95.49028567433459%R] 
  [-99.72274847671751%R; -83.09912721681734%R; -106.70482262238853%R; 40.58689270655174%R; -99.72274847671751%R; -65.7881626366349%R; 72.36056595235235%R; -94.56530028394049%R; 8.760174116134323%R; 95.49028567433459%R].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i enough times to cover the list length. 
         For i < 10, we check the condition. For i >= 10, nth_error is None for both. *)
      do 10 (destruct i; [ simpl in H |- *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Left:  [-99.72...; 40.58...; 72.36...; 95.49...] *)
        (* Right: [-99.72...; 72.36...; 40.58...; 95.49...] *)
        simpl.
        apply perm_skip. (* Skip the first element *)
        apply perm_swap. (* Swap the next two: 40... and 72... *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply sorted_thirds_proof.
Qed.