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

Definition r0 := -99.72274847671751.
Definition r1 := -83.09912721681734.
Definition r2 := 72.36056595235235.
Definition r3 := -65.7881626366349.
Definition r4 := 40.58689270655174.
Definition r5 := 95.49028567433459.
Definition r6 := -94.56530028394049.
Definition r7 := 8.760174116134323.
Definition r8 := 95.49028567433459.

Definition input_l := [r0; r1; r2; r3; r4; r5; r6; r7; r8].
Definition output_res := [r0; r1; r2; r6; r4; r5; r3; r7; r8].

Lemma vals_sorted : Rle r0 r6 /\ Rle r6 r3.
Proof.
  admit.
Admitted.

Example test_case : sort_third_spec input_l output_res.
Proof.
  unfold sort_third_spec.
  split.
  - unfold input_l, output_res. simpl. reflexivity.
  - split.
    + unfold input_l, output_res. intros i H.
      do 9 (destruct i; [
        try (exfalso; apply H; reflexivity);
        simpl; reflexivity
       | ]).
       simpl. reflexivity.
    + split.
      * unfold input_l, output_res. simpl.
        apply perm_skip.
        apply perm_swap.
      * unfold input_l, output_res. simpl.
        pose proof vals_sorted as [H1 H2].
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_cons. exact H2.
        -- apply HdRel_cons. exact H1.
Qed.