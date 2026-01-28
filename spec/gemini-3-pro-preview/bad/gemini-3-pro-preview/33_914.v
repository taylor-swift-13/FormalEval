Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Lemma decimal_le : forall n1 p1 n2 p2, 
  (0 < p1)%Z -> (0 < p2)%Z -> (n1 * p2 <= n2 * p1)%Z -> 
  IZR n1 / IZR p1 <= IZR n2 / IZR p2.
Proof.
  intros n1 p1 n2 p2 Hp1 Hp2 Hle.
  apply Rmult_le_reg_r with (r := IZR p1 * IZR p2).
  - apply Rmult_lt_0_compat; apply IZR_lt; assumption.
  - replace (IZR n1 / IZR p1 * (IZR p1 * IZR p2)) with (IZR n1 * IZR p2).
    + replace (IZR n2 / IZR p2 * (IZR p1 * IZR p2)) with (IZR n2 * IZR p1).
      * rewrite <- mult_IZR; rewrite <- mult_IZR; apply IZR_le; assumption.
      * unfold Rdiv. rewrite Rmult_assoc. rewrite (Rmult_comm (IZR p1)).
        rewrite <- Rmult_assoc. rewrite Rmult_assoc with (r1 := / IZR p2).
        rewrite Rinv_l.
        -- rewrite Rmult_1_r. reflexivity.
        -- apply IZR_neq. intro Hc. rewrite Hc in Hp2. apply Z.lt_irrefl in Hp2. assumption.
    + unfold Rdiv. rewrite Rmult_assoc. rewrite <- Rmult_assoc with (r1 := / IZR p1).
      rewrite Rinv_l.
      * rewrite Rmult_1_r. reflexivity.
      * apply IZR_neq. intro Hc. rewrite Hc in Hp1. apply Z.lt_irrefl in Hp1. assumption.
Qed.

Example test_case : sort_third_spec 
  [-99.72274847671751%R; -83.09912721681734%R; 72.36056595235235%R; -99.72274847671751%R; -65.7881626366349%R; 40.58689270655174%R; -94.56530028394049%R; 8.760174116134323%R; -100.43365896431499%R; 95.49028567433459%R; -65.7881626366349%R; 72.36056595235235%R; -65.7881626366349%R; 95.49028567433459%R] 
  [-99.72274847671751%R; -83.09912721681734%R; 72.36056595235235%R; -99.72274847671751%R; -65.7881626366349%R; 40.58689270655174%R; -94.56530028394049%R; 8.760174116134323%R; -100.43365896431499%R; -65.7881626366349%R; -65.7881626366349%R; 72.36056595235235%R; 95.49028567433459%R; 95.49028567433459%R].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ try (contradict H; discriminate); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        do 3 (apply Permutation_cons; [reflexivity | ]).
        apply Permutation_swap.
        apply Permutation_refl.
      * simpl.
        apply Sorted_cons; [ | apply Sorted_cons; [ | apply Sorted_cons; [ | apply Sorted_cons; [ | apply Sorted_cons; [ | apply Sorted_nil ] ] ] ] ].
        -- apply HdRel_nil.
        -- apply HdRel_cons. apply decimal_le; [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
        -- apply HdRel_cons. apply decimal_le; [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
        -- apply HdRel_cons. apply decimal_le; [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
        -- apply HdRel_cons. apply decimal_le; [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.