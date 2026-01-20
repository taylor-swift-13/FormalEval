Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [9; -5; 29; -276; -6; 12; 9; -6] 
  [-276; -5; 29; 9; -6; 12; 9; -6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 8 (destruct i; [
        simpl; try (exfalso; apply H; reflexivity); reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl. apply perm_swap.
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. simpl. apply Z.le_refl.
        -- apply HdRel_cons. simpl. vm_compute. discriminate.
Qed.