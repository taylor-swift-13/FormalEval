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
  [-4; 7; 3; -6; 3; 0; -8; 6; 2; 0; 1; 8] 
  [-8; 7; 3; -6; 3; 0; -4; 6; 2; 0; 1; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i; [ simpl; try reflexivity; simpl in H; try contradiction | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := [-8; -4; -6; 0]).
        -- apply perm_skip. apply perm_swap.
        -- apply Permutation_trans with (l' := [-4; -8; -6; 0]).
           ++ apply perm_swap.
           ++ apply perm_skip. apply perm_swap.
      * simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons. compute. discriminate.
        -- apply HdRel_cons. compute. discriminate.
        -- apply HdRel_cons. compute. discriminate.
Qed.