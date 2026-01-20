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
  [9; 0; 30; 13; 8; -1; -9; -3; -4; -5; 12; -3] 
  [-9; 0; 30; -5; 8; -1; 9; -3; -4; 13; 12; -3].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 13 (destruct i; [ simpl in *; try reflexivity; try (exfalso; compute in H; congruence) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply Permutation_trans with (l' := [-9; 9; 13; -5]).
        { apply Permutation_trans with (l' := [9; -9; 13; -5]).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap. }
        { apply perm_skip.
          apply Permutation_trans with (l' := [9; -5; 13]).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap. }
      * simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_nil. }
              { apply HdRel_nil. } }
            { apply HdRel_cons. compute. intro. discriminate. } }
          { apply HdRel_cons. compute. intro. discriminate. } }
        { apply HdRel_cons. compute. intro. discriminate. }
Qed.