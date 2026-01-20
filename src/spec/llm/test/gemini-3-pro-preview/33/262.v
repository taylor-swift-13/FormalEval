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
  [9; 0; 289; -200; 8; -1; -9; -3; -4; -5; 12; 9] 
  [-200; 0; 289; -9; 8; -1; -5; -3; -4; 9; 12; 9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i; [ simpl in *; try (exfalso; compute in H; congruence); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply perm_trans with (l' := [-200; 9; -9; -5]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := [-9; 9; -5]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_nil.
                 --- apply HdRel_nil.
              ** apply HdRel_cons. unfold Z.le. simpl. discriminate.
           ++ apply HdRel_cons. unfold Z.le. simpl. discriminate.
        -- apply HdRel_cons. unfold Z.le. simpl. discriminate.
Qed.