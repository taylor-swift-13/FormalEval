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
  [7; 3; -6; 3; 0; -8; 6; 2; 2; 1; 8; 14; 1; 6] 
  [1; 3; -6; 1; 0; -8; 3; 2; 2; 6; 8; 14; 7; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i; [ simpl in *; try reflexivity; exfalso; apply H; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        assert (move_last: forall A (x:A) l, Permutation (x::l) (l ++ [x])).
        { intros A0 x0 l0. induction l0; simpl; auto. 
          eapply Permutation_trans. apply perm_swap. apply perm_skip. apply IHl0. }
        apply Permutation_sym.
        transitivity (1 :: [7; 3; 6; 1]).
        { change [7; 3; 6; 1; 1] with ([7; 3; 6; 1] ++ [1]). apply Permutation_sym. apply move_last. }
        apply perm_skip.
        transitivity (1 :: [7; 3; 6]).
        { change [7; 3; 6; 1] with ([7; 3; 6] ++ [1]). apply Permutation_sym. apply move_last. }
        apply perm_skip.
        transitivity (3 :: [7; 6]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || apply HdRel_cons).
        all: try (compute; discriminate).
Qed.