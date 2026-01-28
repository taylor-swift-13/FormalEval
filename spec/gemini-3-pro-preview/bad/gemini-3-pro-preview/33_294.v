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
  [30; 1; 2; 3; -3; 5; 1; 16; 16; -8; 4; 9; -12; 7; 6; -12; 16]
  [-12; 1; 2; -12; -3; 5; -8; 16; 16; 1; 4; 9; 3; 7; 6; 30; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 17 (destruct i; [
        simpl in H; try discriminate; simpl; reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-12 :: [30; 3; 1; -8] ++ [-12]).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (-12 :: [30; 3; 1; -8] ++ []).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (-8 :: [30; 3; 1] ++ []).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (1 :: [30; 3] ++ []).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [
          match goal with
          | |- HdRel _ _ [] => apply HdRel_nil
          | |- HdRel _ _ (_::_) => apply HdRel_cons; compute; discriminate
          end
        | ]).
        apply Sorted_nil.
Qed.