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
  [1; 2; 3; 5; 1; 20; -8; 9; -12; 7; 6; 5; 2] 
  [-8; 2; 3; 1; 1; 20; 2; 9; -12; 5; 6; 5; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 13 (destruct i; [ 
        simpl in *; try reflexivity; try (exfalso; apply H; reflexivity) 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity [-8; 1; 5; 7; 2].
        { apply perm_skip. apply perm_skip.
          transitivity [5; 2; 7].
          - apply perm_swap.
          - apply perm_skip. apply perm_swap. }
        { transitivity [1; -8; 5; 7; 2].
          - apply perm_swap.
          - apply perm_skip. apply perm_swap. }
      * simpl.
        repeat (apply Sorted_cons; [ try apply HdRel_nil; try (apply HdRel_cons; compute; exact I) | ]).
        apply Sorted_nil.
Qed.