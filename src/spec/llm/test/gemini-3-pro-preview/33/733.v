Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [5; 2; 7; 3; -7; 11; 8; -6; 0; 6; 1; 13; 6; -2; 19]
  [3; 2; 7; 5; -7; 11; 6; -6; 0; 6; 1; 13; 8; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in H; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity [5; 3; 6; 6; 8].
        { apply perm_swap. }
        apply perm_skip. apply perm_skip.
        transitivity [6; 8; 6].
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * simpl.
        repeat (constructor; try lia).
Qed.