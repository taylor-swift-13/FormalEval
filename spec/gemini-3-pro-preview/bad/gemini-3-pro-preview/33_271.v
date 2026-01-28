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
  [-4; 1; 3; -6; 3; 0; -8; 6; 2; 0; 1; 16; 8; 16; 0; 4; 1; 0] 
  [-8; 1; 3; -6; 3; 0; -4; 6; 2; 0; 1; 16; 4; 16; 0; 8; 1; 0].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [-4; -6; -8; 0; 8; 4] with ([-4; -6] ++ -8 :: [0; 8; 4]).
        apply Permutation_cons_app.
        simpl.
        change ([-4; -6; 0; 8; 4]) with ([-4] ++ -6 :: [0; 8; 4]).
        apply Permutation_cons_app.
        simpl.
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat constructor.
Qed.