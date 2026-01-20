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
  [-4; 3; 105; 3; -1; 10; 14; 0; -8; 6; 2; 0; 1; 8; 14; 0; 6]
  [-4; 3; 105; 0; -1; 10; 1; 0; -8; 3; 2; 0; 6; 8; 14; 14; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 18 (destruct i; [ simpl in H; try (contradiction || reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        change ([3; 14; 6; 1; 0]) with ([3; 14; 6; 1] ++ [0]).
        transitivity ([0] ++ [3; 14; 6; 1]).
        2: apply Permutation_app_comm.
        simpl. apply Permutation_cons.
        change ([3; 14; 6; 1]) with ([3; 14; 6] ++ [1]).
        transitivity ([1] ++ [3; 14; 6]).
        2: apply Permutation_app_comm.
        simpl. apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [| constructor; try (unfold Z.le; simpl; discriminate) ]).
        apply Sorted_nil.
Qed.