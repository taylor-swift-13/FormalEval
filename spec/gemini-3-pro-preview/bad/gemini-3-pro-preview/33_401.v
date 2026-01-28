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
  [1; 2; 3; 11; 5; 8; 1; 16; -8; 9; -11; 7; 4; -12; 7; 7; 7] 
  [1; 2; 3; 1; 5; 8; 4; 16; -8; 7; -11; 7; 9; -12; 7; 11; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 17 (destruct i as [|i]; [
        simpl in *;
        match goal with
        | [ H : _ mod 3 <> 0 |- _ ] =>
            try (exfalso; lia);
            try reflexivity
        end
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (1 :: 11 :: 9 :: 4 :: 7 :: nil); [| apply Permutation_swap].
        apply Permutation_cons.
        transitivity (4 :: 11 :: 9 :: 7 :: nil); [| apply Permutation_swap].
        transitivity (11 :: 4 :: 9 :: 7 :: nil); [| apply Permutation_cons; apply Permutation_swap].
        apply Permutation_cons.
        transitivity (7 :: 11 :: 9 :: nil); [| apply Permutation_swap].
        transitivity (11 :: 7 :: 9 :: nil); [| apply Permutation_cons; apply Permutation_swap].
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.