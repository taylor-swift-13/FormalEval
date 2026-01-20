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
  [-4; 7; 105; 3; 3; 0; 7; -8; -2; 2; 0; 12; 1; 20; 0; 0; 0; 1] 
  [-4; 7; 105; 0; 3; 0; 1; -8; -2; 2; 0; 12; 3; 20; 0; 7; 0; 1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 19 (destruct i; [ simpl in H; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        constructor.
        transitivity (0 :: [3; 7; 2; 1]); [| change [3; 7; 2; 1; 0] with ([3; 7; 2; 1] ++ [0]); apply Permutation_middle ].
        constructor.
        transitivity (1 :: [3; 7; 2]); [| change [3; 7; 2; 1] with ([3; 7; 2] ++ [1]); apply Permutation_middle ].
        constructor.
        transitivity (2 :: [3; 7]); [| change [3; 7; 2] with ([3; 7] ++ [2]); apply Permutation_middle ].
        constructor.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; simpl; try discriminate).
Qed.