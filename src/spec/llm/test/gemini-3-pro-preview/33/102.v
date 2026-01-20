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
  [1; 2; 3; 4; 3; 5; 6; 7; 45; 9; 11; 6; 12; 13; 15; 3; 13; 3] 
  [1; 2; 3; 3; 3; 5; 4; 7; 45; 6; 11; 6; 9; 13; 15; 12; 13; 3].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 18 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        constructor.
        change [4; 6; 9; 12; 3] with ([4; 6; 9; 12] ++ [3]).
        change [3; 4; 6; 9; 12] with (3 :: [4; 6; 9; 12] ++ []).
        apply Permutation_middle.
      * simpl.
        repeat constructor; apply Z.leb_le; reflexivity.
Qed.