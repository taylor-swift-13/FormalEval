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
  [5; 2; 7; 9; 3; -6; -6; 0; 300; 1; 13; 6; -2; 19] 
  [-6; 2; 7; -2; 3; -6; 1; 0; 300; 5; 13; 6; 9; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i; [ simpl in *; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [5; 9; -6; 1; -2] with ([5; 9] ++ -6 :: [1; -2]).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply Permutation_cons.
        simpl.
        change [5; 9; 1; -2] with ([5; 9; 1] ++ -2 :: []).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply Permutation_cons.
        simpl.
        change [5; 9; 1] with ([5; 9] ++ 1 :: []).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply Permutation_cons.
        simpl.
        change [5; 9] with ([] ++ 5 :: [9]).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply Permutation_cons.
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; simpl; try lia).
Qed.