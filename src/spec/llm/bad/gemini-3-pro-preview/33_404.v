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
  [900; 2; 7; 900; 9; 3; -7; 8; 0; 1; -12; 6; -2; 19; 13; 19]
  [-7; 2; 7; -2; 9; 3; 1; 8; 0; 19; -12; 6; 900; 19; 13; 900].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (-7 :: [900; 900; 1; -2; 19]).
        2: { change [900; 900; -7; 1; -2; 19] with ([900; 900] ++ -7 :: [1; -2; 19]).
             apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (-2 :: [900; 900; 1; 19]).
        2: { change [900; 900; 1; -2; 19] with ([900; 900; 1] ++ -2 :: [19]).
             apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (1 :: [900; 900; 19]).
        2: { change [900; 900; 1; 19] with ([900; 900] ++ 1 :: [19]).
             apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (19 :: [900; 900]).
        2: { change [900; 900; 19] with ([900; 900] ++ 19 :: []).
             apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; [ compute; discriminate | ]).
        apply Sorted_nil.
Qed.