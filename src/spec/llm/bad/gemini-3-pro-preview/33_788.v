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
  [500; 6; 7; 290; 8; 289; 20; 104; -277; 200; 3; 4; -8; 700; -2; -901; 800; 1000] 
  [-901; 6; 7; -8; 8; 289; 20; 104; -277; 200; 3; 4; 290; 700; -2; 500; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 19 (destruct i; [ simpl in H; try contradiction; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (-901 :: [500; 290; 20; 200; -8]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (-8 :: [500; 290; 20; 200]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (20 :: [500; 290; 200]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (200 :: [500; 290]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (290 :: [500]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; [ | simpl; try lia ]).
Qed.