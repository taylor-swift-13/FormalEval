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
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 3; 4; 700; 900; -901; 800; 1000; -901; -277]
  [-901; 500; 6; -901; 290; 8; -277; 20; -105; 4; 104; 3; 7; 700; 900; 289; 800; 1000; 300; -277].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-901 :: [300; 7; 289; -277; 4] ++ [-901]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        transitivity (-901 :: [300; 7; 289; -277; 4] ++ []).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        transitivity (-277 :: [300; 7; 289] ++ [4]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        transitivity (4 :: [300; 7; 289] ++ []).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        transitivity (7 :: [300] ++ [289]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        transitivity (289 :: [300] ++ []).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat constructor.
Qed.