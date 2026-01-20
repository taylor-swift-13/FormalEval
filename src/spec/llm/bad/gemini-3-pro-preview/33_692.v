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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -104; -901; 800; 1000; 5] 
  [-901; 500; 6; 4; 8; 289; 5; -105; -277; 7; 200; 3; 20; 5; 700; 104; -200; -104; 300; 800; 1000; 900].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * cbv [extract_thirds app].
        transitivity (-901 :: [300; 7; 20; 104; 4; 900] ++ [5]).
        { apply Permutation_cons. apply Permutation_middle. }
        simpl.
        transitivity (4 :: [300; 7; 20; 104] ++ [900; 5]).
        { apply Permutation_cons. apply Permutation_middle. }
        simpl.
        transitivity (5 :: [300; 7; 20; 104; 900] ++ []).
        { apply Permutation_cons. apply Permutation_middle. }
        simpl.
        transitivity (7 :: [300] ++ [20; 104; 900]).
        { apply Permutation_cons. apply Permutation_middle. }
        simpl.
        transitivity (20 :: [300] ++ [104; 900]).
        { apply Permutation_cons. apply Permutation_middle. }
        simpl.
        transitivity (104 :: [300] ++ [900]).
        { apply Permutation_cons. apply Permutation_middle. }
        simpl.
        apply Permutation_refl.
      * cbv [extract_thirds].
        repeat constructor.
Qed.