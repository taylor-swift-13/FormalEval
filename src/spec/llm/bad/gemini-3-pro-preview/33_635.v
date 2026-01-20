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
  [500; 6; 7; 290; 8; 289; 20; 104; -277; 104; 200; 3; 4; -8; 700; 900; -901; 800; 1000] 
  [4; 6; 7; 20; 8; 289; 104; 104; -277; 290; 200; 3; 500; -8; 700; 900; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i as [|i]; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (4 :: [500; 290; 20; 104] ++ [900; 1000]).
        apply Permutation_cons. 2: apply Permutation_middle.
        transitivity (20 :: [500; 290] ++ [104; 900; 1000]).
        apply Permutation_cons. 2: apply Permutation_middle.
        transitivity (104 :: [500; 290] ++ [900; 1000]).
        apply Permutation_cons. 2: apply Permutation_middle.
        transitivity (290 :: [500] ++ [900; 1000]).
        apply Permutation_cons. 2: apply Permutation_middle.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try (compute; congruence)).
Qed.