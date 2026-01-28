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
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; -4; -11; 3; 4; 700; 900; -901; 800; 1000]
  [-277; 500; 6; -11; 290; 8; 7; 20; -105; 289; 104; -4; 300; 3; 4; 700; 900; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ try (compute in H; congruence); compute; reflexivity | ]).
      compute. reflexivity.
    + split.
      * simpl.
        transitivity (-277 :: [300; 7; 289] ++ [-11; 700; 800]).
        2: apply Permutation_middle.
        apply perm_skip.
        transitivity (-11 :: [300; 7; 289] ++ [700; 800]).
        2: apply Permutation_middle.
        apply perm_skip.
        transitivity (7 :: [300] ++ [289; 700; 800]).
        2: apply Permutation_middle.
        apply perm_skip.
        transitivity (289 :: [300] ++ [700; 800]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.