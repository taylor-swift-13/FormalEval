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
  [300; 500; 16; 7; 8; 289; 21; 3; -105; -277; 200; 4; 5; 700; -200; -901; 800; 1000; 300] 
  [-901; 500; 16; -277; 8; 289; 5; 3; -105; 7; 200; 4; 21; 700; -200; 300; 800; 1000; 300].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 19 (destruct i; [ simpl in *; try reflexivity; try (exfalso; compute in H; congruence) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (-901 :: [300; 7; 21; -277; 5; 300]).
        change [300; 7; 21; -277; 5; -901; 300] with ([300; 7; 21; -277; 5] ++ -901 :: [300]).
        apply Permutation_sym, Permutation_middle.
        apply Permutation_cons.
        transitivity (-277 :: [300; 7; 21; 5; 300]).
        change [300; 7; 21; -277; 5; 300] with ([300; 7; 21] ++ -277 :: [5; 300]).
        apply Permutation_sym, Permutation_middle.
        apply Permutation_cons.
        transitivity (5 :: [300; 7; 21; 300]).
        change [300; 7; 21; 5; 300] with ([300; 7; 21] ++ 5 :: [300]).
        apply Permutation_sym, Permutation_middle.
        apply Permutation_cons.
        transitivity (7 :: [300; 21; 300]).
        change [300; 7; 21; 300] with ([300] ++ 7 :: [21; 300]).
        apply Permutation_sym, Permutation_middle.
        apply Permutation_cons.
        transitivity (21 :: [300; 300]).
        change [300; 21; 300] with ([300] ++ 21 :: [300]).
        apply Permutation_sym, Permutation_middle.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ try (apply HdRel_cons; compute; discriminate); try apply HdRel_nil | ]).
        apply Sorted_nil.
Qed.