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
  [300; 500; 6; 7; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -104; -901; 800; 29; 5] 
  [-200; 500; 6; -105; 289; 20; 5; -277; 104; 7; 3; 4; 200; 700; 900; 300; -104; -901; 800; 29; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i; [ simpl in *; try congruence | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-200 :: [300; 7; -105; 200; 5; 800]).
        { apply (Permutation_middle _ [300; 7; -105; 200; 5] [800]). }
        apply Permutation_cons.
        transitivity (-105 :: [300; 7; 200; 5; 800]).
        { apply (Permutation_middle _ [300; 7] [200; 5; 800]). }
        apply Permutation_cons.
        transitivity (5 :: [300; 7; 200; 800]).
        { apply (Permutation_middle _ [300; 7; 200] [800]). }
        apply Permutation_cons.
        transitivity (7 :: [300; 200; 800]).
        { apply (Permutation_middle _ [300] [200; 800]). }
        apply Permutation_cons.
        transitivity (200 :: [300; 800]).
        { apply (Permutation_middle _ [300] [800]). }
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try reflexivity ]).
        apply Sorted_nil.
Qed.