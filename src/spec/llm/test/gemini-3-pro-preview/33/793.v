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
  [500; 6; 7; 290; 30; 8; 289; 20; 104; -277; 104; 200; 3; 4; -8; 700; -2; -901; 18; 1000; 7] 
  [-277; 6; 7; 3; 30; 8; 18; 20; 104; 289; 104; 200; 290; 4; -8; 500; -2; -901; 700; 1000; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i as [|i]; [ simpl in *; try (exfalso; compute in H; congruence); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [500; 290; 289; -277; 3; 700; 18] with ([500; 290; 289] ++ -277 :: [3; 700; 18]).
        apply Permutation_cons_app. simpl.
        change [500; 290; 289; 3; 700; 18] with ([500; 290; 289] ++ 3 :: [700; 18]).
        apply Permutation_cons_app. simpl.
        change [500; 290; 289; 700; 18] with ([500; 290; 289; 700] ++ 18 :: []).
        apply Permutation_cons_app. simpl.
        change [500; 290; 289; 700] with ([500; 290] ++ 289 :: [700]).
        apply Permutation_cons_app. simpl.
        change [500; 290; 700] with ([500] ++ 290 :: [700]).
        apply Permutation_cons_app. simpl.
        change [500; 700] with ([] ++ 500 :: [700]).
        apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.