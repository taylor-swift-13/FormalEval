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
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 8; 300; 900; -901; 800; 1000; -901; 1000]
  [4; 6; 7; 20; 8; 289; 104; -105; -277; 290; 200; 3; 300; 700; 8; 300; 900; -901; 800; 1000; -901; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl in *; try lia; try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [300; 290; 20; 104; 4; 300; 800; 1000] with ([300; 290; 20; 104] ++ 4 :: [300; 800; 1000]).
        apply Permutation_cons_app. simpl.
        change [300; 290; 20; 104; 300; 800; 1000] with ([300; 290] ++ 20 :: [104; 300; 800; 1000]).
        apply Permutation_cons_app. simpl.
        change [300; 290; 104; 300; 800; 1000] with ([300; 290] ++ 104 :: [300; 800; 1000]).
        apply Permutation_cons_app. simpl.
        change [300; 290; 300; 800; 1000] with ([300] ++ 290 :: [300; 800; 1000]).
        apply Permutation_cons_app. simpl.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [ simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) | ]).
        apply Sorted_nil.
Qed.