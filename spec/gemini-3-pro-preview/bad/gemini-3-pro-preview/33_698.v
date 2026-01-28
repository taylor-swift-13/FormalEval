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
  [300; 500; 6; 7; 290; 8; 289; 20; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; -901] 
  [-901; 500; 6; -901; 290; 8; 4; 20; -277; 7; 200; 3; 104; 700; 900; 289; 800; 1000; 300].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [
        simpl in *; try (exfalso; apply H; reflexivity); try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 289; 104; 4]). simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 289; 104; 4]). simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 289; 104]). simpl.
        apply Permutation_cons_app with (l1 := [300]). simpl.
        apply Permutation_cons_app with (l1 := [300; 289]). simpl.
        apply Permutation_cons_app with (l1 := [300]). simpl.
        apply Permutation_cons_app with (l1 := []). simpl.
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.