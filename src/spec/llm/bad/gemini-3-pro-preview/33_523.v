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
  [-4; 7; -6; 1000; 0; -8; -6; 8; 6; 2; 289; 1; 7; -8; -6] 
  [-6; 7; -6; -4; 0; -8; 2; 8; 6; 7; 289; 1; 1000; -8; -6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i as [|i]; [ simpl in *; try (intros C; discriminate C); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [-4; 1000; -6; 2; 7] with ([-4; 1000] ++ -6 :: [2; 7]).
        apply Permutation_cons_app. simpl.
        apply Permutation_cons_app. simpl.
        change [1000; 2; 7] with ([1000] ++ 2 :: [7]).
        apply Permutation_cons_app. simpl.
        change [1000; 7] with ([1000] ++ 7 :: []).
        apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; [ compute; reflexivity | ] ]).
        apply Sorted_nil.
        apply HdRel_nil.
Qed.