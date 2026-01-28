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
  [300; 500; 300; 6; 289; 290; 8; 289; 20; 104; -277; 104; 200; -8; 700; 900; -901; 800; 1000; 15; -8; 700]
  [6; 500; 300; 8; 289; 290; 104; 289; 20; 200; -277; 104; 300; -8; 700; 700; -901; 800; 900; 15; -8; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [ simpl in H; try (contradict H; reflexivity); reflexivity | ]).
      reflexivity.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [8; 104; 200; 900; 1000; 700]). simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [104; 200; 900; 1000; 700]). simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [200; 900; 1000; 700]). simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [900; 1000; 700]). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [900; 1000; 700]). simpl.
        apply Permutation_cons_app with (l1 := [900; 1000]) (l2 := []). simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; compute; try discriminate ]).
        apply Sorted_nil.
Qed.