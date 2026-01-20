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
  [300; 500; 6; 7; 8; 289; 103; 20; -105; -277; 104; 8; 7; 3; 12; 4; 5; 700; 900; -901; 800; 1000]
  [-277; 500; 6; 4; 8; 289; 7; 20; -105; 7; 104; 8; 103; 3; 12; 300; 5; 700; 900; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i as [|i]; [
        simpl in *; try reflexivity; try contradiction
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 103]) (l2 := [7; 4; 900; 1000]). simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 103; 7]) (l2 := [900; 1000]). simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [103; 7; 900; 1000]). simpl.
        apply Permutation_cons_app with (l1 := [300; 103]) (l2 := [900; 1000]). simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [900; 1000]). simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; red; discriminate ]).
        apply Sorted_nil.
Qed.