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
  [500; 9; 8; 7; 6; 5; 4; 2; 1; -6; -1; -3; -4; 800; -5; -6; -7; -8; -9; -11; -2; -1]
  [-9; 9; 8; -6; 6; 5; -6; 2; 1; -4; -1; -3; -1; 800; -5; 4; -7; -8; 7; -11; -2; 500].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for i = 0..21. *)
      do 22 (destruct i; [ simpl in H; try (elim H; reflexivity); simpl; reflexivity | ]).
      (* For i >= 22, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Target is [500; 7; 4; -6; -4; -6; -9; -1] *)
        (* Current is [-9; -6; -6; -4; -1; 4; 7; 500] *)
        apply Permutation_cons_app with (l1 := [500; 7; 4; -6; -4; -6]) (l2 := [-1]). simpl.
        apply Permutation_cons_app with (l1 := [500; 7; 4]) (l2 := [-4; -6; -1]). simpl.
        apply Permutation_cons_app with (l1 := [500; 7; 4; -4]) (l2 := [-1]). simpl.
        apply Permutation_cons_app with (l1 := [500; 7; 4]) (l2 := [-1]). simpl.
        apply Permutation_cons_app with (l1 := [500; 7; 4]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := [500; 7]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := [500]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := []). simpl.
        apply Permutation_nil.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; apply Z.leb_le; reflexivity) ]).
        apply Sorted_nil.
Qed.