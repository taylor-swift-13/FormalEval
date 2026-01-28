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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 4; 5; 700; 900; -200; -901; 800; 1000; 6] 
  [-200; 500; 6; 5; 8; 289; 7; -105; -277; 20; 200; 4; 104; 700; 900; 300; -901; 800; 1000; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i as [|i]; [
        simpl in *;
        try (compute in H; congruence);
        reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 20; 104; 5]) (l2 := [1000]).
        apply Permutation_cons_app with (l1 := [300; 7; 20; 104]) (l2 := [1000]).
        apply Permutation_cons_app with (l1 := [300]) (l2 := [20; 104; 1000]).
        apply Permutation_cons_app with (l1 := [300]) (l2 := [104; 1000]).
        apply Permutation_cons_app with (l1 := [300]) (l2 := [1000]).
        apply Permutation_cons_app with (l1 := []) (l2 := [1000]).
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [
          try apply HdRel_nil; try (apply HdRel_cons; vm_compute; reflexivity)
        | ]).
        apply Sorted_nil.
Qed.