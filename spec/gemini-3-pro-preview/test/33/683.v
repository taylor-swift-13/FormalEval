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
  [300; 500; 6; 7; -901; 8; 289; 20; -105; -277; 104; 5; 200; 3; 4; 5; 700; 900; -901; 800; 1000; 900]
  [-901; 500; 6; -277; -901; 8; 5; 20; -105; 7; 104; 5; 200; 3; 4; 289; 700; 900; 300; 800; 1000; 900].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 289; -277; 200; 5]) (l2 := [900]).
        simpl. apply Permutation_cons_app with (l1 := [300; 7; 289]) (l2 := [200; 5; 900]).
        simpl. apply Permutation_cons_app with (l1 := [300; 7; 289; 200]) (l2 := [900]).
        simpl. apply Permutation_cons_app with (l1 := [300]) (l2 := [289; 200; 900]).
        simpl. apply Permutation_cons_app with (l1 := [300; 289]) (l2 := [900]).
        simpl. apply Permutation_cons_app with (l1 := [300]) (l2 := [900]).
        simpl. apply Permutation_cons_app with (l1 := []) (l2 := [900]).
        simpl. apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil).
        all: try (simpl; intro H; inversion H).
Qed.