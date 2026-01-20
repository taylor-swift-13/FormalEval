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
  [300; 500; 7; 7; -901; 289; -105; -277; 11; 200; 3; 4; 5; 700; 900; -901; 800; 1000; 7; 7]
  [-901; 500; 7; -105; -901; 289; 5; -277; 11; 7; 3; 4; 7; 700; 900; 200; 800; 1000; 300; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Check indices 0 to 20 explicitly. For i >= 21, both are None. *)
      do 21 (destruct i; [ vm_compute in H; try discriminate; vm_compute; reflexivity | ]).
      vm_compute. reflexivity.
    + split.
      * (* Permutation *)
        vm_compute.
        (* Target (sorted): [-901; -105; 5; 7; 7; 200; 300] *)
        (* Source (unsorted): [300; 7; -105; 200; 5; -901; 7] *)
        apply Permutation_cons_app with (l1 := [300; 7; -105; 200; 5]) (l2 := [7]). simpl.
        apply Permutation_cons_app with (l1 := [300; 7]) (l2 := [200; 5; 7]). simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 200]) (l2 := [7]). simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [200; 7]). simpl.
        apply Permutation_cons_app with (l1 := [300; 200]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := []). simpl.
        apply Permutation_nil.
      * (* Sorted *)
        vm_compute.
        repeat (first [ apply Sorted_cons | apply Sorted_nil | apply HdRel_cons | apply HdRel_nil ]).
        all: try (vm_compute; discriminate).
Qed.