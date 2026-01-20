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
  [300; 6; 699; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 801; 19; 104; 3; -901] 
  [-901; 6; 699; 4; 8; 289; 20; -105; -277; 104; 200; 3; 104; 700; 900; 290; 801; 19; 300; 3; -901].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i as [|i]; [
        try (vm_compute in H; discriminate);
        try (vm_compute; reflexivity)
      | ]).
      vm_compute. reflexivity.
    + split.
      * vm_compute.
        apply Permutation_trans with (l' := -901 :: [300; 290; 20; 104; 4; 104]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := 4 :: [300; 290; 20; 104; 104]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := 20 :: [300; 290; 104; 104]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := 104 :: [300; 290; 104]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := 104 :: [300; 290]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := 290 :: [300]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_refl.
      * vm_compute.
        repeat (apply Sorted_cons; [ apply HdRel_cons; [ vm_compute; discriminate | apply HdRel_nil ] | ]).
        apply Sorted_nil.
Qed.