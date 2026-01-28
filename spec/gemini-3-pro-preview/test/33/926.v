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
  [9; 900; 0; 4; 6; 12; 12; 9; 12; 0] 
  [0; 900; 0; 4; 6; 12; 9; 9; 12; 12].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 10 (destruct i as [|i]; [
        vm_compute in H;
        try contradiction;
        vm_compute; reflexivity
      | ]).
      vm_compute. reflexivity.
    + split.
      * vm_compute.
        apply Permutation_trans with (l' := [0; 9; 4; 12]).
        { apply perm_skip. apply perm_swap. }
        { apply Permutation_sym.
          change [9; 4; 12; 0] with ([9; 4; 12] ++ [0]).
          apply Permutation_app_comm. }
      * vm_compute.
        repeat (constructor; try discriminate).
Qed.