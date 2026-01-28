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

Example test_case : sort_third_spec [9; 12; 15; 6; 8; 10; 23; 7; 23; 8] [6; 12; 15; 8; 8; 10; 9; 7; 23; 23].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Check indices 0 to 10 individually to handle mod 3 logic efficiently *)
      do 11 (destruct i; [
        try (vm_compute in H; congruence);
        vm_compute; reflexivity | ]).
      (* Case i > 10 *)
      vm_compute. reflexivity.
    + split.
      * (* Permutation *)
        vm_compute.
        (* LHS: [6; 8; 9; 23], RHS: [9; 6; 23; 8] *)
        (* Step-by-step transformation *)
        apply Permutation_trans with (l' := [6; 9; 8; 23]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [9; 6; 8; 23]).
        { apply perm_swap. }
        apply perm_skip. apply perm_skip. apply perm_swap.
      * (* Sorted *)
        vm_compute.
        repeat (constructor; try (vm_compute; discriminate)).
Qed.