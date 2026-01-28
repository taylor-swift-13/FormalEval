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
  [5; 2; 7; 9; 3; -7; 11; 8; 0; 1; 13; 6; -2; 19; 13] 
  [-2; 2; 7; 1; 3; -7; 5; 8; 0; 9; 13; 6; 11; 19; 13].
Proof.
  unfold sort_third_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Indices preservation *)
      intros i Hi.
      (* Check each index. 0, 3, 6, ... are skipped by hypothesis. Others must match. *)
      do 15 (destruct i; [ solve [ exfalso; apply Hi; reflexivity | reflexivity ] | ]).
      (* For i >= 15, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* Permutation of thirds *)
        vm_compute.
        (* Goal: Permutation [-2; 1; 5; 9; 11] [5; 9; 11; 1; -2] *)
        apply Permutation_sym.
        change [5; 9; 11; 1; -2] with ([5; 9; 11; 1] ++ [-2]).
        apply Permutation_app_comm.
        simpl.
        apply Permutation_cons.
        change [5; 9; 11; 1] with ([5; 9; 11] ++ [1]).
        apply Permutation_app_comm.
        simpl.
        apply Permutation_refl.
      * (* Sortedness *)
        vm_compute.
        repeat (constructor; simpl; try trivial).
Qed.