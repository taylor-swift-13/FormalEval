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
  [-4; 6; 3; 3; 0; 6; 2; 1; 800; 0] 
  [-4; 6; 3; 0; 0; 6; 2; 1; 800; 3].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 10 (destruct i; [
        simpl in H;
        try (exfalso; apply H; reflexivity);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        apply Permutation_cons.
        transitivity [2; 0; 3]; [ apply Permutation_swap | ].
        transitivity [2; 3; 0]; [ apply Permutation_cons; apply Permutation_swap | ].
        apply Permutation_swap.
      * vm_compute.
        repeat (apply Sorted_cons; [ | try constructor; auto with zarith ]).
        apply Sorted_nil.
Qed.