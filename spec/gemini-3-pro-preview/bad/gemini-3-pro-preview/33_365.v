Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [1; 2; 3; -3; 6; 300; 4; 9; 0; 7; 6; 0; -3] 
  [-3; 2; 3; -3; 6; 300; 1; 9; 0; 4; 6; 0; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 13 (destruct i as [|i]; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply Permutation_trans with (l' := [-3; 1; 4; 7; -3]). apply perm_swap.
        apply perm_skip.
        apply Permutation_trans with (l' := [1; 4; -3; 7]). do 2 apply perm_skip. apply perm_swap.
        apply Permutation_trans with (l' := [1; -3; 4; 7]). apply perm_skip. apply perm_swap.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.