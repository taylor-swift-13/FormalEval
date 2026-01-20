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
  [1; 2; 3; -3; 5; 16; 15; 16; -8; 10; -12; 7; 0; -12] 
  [-3; 2; 3; 0; 5; 16; 1; 16; -8; 10; -12; 7; 15; -12].
Proof.
  unfold sort_third_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Indices *)
      intros i H.
      do 14 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* LHS: [-3; 0; 1; 10; 15] *)
        (* RHS: [1; -3; 15; 10; 0] *)
        apply Permutation_trans with (l' := [-3; 1; 0; 10; 15]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [1; -3; 0; 10; 15]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_skip.
        (* Current: [0; 10; 15] vs [15; 10; 0] *)
        apply Permutation_trans with (l' := [0; 15; 10]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [15; 0; 10]).
        { apply perm_swap. }
        apply perm_skip.
        (* Current: [0; 10] vs [10; 0] *)
        apply perm_swap.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try apply HdRel_cons; compute; try discriminate ]).
        apply Sorted_nil.
Qed.