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
  [-4; 7; 3; -6; 3; 0; -8; 6; 2; 0; 1; 105; 8; -8; 0] 
  [-8; 7; 3; -6; 3; 0; -4; 6; 2; 0; 1; 105; 8; -8; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Destruct i to cover all elements of the list *)
      do 15 (destruct i; [ 
        simpl in *; 
        try reflexivity; 
        try (exfalso; apply H; reflexivity) 
      | ]).
      (* For i >= 15 *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [-8; -6; -4; 0; 8] [-4; -6; -8; 0; 8] *)
        apply Permutation_sym.
        (* Goal: Permutation [-4; -6; -8; 0; 8] [-8; -6; -4; 0; 8] *)
        eapply Permutation_trans.
        { apply Permutation_skip. apply Permutation_swap. }
        (* Goal: Permutation [-4; -8; -6; 0; 8] [-8; -6; -4; 0; 8] *)
        eapply Permutation_trans.
        { apply Permutation_swap. }
        (* Goal: Permutation [-8; -4; -6; 0; 8] [-8; -6; -4; 0; 8] *)
        apply Permutation_skip.
        (* Goal: Permutation [-4; -6; 0; 8] [-6; -4; 0; 8] *)
        apply Permutation_swap.
      * (* Sorted *)
        simpl.
        (* Prove sortedness by checking each adjacent pair *)
        repeat (apply Sorted_cons; [ | constructor; try (compute; discriminate) ]).
        apply Sorted_nil.
Qed.