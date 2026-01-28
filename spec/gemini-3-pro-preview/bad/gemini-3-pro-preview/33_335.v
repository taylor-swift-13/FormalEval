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
  [-4; 7; 3; -6; 3; 0; -8; 6; 1; 8; 14] 
  [-8; 7; 3; -6; 3; 0; -4; 6; 1; 8; 14].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices not divisible by 3 *)
      intros i H.
      (* We verify index preservation for all valid indices. *)
      do 11 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      (* For indices beyond the list length, both are None *)
      simpl. reflexivity.
    + split.
      * (* Permutation of extracted thirds *)
        (* Goal: Permutation [-8; -6; -4; 8] [-4; -6; -8; 8] *)
        simpl.
        (* We use transitivity to swap elements into place *)
        (* RHS is [-4; -6; -8; 8]. Swap -4 and -6 to get [-6; -4; -8; 8] *)
        apply Permutation_trans with (l' := [-6; -4; -8; 8]).
        { apply perm_swap. } (* [-4; -6; ...] <-> [-6; -4; ...] *)
        (* Swap -4 and -8 to get [-6; -8; -4; 8] *)
        apply Permutation_trans with (l' := [-6; -8; -4; 8]).
        { apply perm_skip. apply perm_swap. }
        (* Swap -6 and -8 to get [-8; -6; -4; 8] *)
        apply perm_swap.
      * (* Sortedness of extracted thirds *)
        simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons. compute. trivial.
        -- apply HdRel_cons. compute. trivial.
        -- apply HdRel_cons. compute. trivial.
Qed.