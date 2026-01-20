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
  [-4; 7; 3; -6; 3; 0; -8; 2; 1; 8; 14; 0] 
  [-8; 7; 3; -6; 3; 0; -4; 2; 1; 8; 14; 0].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Verify indices 0 to 12 *)
      repeat (destruct i as [|i]; [
        simpl in H; try (compute in H; congruence);
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        (* Goal: Permutation [-8; -6; -4; 8] [-4; -6; -8; 8] *)
        apply perm_trans with (l' := [-6; -8; -4; 8]).
        apply perm_swap.
        apply perm_trans with (l' := [-6; -4; -8; 8]).
        apply perm_skip. apply perm_swap.
        apply perm_swap.
      * simpl.
        apply Sorted_cons.
        { apply HdRel_cons. simpl. auto with zarith. }
        apply Sorted_cons.
        { apply HdRel_cons. simpl. auto with zarith. }
        apply Sorted_cons.
        { apply HdRel_cons. simpl. auto with zarith. }
        apply Sorted_cons.
        { apply HdRel_nil. }
        apply Sorted_nil.
Qed.