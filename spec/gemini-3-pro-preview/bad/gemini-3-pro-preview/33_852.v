Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [-4; 3; 290; 290; 3; 0; -8; 6; 2; 0; 1; -9] 
  [-8; 3; 290; -4; 3; 0; 0; 6; 2; 290; 1; -9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 12 (destruct i; [
        simpl in H; try (apply H; reflexivity);
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        apply perm_trans with (l' := [-8; -4; 290; 0]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply perm_trans with (l' := [-4; -8; 290; 0]).
        { apply perm_swap. }
        { apply perm_skip. apply perm_swap. }
      * vm_compute.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
Qed.