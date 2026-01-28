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
  [-4; 7; 15; 3; 0; 105; -8; 2; 1; 8; 14; 0] 
  [-8; 7; 15; -4; 0; 105; 3; 2; 1; 8; 14; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Unroll the loop for the finite list of length 12 *)
      do 12 (destruct i; [
        simpl in *;
        (* For indices divisible by 3, H is contradictory *)
        try (exfalso; vm_compute in H; congruence);
        reflexivity
      | ]).
      (* For i >= 12, both are None *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [-8; -4; 3; 8] [-4; 3; -8; 8] *)
        (* Transitive step: swap first two elements of LHS to get [-4; -8; 3; 8] *)
        apply Permutation_trans with (l' := [-4; -8; 3; 8]).
        { apply Permutation_swap. }
        (* Now match head -4 and swap next two: [-4; -8; 3; 8] -> [-4; 3; -8; 8] *)
        apply Permutation_cons.
        apply Permutation_swap.
      * (* Sorted *)
        simpl.
        (* Verify sortedness of [-8; -4; 3; 8] *)
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_nil. }
              { apply HdRel_nil. }
            }
            { apply HdRel_cons. unfold Z.le. simpl. congruence. }
          }
          { apply HdRel_cons. unfold Z.le. simpl. congruence. }
        }
        { apply HdRel_cons. unfold Z.le. simpl. congruence. }
Qed.