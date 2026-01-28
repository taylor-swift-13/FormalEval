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
  [-4; 7; 3; -6; 0; -8; 6; 2; 1; 8; 14; 6; 6; -8; 14] 
  [-6; 7; 3; -4; 0; -8; 6; 2; 1; 6; 14; 6; 8; -8; 14].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* We destruct i enough times to cover the list length (15). 
         For indices divisible by 3, H becomes a contradiction (0 <> 0), solved by congruence.
         For other indices, the values match, solved by reflexivity. *)
      do 15 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      (* For i >= 15, both lists are empty at that index *)
      simpl. reflexivity.
    + split.
      * vm_compute.
        (* Goal: Permutation [-6; -4; 6; 6; 8] [-4; -6; 6; 8; 6] *)
        apply Permutation_trans with (l' := [-4; -6; 6; 6; 8]).
        -- apply perm_swap.
        -- do 3 apply perm_skip.
           apply perm_swap.
      * vm_compute.
        (* Goal: Sorted Z.le [-6; -4; 6; 6; 8] *)
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try apply HdRel_cons; auto with zarith ]).
        apply Sorted_nil.
Qed.