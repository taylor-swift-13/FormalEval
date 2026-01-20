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
  [9; 12; 3; 6; 15; 0; -3; 18; 30; -9; -9] 
  [-9; 12; 3; -3; 15; 0; 6; 18; 30; 9; -9].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Destruct i sufficient times to cover the list length *)
      do 12 (destruct i; [ simpl in *; try reflexivity; try congruence | ]).
      reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        change [9; 6; -3; -9] with ([9; 6; -3] ++ [-9]).
        apply Permutation_trans with (l' := [-9] ++ [9; 6; -3]).
        2: apply Permutation_app_comm.
        simpl. apply perm_skip.
        change [9; 6; -3] with ([9; 6] ++ [-3]).
        apply Permutation_trans with (l' := [-3] ++ [9; 6]).
        2: apply Permutation_app_comm.
        simpl. apply perm_skip.
        apply perm_swap.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ simpl; red; simpl; intro Hc; discriminate | ]).
        apply Sorted_nil.
Qed.