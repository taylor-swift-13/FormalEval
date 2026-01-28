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

Example test_case : sort_third_spec [1; 2; 3; -3; 5; 1; 16; -8; 9; 2; -12; 7; 7; 6; 1; 16] [-3; 2; 3; 1; 5; 1; 2; -8; 9; 7; -12; 7; 16; 6; 1; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Destruct i enough times to cover all indices of the list (0 to 16) *)
      do 17 (destruct i; [ simpl in *; try congruence; try reflexivity | ]).
      (* For any i >= 17, both nth_error return None *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Prove Permutation [-3; 1; 2; 7; 16; 16] [1; -3; 16; 2; 7; 16] *)
        apply perm_trans with (l' := [-3; 1; 16; 2; 7; 16]).
        2: apply perm_swap.
        apply perm_skip. apply perm_skip.
        apply perm_trans with (l' := [2; 16; 7; 16]).
        2: apply perm_swap.
        apply perm_skip. apply perm_skip.
        apply perm_swap.
      * simpl.
        (* Prove Sorted Z.le [-3; 1; 2; 7; 16; 16] *)
        repeat (apply Sorted_cons; [ simpl; try apply HdRel_nil; try (apply HdRel_cons; cbv; discriminate) | ]).
        apply Sorted_nil.
Qed.