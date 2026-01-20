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
  [-4; 7; 3; 289; 290; 3; 0; -8; 6; 2; 0; 8; 2; 7] 
  [-4; 7; 3; 0; 290; 3; 2; -8; 6; 2; 0; 8; 289; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* preservation *)
      intros i H.
      (* Destruct i to handle specific indices. 
         The list length is 14, so we check 0..13. 
         For i >= 14, both nth_errors are None. *)
      do 14 (destruct i; [ 
        simpl in H; try (exfalso; apply H; reflexivity); simpl; reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [-4; 0; 2; 2; 289] [-4; 289; 0; 2; 2] *)
        apply perm_skip.
        apply perm_trans with (l' := [0; 289; 2; 2]).
        { (* Subgoal 1: Permutation [0; 2; 2; 289] [0; 289; 2; 2] *)
          apply perm_skip.
          apply perm_trans with (l' := [2; 289; 2]).
          { (* Subgoal 1.1: Permutation [2; 2; 289] [2; 289; 2] *)
            apply perm_skip.
            apply perm_swap. }
          { (* Subgoal 1.2: Permutation [2; 289; 2] [289; 2; 2] *)
            apply perm_swap. }
        }
        { (* Subgoal 2: Permutation [0; 289; 2; 2] [289; 0; 2; 2] *)
          apply perm_swap. }
      * (* Sorted *)
        simpl.
        repeat (constructor; try (intro C; discriminate C)).
Qed.