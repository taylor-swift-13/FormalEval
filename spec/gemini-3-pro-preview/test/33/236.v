Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Psatz.
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
  [9; 0; 3; 3; -4; 9; 289; 3; 12; 3] 
  [3; 0; 3; 3; -4; 9; 9; 3; 12; 289].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* preservation *)
      intros i H.
      do 10 (destruct i; [
        simpl in *;
        try (exfalso; apply H; reflexivity);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [3; 3; 9; 289] [9; 3; 289; 3] *)
        apply Permutation_sym.
        apply perm_trans with (3 :: 9 :: 289 :: 3 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (9 :: 3 :: 289 :: []).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_nil; try apply HdRel_cons; try lia]).
        apply Sorted_nil.
Qed.