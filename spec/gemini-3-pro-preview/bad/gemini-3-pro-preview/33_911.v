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
  [5; 2; -199; 7; 9; 3; -7; 11; 8; -6; 0; 1; 6; -2; 19] 
  [-7; 2; -199; -6; 9; 3; 5; 11; 8; 6; 0; 1; 7; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 15 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* permutation *)
        simpl.
        apply Permutation_sym.
        apply Permutation_trans with (l' := 5 :: -7 :: 7 :: -6 :: 6 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -7 :: 5 :: 7 :: -6 :: 6 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_trans with (l' := 5 :: -6 :: 7 :: 6 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -6 :: 5 :: 7 :: 6 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * (* sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | constructor; try (unfold Z.le; compute; discriminate) ]).
        apply Sorted_nil.
Qed.