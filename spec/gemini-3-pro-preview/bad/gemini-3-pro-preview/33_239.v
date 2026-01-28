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
  [1; 2; 3; 5; 1; -1; -8; 9; -12; 7; -7; 0; 6; 6; 1; 16; -8] 
  [-8; 2; 3; 1; 1; -1; 5; 9; -12; 6; -7; 0; 7; 6; 1; 16; -8].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 17 (destruct i; [
        simpl; try reflexivity;
        try (exfalso; apply H; reflexivity)
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-8; 1; 5; 6; 7; 16] [1; 5; -8; 7; 6; 16] *)
        apply Permutation_trans with (l' := [1; 5; -8; 6; 7; 16]).
        { apply Permutation_skip. apply Permutation_skip. apply Permutation_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [1; -8; 5; 6; 7; 16]).
        { apply Permutation_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ constructor; unfold Z.le; simpl; intro Hc; discriminate Hc | ]).
        apply Sorted_nil.
Qed.