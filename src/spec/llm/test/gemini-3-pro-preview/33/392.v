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
  [2; 3; -3; 1; 16; -8; 9; -12; 7; 6; -12; 16; 7]
  [1; 3; -3; 2; 16; -8; 6; -12; 7; 7; -12; 16; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. Length equality *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i.
      (* Check indices 0 to 12. For i >= 13, both are None. *)
      do 13 (destruct i; [
        simpl; intro H_idx;
        try contradiction; (* For indices divisible by 3, premise is False *)
        reflexivity        (* For others, values match *)
        | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Goal: Permutation [1; 2; 6; 7; 9] [2; 1; 9; 6; 7] *)
        simpl.
        apply perm_trans with (l' := [2; 1; 6; 7; 9]).
        { apply perm_swap. }
        apply perm_skip. apply perm_skip.
        apply perm_trans with (l' := [6; 9; 7]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || 
               (apply HdRel_cons; unfold Z.le; simpl; discriminate)).
Qed.