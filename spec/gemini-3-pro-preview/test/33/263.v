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
  [1; 2; 3; -3; 5; 1; 16; 16; -8; 4; 9; -12; 7; 6; -12; 16]
  [-3; 2; 3; 1; 5; 1; 4; 16; -8; 7; 9; -12; 16; 6; -12; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i; [
        simpl in H;
        try (exfalso; apply H; reflexivity);
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply perm_trans with (l' := [-3; 1; 16; 4; 7; 16]).
        { apply perm_swap. }
        apply perm_skip. apply perm_skip.
        apply perm_trans with (l' := [4; 16; 7; 16]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ |
          match goal with
          | |- HdRel _ _ [] => apply HdRel_nil
          | |- _ => apply HdRel_cons; unfold Z.le; simpl; discriminate
          end
        ]).
        apply Sorted_nil.
Qed.